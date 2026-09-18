(* validator.ml — W0-T1, per D-0005.
 *
 * WHAT THIS IS, AND WHAT IT IS NOT.
 *
 * This validator covers THREE catalog entries: cata/table.tex,
 * cata/atleastnvalues.tex and cata/atmostnvalues.tex. It is NOT a whole-catalog
 * gate and must not be described as one. `make check` is the reproducibility
 * gate; this is a soundness+minimality check over a hand-picked scope.
 *
 * The rule under test is PARSED FROM THE SHIPPED .tex, so the artifact under
 * test is the one that ships. The ground semantics (what the decomposition
 * means) is HAND-ENCODED here, read off 'explenation generator.ml' lines
 * 410-417 and 429-431, because the generator's index modifications are opaque
 * closures (W1-T7) and cannot be printed, compared or inverted. docs/VALIDATOR.md
 * states exactly what that costs in trust.
 *
 * SEMANTICS. A rule "P1,...,Pk / C" is sound iff for every domain store S that
 * satisfies every Pj, every solution of the decomposition inside S satisfies C.
 * Premise/conclusion literals are read the usual way: X_i = t means "every
 * solution has X_i = t" (as a store fact: D(X_i) subset {t}); X_i != t means
 * t is not in D(X_i); N >= p means lb(N) >= p; N < p means ub(N) < p.
 *
 * THE SINGLETON REDUCTION. Every premise literal above is anti-monotone in the
 * store (shrinking the store preserves it), universal and existential
 * quantification preserve anti-monotonicity, and "all solutions in S satisfy C"
 * is anti-monotone too. So if some store S satisfies the premises and contains a
 * solution sigma violating C, the singleton store {sigma} also satisfies the
 * premises and still violates C. Hence:
 *
 *     sound  <=>  for every complete assignment sigma satisfying the ground
 *                 constraint, premises(sigma) implies conclusion(sigma).
 *
 * That turns an enumeration over 2^(m*n) stores into one over m^n assignments.
 * D-0005 asks for the store enumeration, so BOTH are implemented: the full
 * store sweep runs for the small sizes and the run asserts the two agree. A
 * disagreement is a bug in this file and is reported as such.
 *
 * QUANTIFIER AMBIGUITY. The shipped LaTeX does not always determine the rule:
 * repeated index composition emits prefixes like "exists i, forall i, forall t,
 * forall i" for one premise. No uniform policy recovers the intent from that.
 * So each ambiguous premise is checked under EVERY consistent reading, and a
 * rule is reported UNSOUND only when it fails under all of them — a verdict no
 * better parser could overturn. Mixed results are reported AMBIGUOUS, which is
 * itself a defect of the artifact, not a gap in this checker.
 *)

(* ==================== string helpers ==================== *)

let index_sub s sub start =
  let n = String.length s and k = String.length sub in
  let rec go i =
    if i + k > n then None
    else if String.sub s i k = sub then Some i
    else go (i + 1)
  in
  if k = 0 then Some start else go start

let split_sub sub s =
  let k = String.length sub in
  let rec go start acc =
    match index_sub s sub start with
    | None -> List.rev (String.sub s start (String.length s - start) :: acc)
    | Some i -> go (i + k) (String.sub s start (i - start) :: acc)
  in
  go 0 []

let starts_with p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

let drop_prefix p s = String.sub s (String.length p) (String.length s - String.length p)

(* strip LaTeX spacing tildes as well as ordinary whitespace *)
let tidy s =
  let s = String.trim s in
  let n = String.length s in
  let i = ref 0 and j = ref (n - 1) in
  while !i < n && (s.[!i] = '~' || s.[!i] = ' ') do incr i done;
  while !j >= !i && (s.[!j] = '~' || s.[!j] = ' ') do decr j done;
  String.trim (String.sub s !i (!j - !i + 1))

let read_braced s i =
  (* s.[i] must be '{'; returns (contents, index just past the matching '}') *)
  let n = String.length s in
  let b = Buffer.create 64 in
  let rec go j depth =
    if j >= n then failwith "unbalanced braces in .tex"
    else
      match s.[j] with
      | '{' -> if depth = 0 then go (j + 1) 1 else (Buffer.add_char b '{'; go (j + 1) (depth + 1))
      | '}' -> if depth = 1 then (Buffer.contents b, j + 1)
               else (Buffer.add_char b '}'; go (j + 1) (depth - 1))
      | c -> Buffer.add_char b c; go (j + 1) depth
  in
  go i 0

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

(* ==================== rule IR ==================== *)

type dom = Dn | Dm | Dk of int
type quant = QA | QE
type atom =
  | XEq of string * string   (* X_{iv} = tv   *)
  | XNeq of string * string  (* X_{iv} != tv  *)
  | NGeq of string           (* N >= pv       *)
  | NLt of string            (* N < pv        *)
type modif = Q of quant * string | Diseq of string * string | In of string * dom
type lit = { at : atom; ms : modif list; raw : string }
type rul = { prems : lit list; concl : atom; rawp : string; rawc : string }

let atom_vars = function
  | XEq (a, b) | XNeq (a, b) -> [a; b]
  | NGeq p | NLt p -> [p]

let string_of_atom = function
  | XEq (i, t) -> Printf.sprintf "X_%s = %s" i t
  | XNeq (i, t) -> Printf.sprintf "X_%s != %s" i t
  | NGeq p -> Printf.sprintf "N >= %s" p
  | NLt p -> Printf.sprintf "N < %s" p

let string_of_quant = function QA -> "forall" | QE -> "exists"

(* ==================== parser ==================== *)

exception Unparsed of string

let parse_dom s =
  let s = tidy s in
  if s = "\\llbracket1,n\\rrbracket" then Dn
  else if s = "\\llbracket1,m\\rrbracket" then Dm
  else if starts_with "D_{" s then
    (try Dk (int_of_string (String.sub s 3 (String.length s - 4)))
     with _ -> raise (Unparsed ("index set: " ^ s)))
  else raise (Unparsed ("index set: " ^ s))

let parse_atom s =
  let s = tidy s in
  if starts_with "X_{" s then begin
    let (iv, j) = read_braced s 2 in
    let rest = tidy (String.sub s j (String.length s - j)) in
    if starts_with "=" rest then XEq (iv, tidy (drop_prefix "=" rest))
    else if starts_with "\\neq" rest then XNeq (iv, tidy (drop_prefix "\\neq" rest))
    else raise (Unparsed ("X-atom operator in: " ^ s))
  end
  else if starts_with "N" s then begin
    let rest = tidy (drop_prefix "N" s) in
    if starts_with "\\geq" rest then NGeq (tidy (drop_prefix "\\geq" rest))
    else if starts_with "<" rest then NLt (tidy (drop_prefix "<" rest))
    else raise (Unparsed ("N-atom operator in: " ^ s))
  end
  else raise (Unparsed ("atom (only X and N are in scope): " ^ s))

let parse_modif s =
  let s = tidy s in
  if starts_with "\\forall" s then Q (QA, tidy (drop_prefix "\\forall" s))
  else if starts_with "\\exists" s then Q (QE, tidy (drop_prefix "\\exists" s))
  else
    match index_sub s "\\in" 0 with
    | Some i ->
      In (tidy (String.sub s 0 i), parse_dom (String.sub s (i + 3) (String.length s - i - 3)))
    | None ->
      (match index_sub s "\\neq" 0 with
       | Some i ->
         Diseq (tidy (String.sub s 0 i),
                tidy (String.sub s (i + 4) (String.length s - i - 4)))
       | None -> raise (Unparsed ("index modification: " ^ s)))

let parse_lit s =
  let parts = List.map tidy (split_sub ",~" s) in
  match parts with
  | [] -> raise (Unparsed "empty premise group")
  | a :: ms -> { at = parse_atom a; ms = List.map parse_modif (List.filter (fun x -> x <> "") ms); raw = tidy s }

let parse_rules text =
  let rec go start acc =
    match index_sub text "\\frac" start with
    | None -> List.rev acc
    | Some i ->
      let (p, j) = read_braced text (i + 5) in
      let (c, k) = read_braced text j in
      let groups = List.filter (fun g -> tidy g <> "") (split_sub "~~~~" p) in
      go k ({ prems = List.map parse_lit groups; concl = parse_atom c;
              rawp = tidy p; rawc = tidy c } :: acc)
  in
  go 0 []

(* ==================== index-variable ranges ==================== *)

type sizes = { n : int; m : int; rows : int }

let default_dom v =
  if String.length v = 0 then Dn
  else match v.[0] with 't' -> Dm | 'p' -> Dn | 'r' -> Dk 4 | _ -> Dn

(* declared ranges, collected over the whole rule *)
let dom_table r =
  let tbl = Hashtbl.create 16 in
  List.iter (fun l -> List.iter (function In (v, d) -> if not (Hashtbl.mem tbl v) then Hashtbl.add tbl v d
                                          | _ -> ()) l.ms) r.prems;
  tbl

let range tbl sz v =
  let d = match Hashtbl.find_opt tbl v with Some d -> d | None -> default_dom v in
  match d with Dn -> sz.n | Dm -> sz.m | Dk _ -> sz.rows

(* ==================== readings ==================== *)

(* A reading of a premise literal: an ordered list of (var, quant) binders.
   Vars free in the conclusion are normally NOT re-bound (the rule schema
   already quantifies them); the alternative — treating the premise's copy as a
   fresh bound variable — is enumerated as a separate reading, so that an
   "unsound under all readings" verdict really does cover both. *)

let rec perms = function
  | [] -> [[]]
  | l -> List.concat_map (fun x -> List.map (fun p -> x :: p) (perms (List.filter (fun y -> y <> x) l))) l

let rec choices = function
  | [] -> [[]]
  | opts :: tl -> List.concat_map (fun o -> List.map (fun r -> o :: r) (choices tl)) opts

let uniq l = List.rev (List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) [] l)

let lit_readings concl_free l =
  let qvars = uniq (List.filter_map (function Q (_, v) -> Some v | _ -> None) l.ms) in
  let kinds v = uniq (List.filter_map (function Q (q, w) when w = v -> Some q | _ -> None) l.ms) in
  (* vars used by the atom but neither bound nor free in the conclusion *)
  let orphans = List.filter (fun v -> not (List.mem v concl_free) && not (List.mem v qvars))
                  (uniq (atom_vars l.at)) in
  let shared = List.filter (fun v -> List.mem v concl_free) qvars in
  let genuinely_bound = List.filter (fun v -> not (List.mem v concl_free)) qvars in
  (* each shared var: either reuse the conclusion's copy, or bind a fresh one *)
  let shared_opts = List.map (fun v -> [ (v, None) ] @ List.map (fun q -> (v, Some q)) (kinds v)) shared in
  List.concat_map
    (fun sh ->
       let extra = List.filter_map (fun (v, o) -> match o with Some q -> Some (v, q) | None -> None) sh in
       let bindable = genuinely_bound @ List.map fst extra in
       if List.length bindable > 4 then []
       else
         List.concat_map
           (fun order ->
              let kopts = List.map (fun v ->
                  match List.assoc_opt v extra with
                  | Some q -> [ q ]
                  | None -> kinds v) order in
              List.map (fun ks ->
                  List.map2 (fun v k -> (v, k)) order ks
                  @ List.map (fun v -> (v, QE)) orphans)
                (choices kopts))
           (perms bindable))
    (choices shared_opts)
  |> uniq
  |> (fun l -> if l = [] then [ [] ] else l)

(* ==================== evaluation ==================== *)

type env = (string * int) list

let vlook (e : env) v = match List.assoc_opt v e with Some x -> x | None -> raise Not_found

let diseq_ok l (e : env) v x =
  List.for_all
    (function
      | Diseq (a, b) when a = v -> (match List.assoc_opt b e with Some y -> x <> y | None -> true)
      | Diseq (a, b) when b = v -> (match List.assoc_opt a e with Some y -> x <> y | None -> true)
      | _ -> true)
    l.ms

(* guard: diseqs whose both sides are already bound before any binder runs *)
let guards_hold l (e : env) =
  List.for_all
    (function
      | Diseq (a, b) ->
        (match (List.assoc_opt a e, List.assoc_opt b e) with
         | (Some x, Some y) -> x <> y
         | _ -> true)
      | _ -> true)
    l.ms

let eval_lit eval_atom tbl sz l binders (e0 : env) =
  if not (guards_hold l e0) then false
  else
    let rec go binders e =
      match binders with
      | [] -> eval_atom l.at e
      | (v, q) :: tl ->
        let hi = range tbl sz v in
        (* a value excluded by a `\neq` side condition is OUTSIDE the quantifier's
           range: it must be skipped, not counted as a failing universal. *)
        let rec sweep x acc =
          if x > hi then acc
          else if not (diseq_ok l e v x) then sweep (x + 1) acc
          else
            let r = go tl ((v, x) :: List.remove_assoc v e) in
            (match q with
             | QA -> if not r then false else sweep (x + 1) acc
             | QE -> if r then true else sweep (x + 1) acc)
        in
        (match q with QA -> sweep 1 true | QE -> sweep 1 false)
    in
    go binders e0

(* ==================== ground constraints ==================== *)

(* Hand-encoded from 'explenation generator.ml':
   atleastnvalues (l.410-413) B1[i,t] <-> X_i=t ; B2[t] <-> OR_i B1[i,t] ;
                              B4[p] <-> N>=p ; rule6: SUM_t B2[t] >= N
       i.e. the number of distinct values taken by X is at least N.
   atmostnvalues  (l.414-417) same, rule5 with the reified event negated
       i.e. the number of distinct values taken by X is at most N.
   table          (l.429-431) B1[i,t,r] <-> X_i=t ; rule3: B2[r] <-> AND_i B1[i,t,r]
                              ("row r matches") ; rule4: OR_r B2[r].
       i.e. the tuple X is one of the rows. *)

type ground = AtLeast | AtMost | Table of int array array

let ndistinct xs =
  let seen = ref 0 in
  Array.iter (fun v -> seen := !seen lor (1 lsl (v - 1))) xs;
  let c = ref 0 and s = ref !seen in
  while !s <> 0 do c := !c + (!s land 1); s := !s lsr 1 done;
  !c

let sat_ground g xs nv =
  match g with
  | AtLeast -> ndistinct xs >= nv
  | AtMost -> ndistinct xs <= nv
  | Table rw -> Array.exists (fun r -> r = xs) rw

(* ==================== the singleton-store check ==================== *)

let eval_on_asg xs nv at (e : env) =
  match at with
  | XEq (i, t) -> xs.(vlook e i - 1) = vlook e t
  | XNeq (i, t) -> xs.(vlook e i - 1) <> vlook e t
  | NGeq p -> nv >= vlook e p
  | NLt p -> nv < vlook e p

let iter_asgs sz g f =
  let xs = Array.make sz.n 1 in
  let rec go i =
    if i = sz.n then
      for nv = 0 to sz.n do
        if sat_ground g xs nv then f (Array.copy xs) nv
      done
    else
      for v = 1 to sz.m do xs.(i) <- v; go (i + 1) done
  in
  go 0

let iter_concl_envs tbl sz concl f =
  let vars = uniq (atom_vars concl) in
  let rec go vs (e : env) =
    match vs with
    | [] -> f e
    | v :: tl -> for x = 1 to range tbl sz v do go tl ((v, x) :: e) done
  in
  go vars []

exception Counterexample of string

(* sound under this reading, for these sizes and this ground constraint?
   `fired` is set whenever some (instantiation, solution) actually satisfies all
   the premises. A rule whose premises never hold is vacuously sound and can
   never fire — reporting that as SOUND would be an overclaim, so it is tracked
   separately and reported as VACUOUS. *)
let sound_singleton ?(fired = ref false) tbl sz g r reading drop =
  let prems = List.filteri (fun i _ -> i <> drop) r.prems in
  let reading = List.filteri (fun i _ -> i <> drop) reading in
  try
    iter_concl_envs tbl sz r.concl (fun e ->
        iter_asgs sz g (fun xs nv ->
            let ev at en = eval_on_asg xs nv at en in
            let all_prem =
              List.for_all2 (fun l b -> eval_lit ev tbl sz l b e) prems reading in
            if all_prem then fired := true;
            if all_prem && not (ev r.concl e) then
              raise (Counterexample
                       (Printf.sprintf "n=%d m=%d %s X=(%s) N=%d [%s]"
                          sz.n sz.m
                          (String.concat "," (List.map (fun (v, x) -> Printf.sprintf "%s=%d" v x) e))
                          (String.concat "," (Array.to_list (Array.map string_of_int xs)))
                          nv
                          (match g with AtLeast -> "atleast" | AtMost -> "atmost"
                                      | Table rw -> "table{" ^ String.concat ";"
                                          (Array.to_list (Array.map (fun r ->
                                               String.concat "" (Array.to_list (Array.map string_of_int r))) rw)) ^ "}")))));
    None
  with Counterexample s -> Some s

(* ==================== the full store sweep (D-0005 as literally written) ==================== *)

type store = { dxs : int array; nlo : int; nhi : int }

let eval_on_store sz st at (e : env) =
  match at with
  | XEq (i, t) ->
    let full = (1 lsl sz.m) - 1 in
    st.dxs.(vlook e i - 1) land (full lxor (1 lsl (vlook e t - 1))) = 0
  | XNeq (i, t) -> st.dxs.(vlook e i - 1) land (1 lsl (vlook e t - 1)) = 0
  | NGeq p -> st.nlo >= vlook e p
  | NLt p -> st.nhi < vlook e p

let store_entails sz g st concl (e : env) =
  let xs = Array.make sz.n 1 in
  let ok = ref true in
  let rec go i =
    if not !ok then ()
    else if i = sz.n then
      for nv = st.nlo to st.nhi do
        if sat_ground g xs nv && not (eval_on_asg xs nv concl e) then ok := false
      done
    else
      for v = 1 to sz.m do
        if st.dxs.(i) land (1 lsl (v - 1)) <> 0 then begin xs.(i) <- v; go (i + 1) end
      done
  in
  go 0; !ok

let sound_stores tbl sz g r reading drop =
  let prems = List.filteri (fun i _ -> i <> drop) r.prems in
  let reading = List.filteri (fun i _ -> i <> drop) reading in
  let full = (1 lsl sz.m) - 1 in
  let dxs = Array.make sz.n 0 in
  let bad = ref false in
  let rec go i =
    if !bad then ()
    else if i = sz.n then
      for lo = 0 to sz.n do
        for hi = lo to sz.n do
          let st = { dxs = Array.copy dxs; nlo = lo; nhi = hi } in
          iter_concl_envs tbl sz r.concl (fun e ->
              let ev at en = eval_on_store sz st at en in
              if List.for_all2 (fun l b -> eval_lit ev tbl sz l b e) prems reading
              && not (store_entails sz g st r.concl e) then bad := true)
        done
      done
    else
      for d = 0 to full do dxs.(i) <- d; go (i + 1) done
  in
  go 0; not !bad

(* ==================== driving ==================== *)

let tables_for sz =
  (* every table with 1 or 2 distinct rows over [1,m]^n *)
  let all = ref [] in
  let row = Array.make sz.n 1 in
  let rec go i = if i = sz.n then all := Array.copy row :: !all
    else for v = 1 to sz.m do row.(i) <- v; go (i + 1) done in
  go 0;
  let all = Array.of_list (List.rev !all) in
  let out = ref [] in
  Array.iter (fun r -> out := [| r |] :: !out) all;
  Array.iteri (fun i a -> Array.iteri (fun j b -> if j > i then out := [| a; b |] :: !out) all) all;
  List.rev !out

type scope = { entry : string; grounds : (sizes * ground) list; xcheck : (sizes * ground) list }

let mk_scope entry which =
  match which with
  | `NV g ->
    let sizes = List.concat_map (fun n -> List.map (fun m -> { n; m; rows = 0 }) [2; 3; 4]) [2; 3; 4] in
    { entry;
      grounds = List.map (fun s -> (s, g)) sizes;
      xcheck = List.filter_map (fun s -> if s.n <= 3 && s.m <= 3 then Some (s, g) else None) sizes }
  | `Table ->
    let sizes = List.concat_map (fun n -> List.map (fun m -> { n; m; rows = 0 }) [2; 3]) [2; 3] in
    let gs = List.concat_map (fun s ->
        List.map (fun t -> ({ s with rows = Array.length t }, Table t)) (tables_for s)) sizes in
    { entry; grounds = gs; xcheck = List.filter (fun (s, _) -> s.n <= 2 && s.m <= 2) gs }

(* returns (counterexample option, did the premises ever hold?) *)
let sound_everywhere sc tbl r reading drop =
  let fired = ref false in
  let rec go = function
    | [] -> None
    | (sz, g) :: tl ->
      (match sound_singleton ~fired tbl sz g r reading drop with
       | Some ce -> Some ce
       | None -> go tl)
  in
  let ce = go sc.grounds in
  (ce, !fired)

let cross_check sc tbl r reading =
  (* the store sweep and the singleton reduction must agree *)
  List.for_all
    (fun (sz, g) ->
       let a = sound_stores tbl sz g r reading (-1) in
       let b = (sound_singleton tbl sz g r reading (-1) = None) in
       a = b)
    sc.xcheck


(* ==================== verdicts ==================== *)

type verdict =
  | Unsound of string          (* fails under every reading; counterexample *)
  | Ambiguous of string        (* sound under some readings, unsound under others *)
  | OnlyFiringUnsound of string (* every sound reading is vacuous; the one reading
                                  whose premises can ever hold is unsound *)
  | Vacuous                    (* sound, but no store in scope satisfies the premises *)
  | NotMinimal of int list     (* sound, but these premises (0-based) are droppable *)
  | Minimal                    (* sound, minimal, and it can actually fire *)
  | TooAmbiguous of int        (* more candidate readings than we are willing to check *)

let verdict_name = function
  | Unsound _ -> "UNSOUND"
  | Ambiguous _ -> "AMBIGUOUS"
  | OnlyFiringUnsound _ -> "UNSOUND(firing)"
  | Vacuous -> "VACUOUS"
  | NotMinimal _ -> "NOT MINIMAL"
  | Minimal -> "SOUND and MINIMAL"
  | TooAmbiguous _ -> "UNCHECKED"

let is_flag = function Minimal -> false | _ -> true

(* classify one rule; also returns the per-reading results and whether the
   validator's own store-sweep cross-check agreed *)
let classify sc r =
  let tbl = dom_table r in
  let concl_free = uniq (atom_vars r.concl) in
  let readings = choices (List.map (lit_readings concl_free) r.prems) in
  let nread = List.length readings in
  if nread > 256 then (TooAmbiguous nread, [], true)
  else begin
    let results = List.map (fun rd -> (rd, sound_everywhere sc tbl r rd (-1))) readings in
    let agreed = List.for_all (fun (rd, _) -> cross_check sc tbl r rd) results in
    let good = List.filter (fun (_, (ce, _)) -> ce = None) results in
    let bad = List.filter (fun (_, (ce, _)) -> ce <> None) results in
    let first_ce () = match bad with (_, (Some ce, _)) :: _ -> ce | _ -> "?" in
    let v =
      if good = [] then Unsound (first_ce ())
      else if bad <> [] then
        (* If every reading that survives is one whose premises can never hold,
           then the only reading under which this rule could ever fire is an
           unsound one. That is not an ambiguity to be resolved later; the rule
           is broken whichever way the quantifiers were meant. *)
        (if List.for_all (fun (_, (_, fired)) -> not fired) good
         then OnlyFiringUnsound (first_ce ())
         else Ambiguous (first_ce ()))
      else if List.for_all (fun (_, (_, fired)) -> not fired) good then Vacuous
      else begin
        let np = List.length r.prems in
        let drop = ref [] in
        for d = np - 1 downto 0 do
          if List.for_all (fun (rd, _) -> fst (sound_everywhere sc tbl r rd d) = None) good then
            drop := d :: !drop
        done;
        if !drop = [] then Minimal else NotMinimal !drop
      end
    in
    (v, results, agreed)
  end

(* ==================== self-test: positive and negative controls ==================== *)

(* A checker that flags everything proves nothing. These control rules are
   hand-written in the same LaTeX dialect the catalog uses, and the run asserts
   that each lands in the verdict it is supposed to. If a control regresses,
   the catalog verdicts above are not to be believed. *)
let controls =
  [ (* domain of X_i reduced to {t} really does entail X_i = t, and the premise
       cannot be dropped: a genuine sound+minimal rule *)
    ("sound+minimal",
     "$$\\frac{X_{i} \\neq t',~\\forall t',~t' \\neq t,~t' \\in \\llbracket1,m\\rrbracket}{X_{i}=t}$$",
     Minimal);
    (* the same rule with a redundant bound on N bolted on *)
    ("sound, redundant premise",
     "$$\\frac{X_{i} \\neq t',~\\forall t',~t' \\neq t,~t' \\in \\llbracket1,m\\rrbracket~~~~N \\geq p,~\\forall p,~p \\in \\llbracket1,n\\rrbracket}{X_{i}=t}$$",
     NotMinimal [1]);
    (* flatly contradictory *)
    ("unsound",
     "$$\\frac{X_{i}=t,~i \\in \\llbracket1,n\\rrbracket,~t \\in \\llbracket1,m\\rrbracket}{X_{i} \\neq t}$$",
     Unsound "");
    (* premises that no store can satisfy *)
    ("vacuous",
     "$$\\frac{X_{i} \\neq t,~\\forall i,~i \\in \\llbracket1,n\\rrbracket,~\\forall t,~t \\in \\llbracket1,m\\rrbracket}{N<p}$$",
     Vacuous) ]

let same_kind a b =
  match (a, b) with
  | (Unsound _, Unsound _) | (Ambiguous _, Ambiguous _) -> true
  | (OnlyFiringUnsound _, OnlyFiringUnsound _) -> true
  | (NotMinimal x, NotMinimal y) -> x = y
  | (Vacuous, Vacuous) | (Minimal, Minimal) -> true
  | _ -> false

let run_selftest () =
  print_endline "== self-test: controls (a checker that flags everything proves nothing) ==";
  let sc = mk_scope "<control>" (`NV AtMost) in
  let bad = ref 0 in
  List.iter
    (fun (name, tex, want) ->
       let r = List.hd (parse_rules tex) in
       let (v, _, agreed) = classify sc r in
       let ok = same_kind v want && agreed in
       if not ok then incr bad;
       Printf.printf "  %-26s expected %-18s got %-18s %s\n" name
         (verdict_name want) (verdict_name v)
         (if ok then "ok" else "MISMATCH"))
    controls;
  if !bad = 0 then print_endline "  -- all controls behaved; the verdicts below are worth reading"
  else Printf.printf "  -- %d CONTROL(S) FAILED: do not believe the verdicts below\n" !bad;
  print_newline ();
  !bad

(* ==================== main ==================== *)

let () =
  let root = ref "." and only_self = ref false in
  Array.iteri (fun i a ->
      if i > 0 then
        if a = "--selftest" then only_self := true else root := a)
    Sys.argv;
  print_endline "== W0-T1 validator ==";
  print_endline "Scope: 3 of 16 catalog entries (table, atleastnvalues, atmostnvalues).";
  print_endline "Rules are PARSED from the shipped .tex; the ground semantics of each";
  print_endline "decomposition is HAND-ENCODED from the generator source. docs/VALIDATOR.md";
  print_endline "says exactly what that costs in trust. This is not a whole-catalog gate.";
  print_newline ();
  let ctl = run_selftest () in
  if !only_self then exit (if ctl = 0 then 0 else 1);
  let entries =
    [ ("cata/table.tex", `Table);
      ("cata/atleastnvalues.tex", `NV AtLeast);
      ("cata/atmostnvalues.tex", `NV AtMost) ] in
  let flagged = ref 0 and checked = ref 0 and xbad = ref 0 in
  List.iter
    (fun (path, which) ->
       let sc = mk_scope path which in
       let rules = parse_rules (read_file (Filename.concat !root path)) in
       Printf.printf "---- %s  (%d rules) ----\n" path (List.length rules);
       List.iteri
         (fun ri r ->
            incr checked;
            let (v, results, agreed) = classify sc r in
            if is_flag v then incr flagged;
            if not agreed then incr xbad;
            Printf.printf "\n  rule %d/%d   %s  <=  %s\n" (ri + 1) (List.length rules)
              (string_of_atom r.concl)
              (if r.prems = [] then "(no premise)"
               else String.concat " AND " (List.map (fun l -> string_of_atom l.at) r.prems));
            Printf.printf "    readings  : %d (%d sound, %d unsound)\n"
              (List.length results)
              (List.length (List.filter (fun (_, (ce, _)) -> ce = None) results))
              (List.length (List.filter (fun (_, (ce, _)) -> ce <> None) results));
            List.iteri (fun k (rd, (ce, fired)) ->
                if k < 4 then
                  Printf.printf "      [%s]%s %s\n"
                    (if ce = None then "sound  " else "UNSOUND")
                    (if ce = None && not fired then " (premises never hold)" else "")
                    (String.concat " ; "
                       (List.map (fun b ->
                            if b = [] then "(no binder)"
                            else String.concat "," (List.map (fun (v, q) -> string_of_quant q ^ " " ^ v) b))
                          rd)))
              results;
            Printf.printf "    cross-check: %s\n"
              (if agreed then "store sweep agrees with singleton reduction"
               else "!! STORE SWEEP DISAGREES — BUG IN validator.ml");
            (match v with
             | Minimal -> Printf.printf "    VERDICT   : SOUND and MINIMAL\n"
             | Vacuous ->
               Printf.printf "    VERDICT   : VACUOUS — no store in scope satisfies the premises,\n";
               Printf.printf "                so it is sound only because it can never fire\n"
             | NotMinimal ds ->
               Printf.printf "    VERDICT   : SOUND but NOT MINIMAL — droppable: %s\n"
                 (String.concat ", "
                    (List.map (fun d -> Printf.sprintf "#%d (%s)" (d + 1)
                                 (string_of_atom (List.nth r.prems d).at)) ds))
             | Unsound ce ->
               Printf.printf "    VERDICT   : UNSOUND under every reading\n";
               Printf.printf "    counterexample: %s\n" ce
             | Ambiguous ce ->
               Printf.printf "    VERDICT   : AMBIGUOUS — the .tex does not determine the rule\n";
               Printf.printf "    counterexample (unsound reading): %s\n" ce
             | OnlyFiringUnsound ce ->
               Printf.printf "    VERDICT   : UNSOUND — every other reading is vacuous, so the\n";
               Printf.printf "                only reading that can ever fire is the unsound one\n";
               Printf.printf "    counterexample: %s\n" ce
             | TooAmbiguous k ->
               Printf.printf "    VERDICT   : UNCHECKED — %d candidate readings\n" k))
         rules;
       print_newline ())
    entries;
  Printf.printf "== %d rules checked in 3 entries, %d flagged ==\n" !checked !flagged;
  if !xbad > 0 then
    Printf.printf "== %d cross-check disagreements: FIX validator.ml BEFORE BELIEVING THIS ==\n" !xbad;
  print_endline "The other 13 catalog entries are out of scope: generated, unvalidated.";
  exit (if ctl > 0 || !xbad > 0 then 2 else if !flagged > 0 then 1 else 0)
