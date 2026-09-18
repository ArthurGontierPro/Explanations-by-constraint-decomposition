(* validator.ml — W0-T1, extended to the whole catalog by W1-T8, per D-0005.
 *
 * WHAT THIS IS, AND WHAT IT IS NOT.
 *
 * This validator covers ELEVEN of the sixteen catalog entries. The other five
 * are reported OUT OF SCOPE with a machine-checked reason, not silently
 * skipped: `regular`, `roots`, `range` and `among` reference index sets D_4-D_9
 * that the printer never defines (W1-T2), and `cumulative` carries durations
 * d_i as uninterpreted symbols and never mentions the resource capacity at all.
 * Inventing a reading for those would be inventing the result.
 *
 * `make check` is a different thing: it proves the generator still reproduces
 * the committed .tex byte-for-byte, a reproducibility claim that says nothing
 * about whether a rule is true.
 *
 * The rule under test is PARSED FROM THE SHIPPED .tex, so the artifact under
 * test is the one that ships. The ground semantics (what the decomposition
 * means) is HAND-ENCODED here, read off 'explenation generator.ml' lines
 * 383-434, because when W1-T8 began the generator's index modifications were
 * opaque closures that could not be printed, compared or inverted. W1-T7 landed
 * while this was running (463534f) and they are data now, so a later session can
 * derive what is typed here; W1-T8 deliberately measured the committed artifact
 * instead. docs/VALIDATOR.md states exactly what that costs in trust.
 *
 * TWO DEFENCES ON THE HAND-ENCODING (W1-T8, M-1's proposal). Before any rule is
 * judged, the run checks the encodings themselves:
 *   (a) CLOSURE PROPERTIES from the Global Constraint Catalog's `Arg. properties`
 *       field — contractible / extensible / monotone / functional dependency.
 *       These are invariants on the semantics, not on the rules, which is
 *       precisely where the exposure is.
 *   (b) IMPLICATIONS between entries that live wholly inside cata/, listed in
 *       docs/GCCAT.md section 3: all_equal => increasing, all_equal => decreasing,
 *       nvalue => atleast_nvalue, nvalue => atmost_nvalue, alldifferent <=>
 *       nvalue with NVAL = n, alldifferent => every gcc count <= 1.
 * A failure in either means a transcription is wrong and the verdicts below are
 * worthless; the run says so and exits 2.
 *
 * SEMANTICS. A rule "P1,...,Pk / C" is sound iff for every domain store S that
 * satisfies every Pj, every solution of the decomposition inside S satisfies C.
 * Premise/conclusion literals are read the usual way: X_i = t means "every
 * solution has X_i = t" (as a store fact: D(X_i) subset {t}); X_i != t means t
 * is not in D(X_i); X_i >= t means every value in D(X_i) is >= t; X_i < t
 * likewise; N >= p means lb(N) >= p; N < p means ub(N) < p; N = p means
 * D(N) = {p}; N != p means p is not in D(N). O_t, I and V read the same way.
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
 * That turns an enumeration over stores into one over assignments. D-0005 asks
 * for the store enumeration, so BOTH are implemented: the full store sweep runs
 * for the small sizes and the run asserts the two agree. A disagreement is a bug
 * in this file and is reported as such.
 *
 * QUANTIFIER AMBIGUITY. The shipped LaTeX does not always determine the rule:
 * repeated index composition emits prefixes like "exists i, forall i, forall t,
 * forall i" for one premise. No uniform policy recovers the intent from that.
 * So each ambiguous premise is checked under EVERY consistent reading, and a
 * rule is reported UNSOUND only when it fails under all of them — a verdict no
 * better parser could overturn. Mixed results are reported AMBIGUOUS, which is
 * itself a defect of the artifact, not a gap in this checker.
 *
 * OFF-THE-END INDICES. `increasing` and `decreasing` carry index equations
 * (i'=i-1). At i=1 the premise names X_0, which does not exist. This file reads
 * a premise about a non-existent variable as FALSE (the rule instance cannot
 * fire), which is an interpretation, like reading table's D_4 as the row set.
 * It is stated in docs/VALIDATOR.md and it is the only reading under which such
 * a rule is not trivially unsound at the boundary.
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

let rec range_list a b = if a > b then [] else a :: range_list (a + 1) b

let is_ident s =
  String.length s > 0
  && (let ok = ref true in
      String.iter (fun c ->
          if not ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                  || (c >= '0' && c <= '9') || c = '\'')
          then ok := false) s;
      !ok)

(* ==================== rule IR ==================== *)

type dom = Dn | Dm | Dk of int
type quant = QA | QE
type cmp = Ceq | Cneq | Cgeq | Clt
type atom =
  | AX of cmp * string * string   (* X_{iv} cmp tv *)
  | AN of cmp * string            (* N cmp pv       *)
  | AO of cmp * string * string   (* O_{tv} cmp pv  *)
  | AI of cmp * string            (* I cmp iv       *)
  | AV of cmp * string            (* V cmp tv       *)
type modif =
  | Q of quant * string
  | Diseq of string * string
  | In of string * dom
  | Eqn of string * string * int  (* v = base + offset *)
type lit = { at : atom; ms : modif list; raw : string }
type rul = { prems : lit list; concl : atom; rawp : string; rawc : string }

let atom_vars = function
  | AX (_, a, b) | AO (_, a, b) -> [a; b]
  | AN (_, p) -> [p]
  | AI (_, i) -> [i]
  | AV (_, t) -> [t]

let string_of_cmp = function Ceq -> "=" | Cneq -> "!=" | Cgeq -> ">=" | Clt -> "<"

let string_of_atom = function
  | AX (c, i, t) -> Printf.sprintf "X_%s %s %s" i (string_of_cmp c) t
  | AN (c, p) -> Printf.sprintf "N %s %s" (string_of_cmp c) p
  | AO (c, t, p) -> Printf.sprintf "O_%s %s %s" t (string_of_cmp c) p
  | AI (c, i) -> Printf.sprintf "I %s %s" (string_of_cmp c) i
  | AV (c, t) -> Printf.sprintf "V %s %s" (string_of_cmp c) t

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

let parse_cmp_rest s =
  let s = tidy s in
  if starts_with "\\geq" s then (Cgeq, tidy (drop_prefix "\\geq" s))
  else if starts_with "\\neq" s then (Cneq, tidy (drop_prefix "\\neq" s))
  else if starts_with "=" s then (Ceq, tidy (drop_prefix "=" s))
  else if starts_with "<" s then (Clt, tidy (drop_prefix "<" s))
  else raise (Unparsed ("comparison in: " ^ s))

let want_ident ctx v =
  if is_ident v then v else raise (Unparsed (ctx ^ ": not a plain index variable: " ^ v))

let parse_atom s =
  let s = tidy s in
  let subscripted ctx mk =
    let (sv, j) = read_braced s 2 in
    let (c, r) = parse_cmp_rest (String.sub s j (String.length s - j)) in
    mk c (want_ident ctx sv) (want_ident ctx r)
  in
  if starts_with "X_{" s then subscripted "X-atom" (fun c a b -> AX (c, a, b))
  else if starts_with "O_{" s then subscripted "O-atom" (fun c a b -> AO (c, a, b))
  else if starts_with "N" s then
    let (c, r) = parse_cmp_rest (drop_prefix "N" s) in AN (c, want_ident "N-atom" r)
  else if starts_with "I" s then
    let (c, r) = parse_cmp_rest (drop_prefix "I" s) in AI (c, want_ident "I-atom" r)
  else if starts_with "V" s then
    let (c, r) = parse_cmp_rest (drop_prefix "V" s) in AV (c, want_ident "V-atom" r)
  else raise (Unparsed ("atom (X, O, N, I and V are in scope): " ^ s))

(* an index equation: i'=i-1, i'=i+1, t'=t (and NOT t'=t-d_{i}, which names a
   parameter array this file has no semantics for — that is cumulative, and the
   Unparsed it raises is exactly why cumulative is reported out of scope). *)
let parse_eqn s i =
  let lhs = tidy (String.sub s 0 i) in
  let rhs = tidy (String.sub s (i + 1) (String.length s - i - 1)) in
  let split_at j sign =
    let b = tidy (String.sub rhs 0 j) in
    let o = tidy (String.sub rhs (j + 1) (String.length rhs - j - 1)) in
    (b, sign * (try int_of_string o with _ -> raise (Unparsed ("index equation offset: " ^ s))))
  in
  let (b, off) =
    match index_sub rhs "+" 0 with
    | Some j -> split_at j 1
    | None -> (match index_sub rhs "-" 0 with Some j -> split_at j (-1) | None -> (rhs, 0))
  in
  Eqn (want_ident "index equation" lhs, want_ident "index equation" b, off)

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
       | None ->
         (match index_sub s "=" 0 with
          | Some i -> parse_eqn s i
          | None -> raise (Unparsed ("index modification: " ^ s))))

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

(* the D_k's a rule mentions — the evidence behind an "out of scope" verdict *)
let dks_of_text text =
  let out = ref [] in
  let rec go start =
    match index_sub text "D_{" start with
    | None -> ()
    | Some i ->
      let (k, j) = read_braced text (i + 2) in
      if not (List.mem k !out) then out := !out @ [ k ];
      go j
  in
  go 0; !out

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
   "unsound under all readings" verdict really does cover both. Vars defined by
   an index equation are neither bound nor free: they are computed. *)

let rec perms = function
  | [] -> [[]]
  | l -> List.concat_map (fun x -> List.map (fun p -> x :: p) (perms (List.filter (fun y -> y <> x) l))) l

let rec choices = function
  | [] -> [[]]
  | opts :: tl -> List.concat_map (fun o -> List.map (fun r -> o :: r) (choices tl)) opts

let uniq l = List.rev (List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) [] l)

let eqn_vars l = List.filter_map (function Eqn (v, _, _) -> Some v | _ -> None) l.ms

let lit_readings concl_free l =
  let qvars = uniq (List.filter_map (function Q (_, v) -> Some v | _ -> None) l.ms) in
  let kinds v = uniq (List.filter_map (function Q (q, w) when w = v -> Some q | _ -> None) l.ms) in
  let computed = eqn_vars l in
  (* vars used by the atom but neither bound, nor computed, nor free in the conclusion *)
  let orphans = List.filter (fun v -> not (List.mem v concl_free) && not (List.mem v qvars)
                                      && not (List.mem v computed))
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

(* Resolve index equations against a fully-bound environment. `None` means the
   equation puts the index off the end of the array — X_0 or X_{n+1} — in which
   case the premise names a variable that does not exist and is read as false. *)
let resolve_eqns tbl sz l (e : env) =
  let eqs = List.filter_map (function Eqn (v, b, o) -> Some (v, b, o) | _ -> None) l.ms in
  let rec loop e pend fuel =
    if pend = [] then Some e
    else if fuel <= 0 then None
    else
      let (ready, rest) = List.partition (fun (_, b, _) -> List.mem_assoc b e) pend in
      if ready = [] then None
      else
        let bad = ref false in
        let e =
          List.fold_left
            (fun e (v, b, o) ->
               let x = List.assoc b e + o in
               if x < 1 || x > range tbl sz v then (bad := true; e)
               else (v, x) :: List.remove_assoc v e)
            e ready
        in
        if !bad then None else loop e rest (fuel - 1)
  in
  loop e eqs (List.length eqs + 1)

let eval_lit eval_atom tbl sz l binders (e0 : env) =
  if not (guards_hold l e0) then false
  else
    let rec go binders e =
      match binders with
      | [] -> (match resolve_eqns tbl sz l e with None -> false | Some e' -> eval_atom l.at e')
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

(* Hand-encoded from 'explenation generator.ml'. Each line names the generator
   lines it was read off and the gccat Purpose field that corroborates it
   (fetched 2026-09-18; docs/GCCAT.md section 1 for what that field is).
   `Sum` is the exception and is marked as such: cata/sum.tex is ORPHANED —
   no decomposition in the generator produces it — so its semantics is read off
   gccat's sum_ctr Purpose with CTR "=" and nothing else.

   AllEq     l.383-386  alleq       "all variables take the same value"
   AllDiff   l.387-388  alldiff     "all variables take distinct values"
   Gcc       l.393-396  gccn        "O_t is the number of variables taking t"
   Incr      l.397-398  incr        "the variables are increasing"
   Decr      l.399-400  decr        "the variables are decreasing"
   Elem      l.401-405  elem        "V = X[I]"
   NValue    l.406-409  nvalues     "N is the number of distinct values in X"
   AtLeast   l.410-413  atleastnvalues   "at least N distinct values"
   AtMost    l.414-417  atmostnvalues    "at most N distinct values"
   Table     l.429-431  table       "the tuple X is one of the rows"
   Sum       (orphan)                "the sum of X equals N"                *)

type ground =
  | AtLeast | AtMost | Table of int array array
  | AllDiff | AllEq | Incr | Decr | NValue | Gcc | Elem | Sum

let ground_name = function
  | AtLeast -> "atleast" | AtMost -> "atmost" | Table _ -> "table"
  | AllDiff -> "alldifferent" | AllEq -> "allequal" | Incr -> "increasing"
  | Decr -> "decreasing" | NValue -> "nvalue" | Gcc -> "gcc" | Elem -> "element"
  | Sum -> "sum"

let ndistinct xs =
  let seen = ref 0 in
  Array.iter (fun v -> seen := !seen lor (1 lsl (v - 1))) xs;
  let c = ref 0 and s = ref !seen in
  while !s <> 0 do c := !c + (!s land 1); s := !s lsr 1 done;
  !c

let occ m xs = Array.init m (fun k -> Array.fold_left (fun a v -> if v = k + 1 then a + 1 else a) 0 xs)
let sum_of xs = Array.fold_left ( + ) 0 xs

(* a complete assignment: the X vector plus whatever auxiliary variables the
   entry actually has. Entries with no N / no O / no I,V leave them at 0. *)
type asg = { xs : int array; nv : int; ov : int array; iv : int; vv : int }

let sat_ground m g a =
  let xs = a.xs in
  let n = Array.length xs in
  match g with
  | AtLeast -> ndistinct xs >= a.nv
  | AtMost -> ndistinct xs <= a.nv
  | Table rw -> Array.exists (fun r -> r = xs) rw
  | AllDiff ->
    let ok = ref true in
    for i = 0 to n - 1 do for j = i + 1 to n - 1 do if xs.(i) = xs.(j) then ok := false done done; !ok
  | AllEq -> n = 0 || Array.for_all (fun v -> v = xs.(0)) xs
  | Incr -> let ok = ref true in for i = 0 to n - 2 do if xs.(i) > xs.(i + 1) then ok := false done; !ok
  | Decr -> let ok = ref true in for i = 0 to n - 2 do if xs.(i) < xs.(i + 1) then ok := false done; !ok
  | NValue -> ndistinct xs = a.nv
  | Gcc -> a.ov = occ m xs
  | Elem -> a.iv >= 1 && a.iv <= n && xs.(a.iv - 1) = a.vv
  | Sum -> a.nv = sum_of xs

let uses_n = function AtLeast | AtMost | NValue | Sum -> true | _ -> false
let uses_o = function Gcc -> true | _ -> false
let uses_iv = function Elem -> true | _ -> false

let nv_range sz = function
  | AtLeast | AtMost | NValue -> (0, sz.n)
  | Sum -> (sz.n, sz.n * sz.m)
  | _ -> (0, 0)

(* ==================== the singleton-store check ==================== *)

let eval_on_asg sz a at (e : env) =
  let c2 c x y = match c with Ceq -> x = y | Cneq -> x <> y | Cgeq -> x >= y | Clt -> x < y in
  match at with
  | AX (c, i, t) ->
    let ii = vlook e i in
    ii >= 1 && ii <= sz.n && c2 c a.xs.(ii - 1) (vlook e t)
  | AO (c, t, p) ->
    let tt = vlook e t in
    tt >= 1 && tt <= sz.m && c2 c a.ov.(tt - 1) (vlook e p)
  | AN (c, p) -> c2 c a.nv (vlook e p)
  | AI (c, i) -> c2 c a.iv (vlook e i)
  | AV (c, t) -> c2 c a.vv (vlook e t)

(* every complete assignment satisfying the ground constraint, filtered by
   `keep` (used by the store sweep to restrict to a store) *)
let iter_sols sz g keep f =
  let xs = Array.make sz.n 1 in
  let (nlo, nhi) = nv_range sz g in
  let (ilo, ihi) = if uses_iv g then (1, sz.n) else (0, 0) in
  let (vlo, vhi) = if uses_iv g then (1, sz.m) else (0, 0) in
  let rec go i =
    if i = sz.n then begin
      let ov = if uses_o g then occ sz.m xs else Array.make sz.m 0 in
      for nv = nlo to nhi do
        for iv = ilo to ihi do
          for vv = vlo to vhi do
            let a = { xs = Array.copy xs; nv; ov; iv; vv } in
            if sat_ground sz.m g a && keep a then f a
          done
        done
      done
    end
    else for v = 1 to sz.m do xs.(i) <- v; go (i + 1) done
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

let show_asg sz g a =
  Printf.sprintf "X=(%s)%s%s%s [%s]"
    (String.concat "," (Array.to_list (Array.map string_of_int a.xs)))
    (if uses_n g then Printf.sprintf " N=%d" a.nv else "")
    (if uses_o g then " O=(" ^ String.concat "," (Array.to_list (Array.map string_of_int a.ov)) ^ ")" else "")
    (if uses_iv g then Printf.sprintf " I=%d V=%d" a.iv a.vv else "")
    (match g with
     | Table rw -> "table{" ^ String.concat ";"
                     (Array.to_list (Array.map (fun r ->
                          String.concat "" (Array.to_list (Array.map string_of_int r))) rw)) ^ "}"
     | _ -> ground_name g)
  |> fun s -> Printf.sprintf "n=%d m=%d %s" sz.n sz.m s

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
        iter_sols sz g (fun _ -> true) (fun a ->
            let ev at en = eval_on_asg sz a at en in
            let all_prem =
              List.for_all2 (fun l b -> eval_lit ev tbl sz l b e) prems reading in
            if all_prem then fired := true;
            if all_prem && not (ev r.concl e) then
              raise (Counterexample
                       (Printf.sprintf "%s %s" (show_asg sz g a)
                          (String.concat "," (List.map (fun (v, x) -> Printf.sprintf "%s=%d" v x) e))))));
    None
  with Counterexample s -> Some s

(* ==================== the full store sweep (D-0005 as literally written) ==================== *)

type store = { dxs : int array; nlo : int; nhi : int;
               olo : int array; ohi : int array; di : int; dv : int }

(* a domain, as a bitmask over [1,width], entails the literal? *)
let cmp_dom width d c v =
  let full = (1 lsl width) - 1 in
  if v < 1 || v > width then false
  else match c with
    | Ceq -> d land (full lxor (1 lsl (v - 1))) = 0
    | Cneq -> d land (1 lsl (v - 1)) = 0
    | Cgeq -> d land ((1 lsl (v - 1)) - 1) = 0            (* no value < v *)
    | Clt -> d land (full lxor ((1 lsl (v - 1)) - 1)) = 0 (* no value >= v *)

let cmp_int lo hi c v =
  match c with
  | Ceq -> lo = v && hi = v
  | Cneq -> v < lo || v > hi
  | Cgeq -> lo >= v
  | Clt -> hi < v

let eval_on_store sz st at (e : env) =
  match at with
  | AX (c, i, t) ->
    let ii = vlook e i in
    ii >= 1 && ii <= sz.n && cmp_dom sz.m st.dxs.(ii - 1) c (vlook e t)
  | AO (c, t, p) ->
    let tt = vlook e t in
    tt >= 1 && tt <= sz.m && cmp_int st.olo.(tt - 1) st.ohi.(tt - 1) c (vlook e p)
  | AN (c, p) -> cmp_int st.nlo st.nhi c (vlook e p)
  | AI (c, i) -> cmp_dom sz.n st.di c (vlook e i)
  | AV (c, t) -> cmp_dom sz.m st.dv c (vlook e t)

let in_store sz g st a =
  let ok = ref true in
  Array.iteri (fun k v -> if st.dxs.(k) land (1 lsl (v - 1)) = 0 then ok := false) a.xs;
  if uses_n g && (a.nv < st.nlo || a.nv > st.nhi) then ok := false;
  if uses_o g then Array.iteri (fun k v -> if v < st.olo.(k) || v > st.ohi.(k) then ok := false) a.ov;
  if uses_iv g then begin
    if st.di land (1 lsl (a.iv - 1)) = 0 then ok := false;
    if st.dv land (1 lsl (a.vv - 1)) = 0 then ok := false
  end;
  ignore sz; !ok

let store_entails sz g st concl (e : env) =
  let ok = ref true in
  iter_sols sz g (in_store sz g st) (fun a -> if not (eval_on_asg sz a concl e) then ok := false);
  !ok

let intervals lo hi =
  List.concat_map (fun a -> List.map (fun b -> (a, b)) (range_list a hi)) (range_list lo hi)

let rec tuples k opts =
  if k = 0 then [ [] ]
  else List.concat_map (fun x -> List.map (fun r -> x :: r) (tuples (k - 1) opts)) opts

let sound_stores tbl sz g r reading drop =
  let prems = List.filteri (fun i _ -> i <> drop) r.prems in
  let reading = List.filteri (fun i _ -> i <> drop) reading in
  let full = (1 lsl sz.m) - 1 in
  let (gnlo, gnhi) = nv_range sz g in
  let nints = if uses_n g then intervals gnlo gnhi else [ (gnlo, gnhi) ] in
  let oints = if uses_o g then tuples sz.m (intervals 0 sz.n)
    else [ List.map (fun _ -> (0, sz.n)) (range_list 1 sz.m) ] in
  let imasks = if uses_iv g then range_list 0 ((1 lsl sz.n) - 1) else [ (1 lsl sz.n) - 1 ] in
  let vmasks = if uses_iv g then range_list 0 full else [ full ] in
  let dxs = Array.make sz.n 0 in
  let bad = ref false in
  let rec go i =
    if !bad then ()
    else if i = sz.n then
      List.iter (fun (nlo, nhi) ->
          List.iter (fun oi ->
              List.iter (fun di ->
                  List.iter (fun dv ->
                      if not !bad then begin
                        let st = { dxs = Array.copy dxs; nlo; nhi;
                                   olo = Array.of_list (List.map fst oi);
                                   ohi = Array.of_list (List.map snd oi); di; dv } in
                        iter_concl_envs tbl sz r.concl (fun e ->
                            let ev at en = eval_on_store sz st at en in
                            if List.for_all2 (fun l b -> eval_lit ev tbl sz l b e) prems reading
                            && not (store_entails sz g st r.concl e) then bad := true)
                      end)
                    vmasks)
                imasks)
            oints)
        nints
    else for d = 0 to full do dxs.(i) <- d; go (i + 1) done
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
  | `Simple (g, xn, xm) ->
    let sizes = List.concat_map (fun n -> List.map (fun m -> { n; m; rows = 0 }) [2; 3; 4]) [2; 3; 4] in
    { entry;
      grounds = List.map (fun s -> (s, g)) sizes;
      xcheck = List.filter_map (fun s -> if s.n <= xn && s.m <= xm then Some (s, g) else None) sizes }

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

(* ==================== defence (a): closure properties on the ENCODING ==========
 *
 * M-1's proposal (docs/GCCAT.md section 3): the catalog's `Arg. properties` field
 * states contractible / extensible / monotone / functional-dependency invariants,
 * and those are machine-checkable against the hand-encoded semantics. They check
 * the ENCODING, not the rule, which is exactly where docs/VALIDATOR.md says the
 * exposure is. Every property below is quoted from the gccat entry page named
 * beside it (fetched 2026-09-18) except where marked `derived`.
 *)

let vecs n m =
  let out = ref [] in
  let a = Array.make n 1 in
  let rec go i = if i = n then out := Array.copy a :: !out
    else for v = 1 to m do a.(i) <- v; go (i + 1) done in
  go 0; List.rev !out

let drop_at k xs =
  Array.of_list (List.filteri (fun i _ -> i <> k) (Array.to_list xs))

let mk m xs nv = { xs; nv; ov = occ m xs; iv = 0; vv = 0 }

let inv_results = ref []
let inv_check name src ok =
  inv_results := !inv_results @ [ (name, src, ok) ]

(* contractible wrt VARIABLES: dropping any one variable preserves satisfaction,
   with the other arguments unchanged *)
let contractible g =
  let ok = ref true in
  List.iter (fun n -> List.iter (fun m ->
      List.iter (fun xs ->
          let (lo, hi) = nv_range { n; m; rows = 0 } g in
          for nv = lo to hi do
            if sat_ground m g (mk m xs nv) then
              for k = 0 to n - 1 do
                let xs' = drop_at k xs in
                if not (sat_ground m g (mk m xs' nv)) then ok := false
              done
          done)
        (vecs n m))
      [2; 3]) [2; 3; 4];
  !ok

(* extensible wrt VARIABLES: appending any value preserves satisfaction *)
let extensible g =
  let ok = ref true in
  List.iter (fun n -> List.iter (fun m ->
      List.iter (fun xs ->
          let (lo, hi) = nv_range { n; m; rows = 0 } g in
          for nv = lo to hi do
            if sat_ground m g (mk m xs nv) then
              for v = 1 to m do
                let xs' = Array.append xs [| v |] in
                if not (sat_ground m g (mk m xs' nv)) then ok := false
              done
          done)
        (vecs n m))
      [2; 3]) [2; 3];
  !ok

let run_invariants () =
  (* --- atleast_nvalue / atmost_nvalue: the two M-1 verified --- *)
  inv_check "atleast_nvalue extensible wrt VARIABLES" "gccat Catleast_nvalue"
    (extensible AtLeast);
  inv_check "atmost_nvalue contractible wrt VARIABLES" "gccat Catmost_nvalue"
    (contractible AtMost);
  inv_check "atleast_nvalue monotone: NVAL can be decreased" "gccat Catleast_nvalue"
    (let ok = ref true in
     List.iter (fun n -> List.iter (fun m ->
         List.iter (fun xs ->
             for nv = 0 to n do
               if sat_ground m AtLeast (mk m xs nv) then
                 for nv' = 0 to nv do
                   if not (sat_ground m AtLeast (mk m xs nv')) then ok := false done
             done) (vecs n m)) [2; 3]) [2; 3; 4];
     !ok);
  (* --- the four fetched for W1-T8 --- *)
  inv_check "alldifferent contractible wrt VARIABLES" "gccat Calldifferent" (contractible AllDiff);
  inv_check "all_equal contractible wrt VARIABLES" "gccat Call_equal" (contractible AllEq);
  inv_check "increasing contractible wrt VARIABLES" "gccat Cincreasing" (contractible Incr);
  inv_check "decreasing contractible wrt VARIABLES" "gccat Cdecreasing" (contractible Decr);
  (* --- functional dependencies --- *)
  inv_check "nvalue: NVAL determined by VARIABLES" "gccat Cnvalue"
    (let ok = ref true in
     List.iter (fun n -> List.iter (fun m ->
         List.iter (fun xs ->
             let c = ref 0 in
             for nv = 0 to n do if sat_ground m NValue (mk m xs nv) then incr c done;
             if !c <> 1 then ok := false) (vecs n m)) [2; 3]) [2; 3; 4];
     !ok);
  inv_check "gcc: NOCCURRENCE determined by VARIABLES and VAL" "gccat Cglobal_cardinality"
    (let ok = ref true in
     List.iter (fun n -> List.iter (fun m ->
         List.iter (fun xs ->
             let a = { xs; nv = 0; ov = occ m xs; iv = 0; vv = 0 } in
             if not (sat_ground m Gcc a) then ok := false;
             for k = 0 to m - 1 do
               let o' = Array.copy a.ov in
               o'.(k) <- o'.(k) + 1;
               if sat_ground m Gcc { a with ov = o' } then ok := false
             done) (vecs n m)) [2; 3]) [2; 3; 4];
     !ok);
  inv_check "element: VALUE determined by INDEX and TABLE" "gccat Celement"
    (let ok = ref true in
     List.iter (fun n -> List.iter (fun m ->
         List.iter (fun xs ->
             for iv = 1 to n do
               let c = ref 0 in
               for vv = 1 to m do
                 if sat_ground m Elem { xs; nv = 0; ov = [||]; iv; vv } then incr c done;
               if !c <> 1 then ok := false
             done) (vecs n m)) [2; 3]) [2; 3; 4];
     !ok);
  inv_check "nvalue contractible wrt VARIABLES when NVAL=1" "gccat Cnvalue"
    (let ok = ref true in
     List.iter (fun n -> List.iter (fun m ->
         List.iter (fun xs ->
             if sat_ground m NValue (mk m xs 1) then
               for k = 0 to n - 1 do
                 if not (sat_ground m NValue (mk m (drop_at k xs) 1)) then ok := false done)
           (vecs n m)) [2; 3]) [2; 3; 4];
     !ok);
  inv_check "nvalue contractible wrt VARIABLES when NVAL=|VARIABLES|" "gccat Cnvalue (condition re-evaluated)"
    (let ok = ref true in
     List.iter (fun n -> List.iter (fun m ->
         List.iter (fun xs ->
             if sat_ground m NValue (mk m xs n) then
               for k = 0 to n - 1 do
                 if not (sat_ground m NValue (mk m (drop_at k xs) (n - 1))) then ok := false done)
           (vecs n m)) [2; 3]) [2; 3; 4];
     !ok);
  (* --- defence (b): implications between entries, docs/GCCAT.md section 3 --- *)
  let imply name src p q =
    inv_check name src
      (let ok = ref true in
       List.iter (fun n -> List.iter (fun m ->
           List.iter (fun xs -> for k = 0 to n do
               if p m n xs k && not (q m n xs k) then ok := false done) (vecs n m))
           [2; 3]) [2; 3; 4];
       !ok)
  in
  imply "all_equal => increasing" "gccat See also / docs/GCCAT.md s3"
    (fun m _ xs _ -> sat_ground m AllEq (mk m xs 0)) (fun m _ xs _ -> sat_ground m Incr (mk m xs 0));
  imply "all_equal => decreasing" "gccat See also / docs/GCCAT.md s3"
    (fun m _ xs _ -> sat_ground m AllEq (mk m xs 0)) (fun m _ xs _ -> sat_ground m Decr (mk m xs 0));
  imply "nvalue(X,k) => atleast_nvalue(X,k)" "docs/GCCAT.md s3"
    (fun m _ xs k -> sat_ground m NValue (mk m xs k)) (fun m _ xs k -> sat_ground m AtLeast (mk m xs k));
  imply "nvalue(X,k) => atmost_nvalue(X,k)" "docs/GCCAT.md s3"
    (fun m _ xs k -> sat_ground m NValue (mk m xs k)) (fun m _ xs k -> sat_ground m AtMost (mk m xs k));
  imply "alldifferent <=> nvalue(X,n)" "docs/GCCAT.md s3"
    (fun m _ xs _ -> sat_ground m AllDiff (mk m xs 0)) (fun m n xs _ -> sat_ground m NValue (mk m xs n));
  imply "nvalue(X,n) => alldifferent" "docs/GCCAT.md s3 (converse)"
    (fun m n xs _ -> sat_ground m NValue (mk m xs n)) (fun m _ xs _ -> sat_ground m AllDiff (mk m xs 0));
  imply "alldifferent => every gcc count <= 1" "docs/GCCAT.md s3"
    (fun m _ xs _ -> sat_ground m AllDiff (mk m xs 0))
    (fun m _ xs _ -> Array.for_all (fun c -> c <= 1) (occ m xs));
  print_endline "== defences on the hand-encoded ground semantics (W1-T8) ==";
  print_endline "   These check the ENCODING, not the rules — the exposure docs/VALIDATOR.md names.";
  let bad = ref 0 in
  List.iter (fun (name, src, ok) ->
      if not ok then incr bad;
      Printf.printf "  %-58s %-44s %s\n" name src (if ok then "ok" else "FAILED"))
    !inv_results;
  if !bad = 0 then
    Printf.printf "  -- %d/%d invariants hold; the encodings are consistent with the catalog\n"
      (List.length !inv_results) (List.length !inv_results)
  else Printf.printf "  -- %d INVARIANT(S) FAILED: a ground semantics is mis-transcribed\n" !bad;
  print_newline ();
  !bad

(* ==================== self-test: positive and negative controls ==================== *)

(* A checker that flags everything proves nothing. These control rules are
   hand-written in the same LaTeX dialect the catalog uses, and the run asserts
   that each lands in the verdict it is supposed to. If a control regresses,
   the catalog verdicts above are not to be believed. W1-T8 added five more so
   that every new atom shape (>=, <, O_t, I, V) and the new index-equation
   modification are covered by a control in BOTH directions. *)
let controls =
  [ (* domain of X_i reduced to {t} really does entail X_i = t, and the premise
       cannot be dropped: a genuine sound+minimal rule *)
    ("sound+minimal", `NV AtMost,
     "$$\\frac{X_{i} \\neq t',~\\forall t',~t' \\neq t,~t' \\in \\llbracket1,m\\rrbracket}{X_{i}=t}$$",
     Minimal);
    (* the same rule with a redundant bound on N bolted on *)
    ("sound, redundant premise", `NV AtMost,
     "$$\\frac{X_{i} \\neq t',~\\forall t',~t' \\neq t,~t' \\in \\llbracket1,m\\rrbracket~~~~N \\geq p,~\\forall p,~p \\in \\llbracket1,n\\rrbracket}{X_{i}=t}$$",
     NotMinimal [1]);
    (* flatly contradictory *)
    ("unsound", `NV AtMost,
     "$$\\frac{X_{i}=t,~i \\in \\llbracket1,n\\rrbracket,~t \\in \\llbracket1,m\\rrbracket}{X_{i} \\neq t}$$",
     Unsound "");
    (* premises that no store can satisfy *)
    ("vacuous", `NV AtMost,
     "$$\\frac{X_{i} \\neq t,~\\forall i,~i \\in \\llbracket1,n\\rrbracket,~\\forall t,~t \\in \\llbracket1,m\\rrbracket}{N<p}$$",
     Vacuous);
    (* W1-T8: the bounds atoms. Under all-equal, every other variable being >= t
       forces X_i >= t, and the premise cannot be dropped. *)
    ("BC >= sound+minimal", `Simple (AllEq, 3, 3),
     "$$\\frac{X_{i'} \\geq t,~\\forall i',~i' \\neq i,~i' \\in \\llbracket1,n\\rrbracket,~i \\in \\llbracket1,n\\rrbracket}{X_{i} \\geq t}$$",
     Minimal);
    (* W1-T8: index equations, positive. Offset 2, so this is not a catalog rule. *)
    ("index equation sound+minimal", `Simple (Incr, 3, 3),
     "$$\\frac{X_{i'} \\geq t,~i'=i-2}{X_{i} \\geq t}$$",
     Minimal);
    (* W1-T8: index equations, negative — the same shape read against the
       opposite ordering, where it is false. *)
    ("index equation unsound", `Simple (Decr, 3, 3),
     "$$\\frac{X_{i'} \\geq t,~i'=i-1}{X_{i} \\geq t}$$",
     Unsound "");
    (* W1-T8: the O_t atoms of gcc. All variables equal to t forces O_t >= p
       for every p in [1,n]. *)
    ("O-atom sound+minimal", `Simple (Gcc, 2, 2),
     "$$\\frac{X_{i'}=t,~\\forall i',~i' \\in \\llbracket1,n\\rrbracket}{O_{t} \\geq p}$$",
     Minimal);
    (* W1-T8: the O_t atoms again, in the NOT MINIMAL direction, and in a shape
       that is deliberately not any catalog rule: "all variables equal t" already
       entails O_t >= p, so "X_i = t" bolted on is droppable. *)
    ("O-atom redundant premise", `Simple (Gcc, 2, 2),
     "$$\\frac{X_{i'}=t,~\\forall i',~i' \\in \\llbracket1,n\\rrbracket~~~~X_{i} \\neq t',~\\forall t',~t' \\neq t,~t' \\in \\llbracket1,m\\rrbracket}{O_{t} \\geq p}$$",
     NotMinimal [1]);
    (* W1-T8: the V atom of element. If no variable takes t then V = X[I] cannot
       take t either, and the premise cannot be dropped. *)
    ("V-atom sound+minimal", `Simple (Elem, 2, 2),
     "$$\\frac{X_{i} \\neq t,~\\forall i,~i \\in \\llbracket1,n\\rrbracket}{V \\neq t}$$",
     Minimal);
    (* W1-T8: the I atom of element, negative — knowing the index says nothing
       about the value at that index. *)
    ("I-atom unsound", `Simple (Elem, 2, 2),
     "$$\\frac{I=i}{X_{i} \\neq t}$$",
     Unsound "") ]

let same_kind a b =
  match (a, b) with
  | (Unsound _, Unsound _) | (Ambiguous _, Ambiguous _) -> true
  | (OnlyFiringUnsound _, OnlyFiringUnsound _) -> true
  | (NotMinimal x, NotMinimal y) -> x = y
  | (Vacuous, Vacuous) | (Minimal, Minimal) -> true
  | _ -> false

let run_selftest () =
  print_endline "== self-test: controls (a checker that flags everything proves nothing) ==";
  let bad = ref 0 in
  List.iter
    (fun (name, which, tex, want) ->
       let sc = mk_scope "<control>" which in
       let r = List.hd (parse_rules tex) in
       let (v, _, agreed) = classify sc r in
       let ok = same_kind v want && agreed in
       if not ok then incr bad;
       Printf.printf "  %-30s expected %-18s got %-18s %s\n" name
         (verdict_name want) (verdict_name v)
         (if ok then "ok" else "MISMATCH"))
    controls;
  if !bad = 0 then print_endline "  -- all controls behaved; the verdicts below are worth reading"
  else Printf.printf "  -- %d CONTROL(S) FAILED: do not believe the verdicts below\n" !bad;
  print_newline ();
  !bad

(* ==================== the catalog ==================== *)

(* In scope: an entry whose ground semantics can be stated over the symbols the
   rules actually use. Out of scope: an entry whose rules quantify over index
   sets the printer never defines (W1-T2), or whose parameters appear in no
   atom. Out of scope is a RESULT, not a gap — see the W1-T8 report. *)

let in_scope =
  [ ("cata/alldifferent.tex",   `Simple (AllDiff, 3, 3));
    ("cata/allequal.tex",       `Simple (AllEq, 3, 3));
    ("cata/increasing.tex",     `Simple (Incr, 3, 3));
    ("cata/decreasing.tex",     `Simple (Decr, 3, 3));
    ("cata/element.tex",        `Simple (Elem, 2, 2));
    ("cata/nvalues.tex",        `Simple (NValue, 2, 2));
    ("cata/gcc.tex",            `Simple (Gcc, 2, 2));
    ("cata/sum.tex",            `Simple (Sum, 2, 2));
    ("cata/atleastnvalues.tex", `NV AtLeast);
    ("cata/atmostnvalues.tex",  `NV AtMost);
    ("cata/table.tex",          `Table) ]

let out_of_scope =
  [ ("cata/among.tex",
     "index set D_4 is never defined by the printer (W1-T2), AND among's count \
      variable appears in no atom, so the rules constrain X alone while `among` \
      restricts X only jointly with that count");
    ("cata/cumulative.tex",
     "the durations d_i appear as uninterpreted symbols inside index equations \
      (t'=t-d_i), AND the resource capacity appears in no atom, so the rule is \
      schematic over a parameter the artifact never states");
    ("cata/range.tex",
     "index sets D_5, D_6 are never defined by the printer (W1-T2); this is \
      Bessiere's set RANGE and its set variables appear in no atom (gccat's \
      range_ctr is an unrelated constraint — docs/GCCAT.md s5.2)");
    ("cata/regular.tex",
     "index sets D_8, D_9 — the transition relation — are never defined by the \
      printer (W1-T2); gccat has no `regular` entry at all (docs/GCCAT.md s5.1)");
    ("cata/roots.tex",
     "index sets D_5, D_6 are never defined by the printer (W1-T2); the set \
      variables S and T appear in no atom") ]

(* ==================== main ==================== *)

let () =
  let root = ref "." and only_self = ref false in
  Array.iteri (fun i a ->
      if i > 0 then
        if a = "--selftest" then only_self := true else root := a)
    Sys.argv;
  print_endline "== W0-T1 validator, extended to the catalog by W1-T8 ==";
  print_endline "Scope: 11 of the 16 catalog entries. The other 5 are reported out of scope";
  print_endline "with a reason, not skipped. Rules are PARSED from the shipped .tex; the ground";
  print_endline "semantics of each decomposition is HAND-ENCODED from the generator source and";
  print_endline "then checked against the Global Constraint Catalog's closure properties.";
  print_endline "docs/VALIDATOR.md says exactly what that costs in trust.";
  print_newline ();
  let inv = run_invariants () in
  let ctl = run_selftest () in
  if !only_self then exit (if ctl = 0 && inv = 0 then 0 else 1);
  let flagged = ref 0 and checked = ref 0 and xbad = ref 0
  and minimal = ref 0 and skipped = ref 0 in
  List.iter
    (fun (path, which) ->
       let sc = mk_scope path which in
       match (try `R (parse_rules (read_file (Filename.concat !root path)))
              with Unparsed msg -> `E msg) with
       | `E msg ->
         incr skipped;
         Printf.printf "---- %s  (UNPARSED) ----\n    %s\n\n" path msg
       | `R rules ->
         Printf.printf "---- %s  (%d rules) ----\n" path (List.length rules);
         List.iteri
           (fun ri r ->
              incr checked;
              let (v, results, agreed) = classify sc r in
              if is_flag v then incr flagged else incr minimal;
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
    in_scope;
  print_endline "== out of scope: what could not be validated, and why ==";
  print_endline "   'Cannot be validated because the artifact is underspecified' is a result,";
  print_endline "   not a gap. Evidence for W1-T2.";
  let oos_rules = ref 0 in
  List.iter
    (fun (path, why) ->
       let text = try read_file (Filename.concat !root path) with _ -> "" in
       let nr = List.length (split_sub "\\frac" text) - 1 in
       oos_rules := !oos_rules + nr;
       let dks = dks_of_text text in
       let parsed = try ignore (parse_rules text); "parses" with
         | Unparsed msg -> "UNPARSED: " ^ msg
         | _ -> "parse error" in
       Printf.printf "\n  %s  (%d rules, %s)\n" path nr parsed;
       Printf.printf "    undefined index sets referenced: %s\n"
         (if dks = [] then "(none)" else String.concat ", " (List.map (fun k -> "D_" ^ k) dks));
       Printf.printf "    reason: %s\n" why)
    out_of_scope;
  print_newline ();
  Printf.printf "== %d rules checked in %d entries: %d SOUND and MINIMAL, %d flagged ==\n"
    !checked (List.length in_scope - !skipped) !minimal !flagged;
  Printf.printf "== %d rules in %d entries out of scope (underspecified artifact) ==\n"
    !oos_rules (List.length out_of_scope);
  if !xbad > 0 then
    Printf.printf "== %d cross-check disagreements: FIX validator.ml BEFORE BELIEVING THIS ==\n" !xbad;
  if inv > 0 then
    Printf.printf "== %d encoding invariant(s) failed: THE GROUND SEMANTICS IS WRONG ==\n" inv;
  exit (if ctl > 0 || inv > 0 || !xbad > 0 then 2 else if !flagged > 0 then 1 else 0)
