(*Moulinette by Arthur GONTIER 2020 (explenation generator from constraint decomposition)*) 
open List 
type var_name = X | B of int | T | I | V | N | O
(*index modifications*) 
type ind_name = I of int | T of int | P of int | R of int
type ind_const = C of int 
type ind_symbols = PLUS|MINUS|IN|NEQ|LEQ|GEQ|EQ 
(*==========================================================================
  G1 and G8 — the two cheapest format gaps, closed together because they are
  the same gap seen twice: an index set the decomposition wants to talk about
  but the format cannot NAME, and a threshold the decomposition wants to talk
  about but the format cannot CARRY.

  G1 (docs/DECOMP_FORMAT_NOTES.md): "no way to carry a bare integer threshold
  into the printed rule ... the constant is never captured as an event, index,
  or anything else the printer walks -- it lives only as an OCaml literal baked
  into which schema gets called". rule5/rule6/rule7 ARE "Boolean sum <=/>=/= c"
  and nothing anywhere holds that c. So at_most(c,x,v), at_least, exactly and
  alldifferent's implicit 1 all print rules that never mention their own bound.

  G8: "ind_set names only whole predefined ranges -- no subrange, no exclusion".
  D of int is an opaque per-decomposition counter, so D 4 is the row set in
  table.tex and the value set in among.tex; W1-T2 rightly refuses to print any
  of them. D2 of ind_name list has no printer at all (that is G7).

  The fix for both is to make ind_set a SET TERM that prints its own definition,
  rather than a name the artifact would have to define elsewhere:

    DSub  (parent,a,b)        a literal subrange, [[a,b]]
    DExc  (parent,elts)       parent minus listed constants and/or indices
    DPar  (name,parent)       a named parameter subset: "s, s subset of [[1,m]]"
    DCard (name,parent,op,b)  as DPar plus a cardinality: "..., |S| = c+1"

  DCard is where the threshold lives, and it is what closes G1: the bound is an
  ind_bound value carried inside the index data, so the printer walks it and it
  reaches the LaTeX. ind_bound is BInt for a literal and BPar (name,offset) for
  a symbolic parameter, because the bound a rule needs is not always the bound
  in the signature -- at_most's witness set has c+1 elements, not c (see the
  atmost decomposition below for why).

  These four print their own meaning, so ind_set_defined accepts them: they are
  not D_4. The W1-T2 refusal is untouched for D of int and D2, which still name
  nothing -- table, regular, roots and range are deliberately NOT changed here,
  and their branches are still refused.
  ========================================================================*)
type ind_bound = BInt of int | BPar of string*int
type ind_elt   = EInt of int | EInd of ind_name | EPar of string
type ind_set = D of int | D2 of ind_name list
             | DSub  of ind_set*int*int                       (*[[a,b]]*)
             | DExc  of ind_set*ind_elt list                  (*parent \ {..}*)
             | DPar  of string*ind_set                        (*named parameter subset*)
             | DCard of string*ind_set*ind_symbols*ind_bound  (*named subset of given cardinality*)
type ind_modifs = | Set of ind_name*ind_symbols*ind_set (*I∈D*) 
                  | Rel of ind_name*ind_symbols*ind_name (*I≠I2*) 
                  | Addint of ind_name*ind_name*ind_symbols*int (*I2=I+1*) 
                  | Addcst of ind_name*ind_name*ind_symbols*ind_const*ind_name (*I3=I2-C I*) 
                  | EXFORALL of ind_name 
                  | EXEXISTS of ind_name 
type consistancy = AC | BC 
(*event types*) 
type index = Ind of ind_name*ind_modifs list
(*==========================================================================
  W1-T7 — index modifications are DATA, not closures.

  A decomp_event used to carry two `index list -> index list` OCaml closures,
  one for the descending traversal and one for the ascending one. A closure
  cannot be printed, compared or inverted, so nothing could say what a
  decomposition means without running it, a wrong composition produced a
  plausible-looking wrong rule with no way to notice, and validator.ml had to
  hand-encode the ground semantics of every entry instead of deriving it
  (docs/VALIDATOR.md). D-0009 sharpens this: the emitted .tex is itself lossy.

  `ind_op` is the first-order replacement. Every combinator the decompositions
  used is one constructor, `apply_op` is the interpreter, and because the type
  is first-order, structural equality compares two modifications and
  `invert_op` inverts the ones that have an inverse.

  A family is a letter, not a numbered index: `i_out` drops the first index
  named i, i', i''..., so the number never mattered and keeping it in the data
  would have made equal modifications compare unequal.
  ========================================================================*)
type ind_fam = FI | FT | FP | FR
type ind_op =
  | OpId                                                     (*id*)
  | OpOn     of ind_fam * ind_set             (*oni, ontin d: DISCARD the index list, replace it with one fresh index of that family ranging over the set*)
  | OpOut    of ind_fam                       (*i_out: drop the FIRST index of that family*)
  | OpForall of ind_fam * ind_set             (*foralli, foralltin d: prepend a fresh universally bound index*)
  | OpPoint  of ind_fam * ind_set             (*pointi, pointtin d: prepend a fresh index that is RANGED BUT UNBOUND — a free parameter of the rule schema, not a quantifier (W1-T9)*)
  | OpSum    of ind_fam * ind_set             (*sumi: every index of that family becomes a primed, universally bound sibling constrained to differ from it*)
  | OpPrim   of ind_fam * ind_set             (*tprimin d: as OpSum but the sibling is not bound here*)
  | OpShift  of ind_fam * ind_symbols * int   (*iplus k, imoin k: i' = i +/- k*)
  | OpShiftC of ind_fam * ind_symbols * ind_const * ind_fam  (*tplusci c: t' = t +/- c_i*)
  | OpSeq    of ind_op list                   (*imap: applied RIGHT TO LEFT, exactly as imap composed its closures*)
type event = | Global_event of bool*var_name*index list*consistancy
             | Decomp_event of bool*var_name*index list
type decomp_event = | Global_devent  of bool*var_name*ind_op*ind_op*consistancy
                    | Decomp_devent  of bool*var_name*ind_op*ind_op
                    | Reified_devent of bool*var_name*ind_op*ind_op
(*explanation tree*) 
type leaf = Var of event | T | F | IM | R | FE 
type tree = | Lit of leaf 
            | EXOR of event*tree list 
            | EXAND of event*tree list 
(*constraint with id, explanation rule and devent list*) 
type decomp_ctr = Decomp of int*(event->decomp_event->decomp_ctr->decomp_ctr list->event list->tree)*decomp_event list

(*event accessors*)
let sign x = match x with Global_event (b,_,_,_) | Decomp_event (b,_,_) -> b
let dsign x = match x with Global_devent (b,_,_,_,_) | Decomp_devent (b,_,_,_) | Reified_devent (b,_,_,_) -> b
let name x = match x with Global_event (_,n,_,_) | Decomp_event (_,n,_) -> n
let dname x = match x with Global_devent (_,n,_,_,_) | Decomp_devent (_,n,_,_) | Reified_devent (_,n,_,_) -> n
let index_list x = match x with Global_event (_,_,l,_) | Decomp_event (_,_,l)->l
let cons x = match x with Global_event (_,_,_,c) -> c
  | _ -> failwith "inner decomp events have no consistancy"
let dcons x = match x with Global_devent (_,_,_,_,c) -> c 
  | _ -> failwith "inner decomp events have no consistancy"
let index_update x = match x with Global_devent (_,_,f,_,_) | Decomp_devent (_,_,f,_) | Reified_devent (_,_,f,_) -> f
let index_propagate x = match x with Global_devent (_,_,_,f,_) | Decomp_devent (_,_,_,f) | Reified_devent (_,_,_,f) -> f
let ind_name i = match i with Ind (i,_) -> i
let ind_modifs_list i = match i with Ind (_,l) -> l
let decomp_ctr_rule c = match c with Decomp (_,r,_) -> r
let decomp_ctr_id c = match c with Decomp (id,_,_) -> id
let decomp_event_list c = match c with Decomp (_,_,l) -> l

let prim i = match i with I a -> I (a+1) | T a -> T (a+1) | P a -> P (a+1) | R a -> R (a+1) 


(*W1-T7 — the interpreter, the printer, the inverse.*)
let fam_ind (f:ind_fam) : ind_name = match f with FI -> I 1 | FT -> T 1 | FP -> P 1 | FR -> R 1
let fam_of (i:ind_name) : ind_fam = match i with I _ -> FI | T _ -> FT | P _ -> FP | R _ -> FR
let fam_letter (f:ind_fam) = match f with FI -> "i" | FT -> "t" | FP -> "p" | FR -> "r"
let rec fam_find f il = match il with
  | [] -> failwith ("Index "^fam_letter f^" has left the building")
  | i::tl -> if fam_of (ind_name i) = f then i else fam_find f tl
let rec fam_map f g il = match il with
  | [] -> [] | i::tl -> if fam_of (ind_name i) = f then g i::fam_map f g tl else i::fam_map f g tl
let rec fam_out f il = match il with
  | [] -> [] | i::tl -> if fam_of (ind_name i) = f then tl else i::fam_out f tl
(*the index nodes the old closures built, unchanged*)
let sum_node i d  = Ind (prim (ind_name i), [EXFORALL (prim (ind_name i)); Set (prim (ind_name i),IN,d); Rel (prim (ind_name i), NEQ, ind_name i)]@ind_modifs_list i)
let prim_node i d = Ind (prim (ind_name i), [Set (prim (ind_name i),IN,d); Rel (prim (ind_name i), NEQ, ind_name i)]@ind_modifs_list i)
let shift_node i sym k   = Ind (prim (ind_name i), [Addint (prim (ind_name i), ind_name i, sym, k)]@ind_modifs_list i)
let shiftc_node i sym c j= Ind (prim (ind_name i), [Addcst (prim (ind_name i), ind_name i, sym, c, ind_name j)]@ind_modifs_list i)
let rec apply_op op il = match op with
  | OpId             -> il
  | OpOn     (f,d)   -> Ind (fam_ind f,Set (fam_ind f,IN,d)::[])::[]
  | OpOut     f      -> fam_out f il
  | OpForall (f,d)   -> Ind (fam_ind f,[EXFORALL (fam_ind f);Set (fam_ind f,IN,d)])::il
  | OpPoint  (f,d)   -> Ind (fam_ind f,[Set (fam_ind f,IN,d)])::il
  | OpSum    (f,d)   -> fam_map f (fun x -> sum_node x d) il
  | OpPrim   (f,d)   -> fam_map f (fun x -> prim_node x d) il
  | OpShift  (f,s,k) -> fam_map f (fun x -> shift_node x s k) il
  | OpShiftC (f,s,c,g) -> fam_map f (fun x -> shiftc_node x s c (fam_find g il)) il
  | OpSeq     l      -> fold_right (fun o acc -> apply_op o acc) l il

let op_sym s = match s with PLUS->"+"|MINUS->"-"|IN->" in "|NEQ->"<>"|LEQ->"<="|GEQ->">="|EQ->"="
(*moved up from the LaTeX printer block: op_set and print_bound need it, and
  both types are already in scope here, so `I` still resolves to ind_name.*)
let printind_name_int a = match a with 1 -> "" | 2 -> "'" | 3 -> "''" | _ -> "_{"^string_of_int a^"}"
let printind_name i = match i with I a -> "i"^printind_name_int a | T a -> "t"^printind_name_int a | P a -> "p"^printind_name_int a | R a -> "r"^printind_name_int a
let print_bound b = match b with
  | BInt k     -> string_of_int k
  | BPar (s,0) -> s
  | BPar (s,k) -> if k > 0 then s^"+"^string_of_int k else s^"-"^string_of_int (-k)
let print_elt e = match e with EInt k -> string_of_int k | EInd i -> printind_name i | EPar s -> s
let rec op_set s = match s with
  | D a -> "D"^string_of_int a
  | D2 _ -> "D(list)"
  | DSub (_,a,b) -> "["^string_of_int a^","^string_of_int b^"]"
  | DExc (p,es) -> op_set p^"\\{"^String.concat "," (map print_elt es)^"}"
  | DPar (nm,p) -> nm^" subset of "^op_set p
  | DCard (nm,p,sym,b) -> nm^" subset of "^op_set p^", |"^nm^"|"^op_sym sym^print_bound b
let rec print_op op = match op with
  | OpId             -> "id"
  | OpOn     (f,d)   -> "on "^fam_letter f^" in "^op_set d
  | OpOut     f      -> "out "^fam_letter f
  | OpForall (f,d)   -> "forall "^fam_letter f^" in "^op_set d
  | OpPoint  (f,d)   -> "point "^fam_letter f^" in "^op_set d
  | OpSum    (f,d)   -> "sum "^fam_letter f^"' in "^op_set d^" ("^fam_letter f^"'<>"^fam_letter f^")"
  | OpPrim   (f,d)   -> "prim "^fam_letter f^"' in "^op_set d^" ("^fam_letter f^"'<>"^fam_letter f^")"
  | OpShift  (f,s,k) -> fam_letter f^"'="^fam_letter f^op_sym s^string_of_int k
  | OpShiftC (f,s,_,g) -> fam_letter f^"'="^fam_letter f^op_sym s^"d_"^fam_letter g
  | OpSeq     l      -> "("^String.concat " o " (map print_op l)^")"

(*Partial inverse, on the TERM. OpOn and OpOut destroy information and
  OpSum/OpPrim are not injective, so None is the honest answer for them.
  Composition inverts in reverse order, matching OpSeq's right-to-left
  application.

  What "inverse" does and does not mean here, MEASURED 2026-09-18 by applying
  op then invert_op op to [Ind (I 1,[]); Ind (T 1,[])] and comparing:

    OpId, OpForall/OpOut, OpSeq of those   round-trip EXACTLY, back = input.
    OpShift, OpShiftC                      do NOT. i'=i+1 then i'=i-1 yields
                                           i'' carrying BOTH Addint modifiers.

  The shift case is inverse in meaning (i''=i) but not on the representation,
  because applying a modification APPENDS to the index's modifier list instead
  of rewriting the index. That accumulation is the same mechanism that makes a
  premise carry a self-contradictory binder prefix in the emitted LaTeX
  (D-0009), so it is recorded here rather than papered over. Accordingly the
  run report says "declared inverse", which is a statement about the two terms,
  not a claim that the index lists round-trip.*)
let rec invert_op op = match op with
  | OpId               -> Some OpId
  | OpForall (f,_)     -> Some (OpOut f)
  | OpPoint  (f,_)     -> Some (OpOut f)
  | OpShift  (f,PLUS,k)  -> Some (OpShift (f,MINUS,k))
  | OpShift  (f,MINUS,k) -> Some (OpShift (f,PLUS,k))
  | OpShiftC (f,PLUS,c,g)  -> Some (OpShiftC (f,MINUS,c,g))
  | OpShiftC (f,MINUS,c,g) -> Some (OpShiftC (f,PLUS,c,g))
  | OpSeq l            -> invert_seq (rev l)
  | _                  -> None
and invert_seq l = match l with
  | [] -> Some (OpSeq [])
  | o::tl -> (match invert_op o with
      | None -> None
      | Some a -> (match invert_seq tl with
          | Some (OpSeq b) -> Some (OpSeq (a::b))
          | _ -> None))

let id = OpId(*identity index modification*)

(*W1-T7's payoff, exercised rather than merely available: every run prints the
  decomposition each catalog entry was generated from, which was impossible
  while the modifications were closures. `invert_op` is applied to each
  ascending modification and the result COMPARED with the descending one — the
  two are meant to be a descending/ascending pair, so "propagate inverts
  update" is a property that can now be stated per devent instead of assumed.*)
let print_var_name (v:var_name) = match v with
  | X -> "X" | B i -> "B"^string_of_int i | T -> "T" | I -> "I" | V -> "V" | N -> "N" | O -> "O"
let print_devent de =
  let u = index_update de in
  let g = index_propagate de in
  Printf.printf "      %-7s %-4s  update %-30s propagate %-30s %s\n"
    (match de with Global_devent _ -> "global" | Reified_devent _ -> "reified" | Decomp_devent _ -> "decomp")
    ((if dsign de then "" else "!")^print_var_name (dname de))
    (print_op u) (print_op g)
    (match invert_op g with
     | Some iv -> if iv = u then "propagate is the declared inverse of update"
                  else "inverse of propagate is "^print_op iv^", NOT the update"
     | None -> "propagate is not invertible")
let print_decomp dec =
  Printf.printf "    decomposition (W1-T7), %d atomic constraint(s):\n" (length dec);
  iter (fun c -> Printf.printf "    ctr %d\n" (decomp_ctr_id c);
                 iter print_devent (decomp_event_list c)) dec
let n   e = match e with(*negation of event x*) 
  | Global_event (b,n,l,c)-> Global_event (not b,n,l,c)
  | Decomp_event (b,n,l) -> Decomp_event (not b,n,l)
(*apply index modification functions on an event*) 
let ap  e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,apply_op (index_propagate de) (apply_op (index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,apply_op (index_propagate de) (apply_op (index_update dep) (index_list e)))
(*apply index modification functions with negation*) 
let nap e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,apply_op (index_propagate de) (apply_op (index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,apply_op (index_propagate de) (apply_op (index_update dep) (index_list e)))
(*apply index modification functions with particularities for sum, bigvee and bigwedge*)
let addexists de = (fun ill -> (match (apply_op (index_propagate de) []) with Ind (i,il)::[]->Ind (i,EXEXISTS i::il)|_->failwith "missing index set exist")::ill)
let addforall de = (fun ill -> (match (apply_op (index_propagate de) []) with Ind (i,il)::[]->Ind (i,EXFORALL i::il)|_->failwith "missing index set forall")::ill)
let addprim   de = (fun ill -> (match (apply_op (index_propagate de) []) with Ind (i,il)::[]->Ind (prim i,EXFORALL (prim i)::Rel (prim i,NEQ,i)::Set (prim i,IN,match il with Set (_,_,d)::[]->d|_->failwith "missing index set" )::il)|_->failwith "missing index set prim")::ill)
let apexists e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addexists de) (apply_op (index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addexists de) (apply_op (index_update dep) (index_list e)))
let apforall e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addforall de) (apply_op (index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addforall de) (apply_op (index_update dep) (index_list e)))
let apprim e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addprim de) (apply_op (index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addprim de) (apply_op (index_update dep) (index_list e)))
let napexists e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addexists de) (apply_op (index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addexists de) (apply_op (index_update dep) (index_list e)))
let napforall e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addforall de) (apply_op (index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addforall de) (apply_op (index_update dep) (index_list e)))
let napprim e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addprim de) (apply_op (index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addprim de) (apply_op (index_update dep) (index_list e)))

(*Utilitary functions*) 
let rec invars e del = (* devent in decomp ctr list? *) 
  match del with [] -> false | de::tl -> if dname de = name e then true else invars e tl 
let rec vars e del = (* event list with the same name as e*) 
  match del with [] -> [] | de::tl -> if dname de = name e then de::vars e tl else vars e tl 
let rec ctrs e dec = (* constraint list where event e appears*) 
  match dec with [] -> [] | c::tl -> if invars e (decomp_event_list c) then c::ctrs e tl else ctrs e tl 
let rec subl e l = (* event list without event e*) 
  match l with [] -> [] | c::tl -> if (dsign e = dsign c)&&(dname e = dname c) then subl e tl else c::subl e tl 
let rec subc cc l = (* ctr list without constraint cc*) 
  match l with [] -> [] | c::tl -> if  decomp_ctr_id cc = decomp_ctr_id c then subc cc tl else c::subc cc tl 
let rec subi i l = (* ind list without index i*) 
  match l with [] -> [] | j::tl -> if  ind_name i = ind_name j then subi i tl else j::subi i tl 
let rec inl cc l = (* cc in list l? *) 
  match l with [] -> false | c::tl -> if cc=c then true else inl cc tl 
let rec reified_devent del = 
  match del with [] -> Reified_devent (true, T,id,id) | de::tl -> match de with | Reified_devent (_,_,_,_) -> de | _ -> reified_devent tl

 
(*find event e  in the decomposition and call the explanations rules*) 
let rec find e prec dec ch =  
  if inl e ch || inl (n e) ch then Lit R else 
  let cl = ctrs e dec in 
  let cl = subc prec cl in 
  if cl = [] then Lit IM else 
  EXOR (e,flatten (map (fun c-> map (fun de -> (decomp_ctr_rule c) e de c dec (ch@[e])) (vars e (decomp_event_list c))) cl)) 
 
and fre  re e de c dec ch =  (*explanation by refied event*) 
  if dname re  = T then Lit T else EXAND (e,[find ( ap e re de) c dec ch]) 
and fnre re e de c dec ch =  (*explanation by negative refied event*) 
  if dname re  = T then Lit F else EXAND (e,[find (nap e re de) c dec ch])
and fel  del e de c dec ch = (*explanation by event list*) 
  map (fun dee-> find ( ap e dee de) c dec ch) del 
and fnel del e de c dec ch = (*explanation by negative event list*) 
  map (fun dee-> find (nap e dee de) c dec ch) del 

(*==========================================================================
  W1-T9 defect 1 — `allequal` rules 2-3 had the inequality inverted.

  For a reified conjunction R <=> /\_j L_j, deriving that one conjunct L_k is
  FALSE needs BOTH ~R and every other conjunct L_{j!=k}: from ~R alone nothing
  follows about L_k, and from the siblings alone nothing follows either. rule3
  and rule4 built that pair with EXOR when `del` is a single indexed family,
  so each half was emitted as a rule in its own right, without the other. The
  half carrying only the prim siblings is exactly `allequal` rule 2,
  {forall i'!=i: X_i' < t} |- X_i >= t, which is backwards: under all-equal
  every other variable being below t puts X_i below t too. Counterexample
  n=m=2, X=(1,1), t=2 (validator, W1-T8).

  The multi-conjunct branch two lines down already used EXAND, and so do
  rule5/6/7 in the same situation, so this is the singleton case disagreeing
  with every sibling rather than a deliberate reading.

  MEASURED consequence of the repair (make validate, before -> after):
  42 rules -> 35, and every rule that disappears is one the validator flagged;
  no SOUND and MINIMAL rule is lost, the count stays 11. allequal 2 UNSOUND
  -> gone (2 rules left, both SOUND and MINIMAL); atleastnvalues, atmostnvalues
  and nvalues each lose 1 UNSOUND; table loses 2 of its 3 UNSOUND; among loses
  1 out-of-scope rule. The two halves are now an AND, so a branch whose ~R half
  has no explanation dies as a whole and is COUNTED by filter_branches (W1-T3)
  instead of shipping as half a rule. That is what happens to allequal: ~B2/~B3
  are not derivable from B2 \/ B3, so `allequal` honestly has no non-trivial
  rule under this decomposition.

  cata/atleastnvalues.tex and cata/atmostnvalues.tex remain byte-identical
  (checked): both lose the same rule, so W1-T5's evidence is preserved.
  ========================================================================*)
(*Explenation rules*) 
and rule1 e de c dec ch = (*Global_devent<=>Reified_devent*) 
  let re = reified_devent (decomp_event_list c) in 
  let x = hd (subl re (decomp_event_list c)) in 
  if dname re = name e 
  then if dsign de = sign e 
    then EXAND (e,[Lit (Var ( ap e x re))]) 
    else EXAND (e,[Lit (Var (nap e x re))]) 
  else Lit FE

and rule3 e de c dec ch = (*conjonction*) 
  let re = reified_devent (decomp_event_list c) in
  let del = subl re (decomp_event_list c) in
  if dname de = dname re
  then if dsign de = sign e
    then match del with 
      | dee::[] -> EXAND (e,[find (apforall e dee de) c dec ch]) 
      | _       -> EXAND (e, fel del e de c dec ch) 
    else match del with 
      | dee::[] -> EXOR  (e,[find (napexists e dee de) c dec ch]) 
      | _       -> EXOR  (e,fnel del e de c dec ch) 
  else 
    if sign e = dsign de
    then fre re e de c dec ch 
    else match del with
      | dee::[] -> EXAND (e,fnre re e de c dec ch::[find (apprim e dee de) c dec ch]) (*W1-T9*)
      | _       -> EXAND (e,fnre re e de c dec ch::fel (subl de del) e de c dec ch) 

and rule4 e de c dec ch = (*disjunction*) 
  let re = reified_devent (decomp_event_list c) in
  let del = subl re (decomp_event_list c) in
  if dname de = dname re
  then if dsign de = sign e 
    then match del with 
      | dee::[] -> EXOR  (e,[find (apexists e dee de) c dec ch]) 
      | _       -> EXOR  (e,fel del e de c dec ch) 
    else match del with 
      | dee::[] -> EXAND (e,[find (napforall e dee de) c dec ch]) 
      | _       -> EXAND (e,fnel del e de c dec ch) 
  else  
    if sign e = dsign de
    then match del with
      | dee::[] -> EXAND (e,fre re e de c dec ch::[find (napprim e dee de) c dec ch]) (*W1-T9*)
      | _       -> EXAND (e,fre re e de c dec ch::fnel (subl de del) e de c dec ch) 
    else fnre re e de c dec ch 

and rule5 e de c dec ch = (*Bool sum<=c*) 
  let re = reified_devent (decomp_event_list c) in
  match subl re (decomp_event_list c) with
    | dee::[]->
      if dname de = dname re
      then if dsign de = sign e 
        then EXAND (e,[find (napforall e dee de) c dec ch])
        else EXAND (e,[find ( apforall e dee de) c dec ch]) 
      else  
        if sign e = dsign de
        then EXAND (e,fnre re e de c dec ch::[find (napprim e dee de) c dec ch])
        else EXAND (e, fre re e de c dec ch::[find ( apprim e dee de) c dec ch])
    | _ -> failwith "sommes multiples pas encore implémentés"

and rule6 e de c dec ch = (*Bool sum=>c*) 
  let re = reified_devent (decomp_event_list c) in
  match subl re (decomp_event_list c) with
    | dee::[]->
      if dname de = dname re
      then if dsign de = sign e 
        then EXAND (e,[find ( apforall e dee de) c dec ch]) 
        else EXAND (e,[find (napforall e dee de) c dec ch])
      else  
        if sign e = dsign de
        then EXAND (e, fre re e de c dec ch::[find (napprim e dee de) c dec ch])
        else EXAND (e,fnre re e de c dec ch::[find ( apprim e dee de) c dec ch])
    | _ -> failwith "sommes multiples pas encore implémentés"

and rule7 e de c dec ch = (*Bool sum=c*) 
  let re = reified_devent (decomp_event_list c) in
  match subl re (decomp_event_list c) with
    | dee::[]->
      if dname de = dname re
      then if dsign de = sign e 
        then EXAND (e,find (apforall e dee de) c dec ch::[find (napforall e dee de) c dec ch])(*incohérent?*) 
        else EXOR  (e,find (apforall e dee de) c dec ch::[find (napforall e dee de) c dec ch])(*incohérent?*) 
      else  
        if sign e = dsign de
        then EXAND (e,fre re e de c dec ch::[find (napforall e dee de) c dec ch]) 
        else EXAND (e,fre re e de c dec ch::[find ( apforall e dee de) c dec ch]) 
    | _ -> failwith "sommes multiples pas encore implémentés"

let rec removesame l = (*keeps one occurence of each element*)
  match l with []->[]|v::tl->if inl v tl then removesame tl else [v]@(removesame tl) 
(*the branch filter that used to live here is now below the printers: W1-T3*)

let concat l = (*Concaténation d'un EXAND de EXOR en EXOR de EXAND*) 
  match l with []-> [] | l1::[]-> l1 | l1::tl -> fold_left (fun l1 l2 -> flatten (map (fun x -> map (fun y -> x@y) l1) l2)) l1 tl 

let rec an a = (*analysis of the explanation tree, return explanation list*) 
  match a with 
    | Lit x -> [[x]] 
    | EXOR (_,l) -> flatten (map an l) 
    | EXAND (_,l) -> concat (map an l) 

(*Input global event*)
let rule0 e de c dec ch = (*Global_devent<=>Reified_devent*)  
  let re = reified_devent (decomp_event_list c) in 
  if dsign de = sign e 
  then  fre re e de c dec ch
  else fnre re e de c dec ch

(*==========================================================================
  W1-T10 — the printers used to emit the literal STRING "ERROR B "/"ERROR T "
  into the .tex instead of failing. That is W1-T3's disease in the printer: a
  generator failure and a generated artifact were the same observable, and a
  reader of cata/*.tex could not tell an explanation from an error message.

  `B` is an auxiliary of the decomposition. Reaching a printer with one means
  the AND/OR traversal handed it an inner reified variable that no
  Global_devent ever turned back into a solver literal, so there is no rule to
  print. `T` is the name of the placeholder Reified_devent that
  `reified_devent` returns for a constraint carrying none; fre/fnre already
  intercept it as Lit T / Lit F, so a `T` literal reaching a printer means that
  interception was bypassed.

  MEASURED 2026-09-18: raising changes no shipped entry. All 16 regenerate
  byte-identically (make check), because every `B` in today's decompositions
  resolves to a Global_devent first. The first decomposition with an
  accumulated-state auxiliary — `value_precede`, `lex_less` — hits it, and now
  gets a named failure instead of "ERROR B " in its catalog entry.
  ========================================================================*)
exception Generator_failure of string

(*Print explanation in string*) 
let rec printprim n = match n with 1 -> "" | _ ->"'"^printprim (n-1)
(*==========================================================================
  W1-T2 — an index set the printer cannot define is REFUSED, not invented.

  printind_set_int defines exactly three sets: D 1 and D 3 as [1,n] and D 2 as
  [1,m]. Everything else fell through to the string "D_{k}", and D2 to the
  string "setfils", neither of which the artifact ever defines. That is not a
  rendering blemish: W1-V measured it as the reason `among`, `cumulative`,
  `range`, `regular` and `roots` — 5 entries, 14 rules — could not be validated
  at all, because they quantify over sets the artifact never states.

  Worse, and this is why the numbering cannot simply be extended: the `D_k`
  counter is chosen PER DECOMPOSITION, so D 4 is the row set in table.tex and
  the value set in among.tex. `D_4` therefore carries no meaning across
  entries, and defining "D_4" once in the printer would give two different
  entries the same name for two different sets — papering over the defect
  rather than confronting it. Naming them properly is a property of the input
  format, so it belongs to W2-T1/E2, not to the printer.

  The roadmap's judgement, which stands: REFUSING TO EMIT IS BETTER THAN
  PRINTING AN UNDEFINED SET. So:
    - filter_branches drops any branch whose literals reference an undefined
      set, and COUNTS it, exactly as W1-T3 made F-branches loud;
    - these two printers RAISE as a backstop, so an undefined set can never
      reach a .tex even if the filter is ever bypassed.
  An entry all of whose branches are refused still gets its file, containing no
  rule and a diagnostics footer that names the sets — "no rule that this
  artifact can state" is a result, and a silent D_4 was not.
  ========================================================================*)
(*G1/G8: the four new set formers are defined BY BEING PRINTED -- each renders
  its own containment and, for DCard, its own cardinality -- so accepting them
  here is not a relaxation of W1-T2. D of int and D2 are unchanged and still
  refused, which is why table/regular/roots/range still emit nothing.*)
let rec ind_set_defined s = match s with
  | D 1 | D 2 | D 3 -> true | D _ -> false | D2 _ -> false
  | DSub  (p,_,_)   -> ind_set_defined p
  | DExc  (p,_)     -> ind_set_defined p
  | DPar  (_,p)     -> ind_set_defined p
  | DCard (_,p,_,_) -> ind_set_defined p
let printind_set_int a = match a with 1 -> "\\llbracket1,n\\rrbracket" | 2 -> "\\llbracket1,m\\rrbracket" | 3 -> "\\llbracket1,n\\rrbracket"
  | _ -> raise (Generator_failure ("printind_set: index set D_"^string_of_int a^" is referenced but the printer defines no such set, and the D_k counter is per-decomposition so it cannot be defined here (W1-T2)"))
let printcard_sym s = match s with
  | EQ -> "=" | LEQ -> " \\leq " | GEQ -> " \\geq " | NEQ -> " \\neq "
  | PLUS | MINUS | IN -> raise (Generator_failure "printind_set: a cardinality can only be compared with =, <=, >= or <> (G1)")
let rec printind_set s = match s with
  | D a -> printind_set_int a
  | D2 _ -> raise (Generator_failure "printind_set: the D2 (index-list) set variant has no printer; it used to emit the literal string \"setfils\" (W1-T2, consolidated gap G7)" )
  | DSub (_,a,b) -> "\\llbracket"^string_of_int a^","^string_of_int b^"\\rrbracket"
  | DExc (p,es) -> printind_set p^" \\setminus \\{"^String.concat "," (map print_elt es)^"\\}"
  | DPar (nm,p) -> nm^",~"^nm^" \\subseteq "^printind_set p
  | DCard (nm,p,sym,b) -> nm^",~"^nm^" \\subseteq "^printind_set p^",~|"^nm^"|"^printcard_sym sym^print_bound b
let printind_const_int a = match a with 1 -> "" | _ -> "_{"^string_of_int a^"}"
let printind_const c = match c with C a -> "d"^printind_const_int a
let printind_symbols s = match s with PLUS-> "+"|MINUS->"-"|IN->"∈"|NEQ->"≠"|LEQ->"<="|GEQ->">="|EQ->"=" 
let printind_modifs op= match op with 
  | Set (ind1,sym1,set1) ->printind_name ind1^printind_symbols sym1^printind_set set1 
  | Rel (ind1,sym1,ind2) ->printind_name ind1^printind_symbols sym1^printind_name ind2 
  | Addint (ind1,ind2,sym1,int) ->printind_name ind1^"="^printind_name ind2^printind_symbols sym1^string_of_int int 
  | Addcst (ind1,ind2,sym1,cst1,ind3) ->printind_name ind1^"="^printind_name ind2^printind_symbols sym1^printind_const cst1^printind_name ind3 
  | EXFORALL ind1 ->"∀"^printind_name ind1 
  | EXEXISTS ind1 ->"∃"^printind_name ind1 
let rec printiopl il = match il with []->""|i::tl->printind_modifs i^","^printiopl tl 
let printi i = printind_name (ind_name i)^" "^printiopl (ind_modifs_list i) 
let printcons v = match cons v with AC -> if sign v then "=" else "≠" | BC -> if sign v then "≥" else "<" 
let rec isppp il = match il with [] -> [] | i::tl -> match i with Ind (P _,_) -> [i] | _ -> isppp tl
let rec isttt il = match il with [] -> [] | i::tl -> match i with Ind (T _,_) -> [i] | _ -> isttt tl
let rec printind_name_list il = match il with []->""|i::tl->printind_name (ind_name i) 
let rec printiopl_list il = match il with []->""|i::tl->printiopl (ind_modifs_list i)
let printglobal_event e = 
  let right = hd (match isppp (index_list e) with [] -> isttt (index_list e) | _ -> isppp (index_list e)) in
  let left = subi right (index_list e) in
  printind_name_list left^printcons e^printind_name (ind_name right)^printiopl_list (index_list e)
let printevent_var v = match name v with 
  | X -> "   X"^printglobal_event v
  | B i -> raise (Generator_failure ("printevent_var: auxiliary B"^string_of_int i^" reached the printer — no Global_devent turned it back into a solver literal, so there is no rule to print (W1-T10)"))
  | T -> raise (Generator_failure "printevent_var: the placeholder reified name T reached the printer; fre/fnre should have intercepted it as Lit T / Lit F (W1-T10)") 
  | I -> "   I"^printcons v^printi (hd (index_list v)) 
  | V -> "   V"^printcons v^printi (hd (index_list v)) 
  | N -> "   N"^printcons v^printi (hd (index_list v)) 
  | O -> "   X"^printglobal_event v
let rec printe el = match el with []->"" | e::tl -> match e with  
  |F|IM|FE|R -> "? "^printe tl 
  | T -> printe tl 
  | Var v -> printevent_var v^printe tl 
(*Print explanation in LaTex*) 
let printsymtex s = match s with PLUS-> "+"|MINUS->"-"|IN->" \\in "|NEQ->" \\neq "|LEQ->" \\leq "|GEQ->" \\geq "|EQ->"=" 
let printioptex op= match op with 
  | Set (ind1,sym1,set1) ->printind_name ind1^printsymtex sym1^printind_set set1 
  | Rel (ind1,sym1,ind2) ->printind_name ind1^printsymtex sym1^printind_name ind2 
  | Addint (ind1,ind2,sym1,int) ->printind_name ind1^"="^printind_name ind2^printsymtex sym1^string_of_int int 
  | Addcst (ind1,ind2,sym1,cst1,ind3) ->printind_name ind1^"="^printind_name ind2^printsymtex sym1^printind_const cst1^"_{"^printind_name ind3^"}" 
  | EXFORALL ind1 ->"\\forall "^printind_name ind1 
  | EXEXISTS ind1 ->"\\exists "^printind_name ind1 
let rec printiopltex il = match il with []->""|i::[]->printioptex i|i::tl->printioptex i^",~"^printiopltex tl 
let printitex i = printind_name (ind_name i)^(if ind_modifs_list i!=[]then ",~" else "")^printiopltex (ind_modifs_list i) 
let printconstex v = match cons v with AC -> if sign v then "=" else " \\neq " | BC -> if sign v then " \\geq " else "<"
let rec printiopl_listtex il = match il with []->""|i::tl->(if ind_modifs_list i!=[]then ",~" else "")^printiopltex (ind_modifs_list i)^printiopl_listtex tl
let printglobal_eventtex e = 
  let right = hd (isppp (index_list e)@isttt (index_list e)) in
  let left = subi right (index_list e) in
  "_{"^printind_name_list left^"}"^printconstex e^printind_name (ind_name right)^""^printiopl_listtex (index_list e)
let printvartex v = match name v with 
  | X -> "X"^printglobal_eventtex v
  | B i -> raise (Generator_failure ("printvartex: auxiliary B"^string_of_int i^" reached the printer — no Global_devent turned it back into a solver literal, so there is no rule to print (W1-T10)"))
  | T -> raise (Generator_failure "printvartex: the placeholder reified name T reached the printer; fre/fnre should have intercepted it as Lit T / Lit F (W1-T10)") 
  | I -> "I"^printconstex v^printitex (hd (index_list v)) 
  | V -> "V"^printconstex v^printitex (hd (index_list v)) 
  | N -> "N"^printconstex v^printitex (hd (index_list v)) 
  | O -> "O"^printglobal_eventtex v 
let rec printetex el = match el with []->"" | e::tl -> match e with  
  |F|IM|FE|R -> "? "^printetex tl 
  | T -> printetex tl
  | Var v ->printvartex v^(match tl with []->""|v2::_->match v2 with Var _ -> "~~~~"|_->"")^printetex tl
(*Output fraction in tex file*) 
open Printf 
let rec printfraqtex el x fic = match el with  
  | [] -> () 
  | e::tl -> fprintf fic "%s" ("$$\\frac{"^e^"}{"^printvartex x^"}$$ ");printfraqtex tl x fic 
(*==========================================================================
  W1-T3 — make failure loud.

  `removeimp` used to drop every branch containing F, IM, FE or R, all four of
  which print as "?". So "no explanation exists" and "the generator failed"
  were the same observable: silence. They are not the same thing:

    F   the constraint carrying the branch is NOT reified, so "this constraint
        is false" is not a fact anything can explain. The branch is genuinely
        unsatisfiable; dropping it is correct. It is now COUNTED and REPORTED.
    R   the AND/OR traversal met a cycle and cut the branch. Cutting keeps
        termination but loses a candidate explanation, so it is a WARNING.
    IM  the event occurs in no further constraint: a dead end.
    FE  a rule schema was applied to a constraint shape it does not handle.

  IM and FE mean the generator could not do its job, so they now RAISE instead
  of vanishing. Measured 2026-09-18 by instrumenting the filter over all 16
  entries: of the 25 dropped branches, ALL 25 are F; IM, FE and R do not occur.
  Raising therefore changes no emitted rule today.

  Two further silences are reported here rather than fixed, because fixing them
  is W1-T4 and W1-T7 and not this task:
    - a surviving branch with no literal in it prints as an EMPTY premise, i.e.
      a rule concluding from nothing (cata/table.tex rule 1);
    - a literal that binds the same index name more than once makes the emitted
      LaTeX ambiguous, so the shipped rule does not determine what it means
      (D-0009).
  ========================================================================*)

type blocker = BNone | BF | BR | BIM | BFE
let rec blocking_leaf l = match l with
  | [] -> BNone
  | c::tl -> (match c with
      | F  -> BF
      | R  -> BR
      | IM -> BIM
      | FE -> BFE
      | T  -> blocking_leaf tl
      | Var _ -> blocking_leaf tl)
let rec branch_tag l = match l with
  | [] -> []
  | c::tl -> (match c with
      | F -> "F" | R -> "R" | IM -> "IM" | FE -> "FE"
      | T -> "T" | Var _ -> "lit") :: branch_tag tl
let rec has_lit l = match l with
  | [] -> false
  | c::tl -> (match c with Var _ -> true | _ -> has_lit tl)

(*Binders are read off the index structure, not off the LaTeX we just printed,
  so the ambiguity report is independent of the printer (D-0009).*)
let rec binders_modifs ml = match ml with
  | [] -> []
  | m::tl -> (match m with
      | EXFORALL i -> printind_name i :: binders_modifs tl
      | EXEXISTS i -> printind_name i :: binders_modifs tl
      | Set _ | Rel _ | Addint _ | Addcst _ -> binders_modifs tl)
let rec binders_indexes il = match il with
  | [] -> []
  | i::tl -> binders_modifs (ind_modifs_list i) @ binders_indexes tl
let rec countocc x l = match l with [] -> 0 | y::tl -> (if x = y then 1 else 0) + countocc x tl
let rec repeated l = match l with
  | [] -> []
  | x::tl -> let r = repeated tl in
             if countocc x tl > 0 && not (mem x r) then x::r else r
(*W1-T2 — like binders_indexes, read off the index STRUCTURE, not the LaTeX,
  so the refusal does not depend on the printer it protects.*)
let rec undef_modifs ml = match ml with
  | [] -> []
  | m::tl -> (match m with
      | Set (_,_,d) -> (if ind_set_defined d then [] else [op_set d]) @ undef_modifs tl
      | Rel _ | Addint _ | Addcst _ | EXFORALL _ | EXEXISTS _ -> undef_modifs tl)
let rec undef_indexes il = match il with
  | [] -> []
  | i::tl -> undef_modifs (ind_modifs_list i) @ undef_indexes tl
let rec branch_undef l = match l with
  | [] -> []
  | c::tl -> (match c with
      | Var v -> undef_indexes (index_list v) @ branch_undef tl
      | _ -> branch_undef tl)
let undef_seen : string list ref = ref []

let rec branch_ambig l = match l with
  | [] -> []
  | c::tl -> (match c with
      | Var v -> repeated (binders_indexes (index_list v)) @ branch_ambig tl
      | _ -> branch_ambig tl)

(*Replaces removeimp. Returns the surviving branches and a census:
  (kept, duplicate, dropped-F, cut-R, empty-premise, ambiguous-binder,
   refused-undefined-index-set).*)
let rec filter_branches where ll = match ll with
  | [] -> ([], (0,0,0,0,0,0,0))
  | l::tl ->
    let (kept,(nk,nd,nf,nr,nemp,nam,nu)) = filter_branches where tl in
    (match blocking_leaf l with
     | BFE -> raise (Generator_failure (where^" — a rule schema was applied to a constraint shape it does not handle (FE); branch ["^String.concat "+" (branch_tag l)^"]"))
     | BIM -> raise (Generator_failure (where^" — dead-end event: no constraint in the decomposition explains it (IM); branch ["^String.concat "+" (branch_tag l)^"]"))
     | BR  -> (kept,(nk,nd,nf,nr+1,nemp,nam,nu))
     | BF  -> (kept,(nk,nd,nf+1,nr,nemp,nam,nu))
     | BNone ->
       (*W1-T2: refuse before anything can print an undefined set*)
       match removesame (branch_undef l) with
       | _::_ as us -> undef_seen := !undef_seen @ us;
                       (kept,(nk,nd,nf,nr,nemp,nam,nu+1))
       | [] ->
       if inl l tl then (kept,(nk,nd+1,nf,nr,nemp,nam,nu))
       else (removesame l::kept,
             (nk+1,nd,nf,nr,
              nemp + (if has_lit l then 0 else 1),
              nam  + (match branch_ambig l with [] -> 0 | _ -> 1),
              nu)))

(*Running census, printed at the end of a run. stdout, never stderr: the gate
  in the Makefile fails the build if the generator writes to stderr.*)
let gen_files  = ref 0
let gen_events = ref 0
let gen_rules  = ref 0
let gen_dropF  = ref 0
let gen_dropR  = ref 0
let gen_dup    = ref 0
let gen_norule = ref 0
let gen_empty  = ref 0
let gen_ambig  = ref 0
let gen_undef  = ref 0
let footer : string list ref = ref []
let note s = footer := !footer @ [s]
(*A per-entry caveat, set immediately before the explainall that writes the
  entry and cleared by write_footer. The rest of the footer is measured by the
  generator itself; this carries what a HUMAN measured about the entry, so that
  a .tex known to ship an unsound rule says so in the file rather than only in a
  commit message. Empty for every entry that does not set it, which is why no
  existing golden moves.*)
let caveat : string list ref = ref []

(*Output event explanation LateX rule from a global event and a decomposition*)
let emit_event e dec fic =
  let lbl = printvartex e in
  let cl = ctrs e dec in
  let tree = EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (vars e (decomp_event_list c))) cl)) in
  undef_seen := [];
  let (kept,(nk,nd,nf,nr,nemp,nam,nu)) = filter_branches lbl (an tree) in
  let undefs = removesame !undef_seen in
  let _ = printfraqtex (map (fun l-> printetex l) kept) e fic in
  gen_events := !gen_events + 1;
  gen_rules  := !gen_rules  + nk;
  gen_dropF  := !gen_dropF  + nf;
  gen_dropR  := !gen_dropR  + nr;
  gen_dup    := !gen_dup    + nd;
  gen_empty  := !gen_empty  + nemp;
  gen_ambig  := !gen_ambig  + nam;
  gen_undef  := !gen_undef  + nu;
  printf "  %-30s %d candidate(s) -> %d rule(s); dropped: F %d, cycle %d, duplicate %d, undefined index set %d\n"
    lbl (nk+nd+nf+nr+nu) nk nf nr nd nu;
  note (sprintf "%s : %d candidate(s) -> %d rule(s); dropped F %d, cycle %d, duplicate %d, undefined index set %d"
          lbl (nk+nd+nf+nr+nu) nk nf nr nd nu);
  if nu > 0 then begin
    printf "      REFUSED: %d branch(es) reference an index set the artifact never defines (%s) — W1-T2\n"
      nu (String.concat ", " undefs);
    note (sprintf "  ** REFUSED for %s: %d branch(es) reference undefined index set(s) %s; emitting them would state a rule over a set the artifact never defines (W1-T2) **"
            lbl nu (String.concat ", " undefs))
  end;
  if nk = 0 then begin
    gen_norule := !gen_norule + 1;
    printf "      NO RULE EMITTED — %s\n"
      (if nu > 0
       then "every candidate branch quantifies over an index set this artifact cannot define; refusing is the result (W1-T2)"
       else if nf+nr > 0
       then "every candidate branch was blocked: this is 'no explanation exists', not a silent success"
       else "the decomposition produced no candidate branch at all");
    note (sprintf "  ** NO RULE EMITTED for %s: %d candidate(s), all blocked **" lbl (nf+nr+nu))
  end;
  if nemp > 0 then begin
    printf "      DEFECT: %d emitted rule(s) have an EMPTY PREMISE (conclude from nothing) — W1-T4\n" nemp;
    note (sprintf "  ** DEFECT: %d emitted rule(s) for %s have an EMPTY premise (W1-T4) **" nemp lbl)
  end;
  if nam > 0 then begin
    printf "      DEFECT: %d emitted rule(s) bind an index name twice, so the LaTeX does not determine the rule — D-0009\n" nam;
    note (sprintf "  ** DEFECT: %d emitted rule(s) for %s bind an index name twice; the LaTeX is ambiguous (D-0009) **" nam lbl)
  end;
  if nr > 0 then begin
    printf "      WARNING: %d branch(es) cut by cycle detection; a candidate explanation was lost\n" nr;
    note (sprintf "  ** WARNING: %d branch(es) for %s cut by cycle detection **" nr lbl)
  end

(*The diagnostics are appended to the .tex as LaTeX comments, so the shipped
  artifact itself says what it does not contain. No trailing newline is written,
  which keeps the property the rest of the toolchain relies on.*)
(*The footer deliberately does NOT name its own file: cata/atleastnvalues.tex and
  cata/atmostnvalues.tex are byte-identical although their decompositions differ,
  and that collision is W1-T5's evidence. A filename in the footer would make the
  two files differ for a reason that has nothing to do with the bug.*)
let write_footer fic =
  fprintf fic "\n%%%% generator diagnostics (W1-T3)";
  iter (fun s -> fprintf fic "\n%%%% %s" s) !footer;
  iter (fun s -> fprintf fic "\n%%%% %s" s) !caveat;
  footer := [];
  caveat := []

let explain e dec =
  printf "== exp.tex ==\n";
  print_decomp dec;
  footer := [];
  let fic = open_out "exp.tex" in
  let _ = emit_event e dec fic in
  let _ = write_footer fic in
  close_out fic;
  gen_files := !gen_files + 1
let rec explainallaux el dec fic =
  match el with []->() | e::tl ->
    let _ = emit_event e dec fic in
    let _ = emit_event (n e) dec fic in
    explainallaux tl dec fic
let explainall el dec str =
  printf "== %s ==\n" str;
  print_decomp dec;
  footer := [];
  let fic = open_out str in
  let _ = explainallaux el dec fic in
  let _ = write_footer fic in
  close_out fic;
  gen_files := !gen_files + 1


(*W1-T7 — the decompositions' vocabulary, now VALUES of type ind_op rather
  than closures. Every name below kept its meaning and its spelling, so the
  decomposition table at the bottom of this file is untouched; only what the
  names denote changed, from a function nothing could inspect to a term that
  print_op prints, (=) compares and invert_op inverts.

  The closure builders these used to be defined in terms of (iap/tap/pap,
  i_out/t_out/p_out, iii/ttt/ppp, sum, addint, addcst) moved next to apply_op
  as fam_map/fam_out/fam_find and the *_node builders, and they build exactly
  the same index nodes: this is a re-encoding, not a change of meaning, and the
  golden-file gate is what says so.

  uniqueset, iprim and iprimneqi were dead before this change and are gone. Of
  the vocabulary below, the decompositions use id, oni, ont, onr, ontin, i_out,
  t_out, p_out, foralli, forallt, forallp, iplus, imoin, tplusci, tmoinci,
  tprimin and imap; the rest are kept because they are the format's vocabulary,
  which W2-T1 has to freeze.*)
let oni = OpOn (FI,D 1)
let ont = OpOn (FT,D 2)
let onp = OpOn (FP,D 3)
let onr = OpOn (FR,D 4)
let oniin set = OpOn (FI,set)
let ontin set = OpOn (FT,set)
let onpin set = OpOn (FP,set)
let onrin set = OpOn (FR,set)
let i_out = OpOut FI
let t_out = OpOut FT
let p_out = OpOut FP
let sumiin set = OpSum (FI,set)
let sumtin set = OpSum (FT,set)
let sumpin set = OpSum (FP,set)
let sumi = OpSum (FI,D 1)
let sumt = OpSum (FT,D 2)
let sump = OpSum (FP,D 3)
let foralliin set = OpForall (FI,set)
let foralltin set = OpForall (FT,set)
let forallpin set = OpForall (FP,set)
let pointiin set = OpPoint (FI,set)
let pointtin set = OpPoint (FT,set)
let pointpin set = OpPoint (FP,set)
let pointi = OpPoint (FI,D 1)
let pointt = OpPoint (FT,D 2)
let pointp = OpPoint (FP,D 3)
let foralli = OpForall (FI,D 1)
let forallt = OpForall (FT,D 2)
let forallp = OpForall (FP,D 3)
let iplus int = OpShift (FI,PLUS,int)
let imoin int = OpShift (FI,MINUS,int)
let tplus int = OpShift (FT,PLUS,int)
let tmoin int = OpShift (FT,MINUS,int)
let tplusci c = OpShiftC (FT,PLUS,c,FI)
let tmoinci c = OpShiftC (FT,MINUS,c,FI)
let tprimin d = OpPrim (FT,d)
(*imap composed right to left and OpSeq is applied right to left, so this is a
  change of representation and nothing else. The empty case still fails loudly.*)
let imap l = match l with []->failwith "empty im list" | _ -> OpSeq l

(*Decompositions*) 
let alleq  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), id, i_out)]);
              Decomp (2, rule3, [Decomp_devent (false, (B 1), id, oni); Reified_devent (true, (B 3), id, i_out)]);
              Decomp (4, rule4, [Decomp_devent (true , (B 2), id, id); Decomp_devent (true, (B 3), id, id)])]
let alldiff= [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule5, [Decomp_devent (true , (B 1), id, oni)])]
let cumul  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), tplusci (C 1), tmoinci (C 1)); Decomp_devent (false, (B 1), id, id); Reified_devent (true, (B 2), id, id)]);
              Decomp (3, rule5, [Decomp_devent (true , (B 2), id, oni)])]
let gcc    = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), id, oni)])]
(*W1-T9 defect 3 — `gcc` rules 1-2 were vacuous.
  B2's ASCENDING modification was `imap [i_out;forallp]`, which prepends a
  UNIVERSALLY bound p, so the premise printed as `forall p in [1,n]: O_t >= p`.
  That collapses to O_t >= n, which contradicts the companion premise that the
  other n-1 variables avoid t, and the rule could never fire (VACUOUS, W1-T8).
  The clause B2_{t,p} <=> (#{i : X_i = t} >= p) is quantified over p at the
  CONSTRAINT level, so an explanation built from it is a schema valid for each
  p separately: p is a free parameter, not something the premise quantifies.
  `pointp` emits exactly that — p with its range and no binder.
  MEASURED: both rules go VACUOUS -> SOUND and MINIMAL, so all 4 gcc rules are
  now sound and minimal. Only the ascending op changed, so rules 3-4, which
  reach B2 through the DESCENDING `imap [foralli;p_out]`, are byte-unchanged.*)
let gccn   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule6, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), imap [foralli;p_out], imap [i_out;pointp])]);
              Decomp (3, rule1, [Global_devent (true ,  O   , id, id, BC); Reified_devent (true, (B 2), id, id)])]
let incr   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (false, (B 1), id, id); Decomp_devent (true , (B 1), imoin 1, iplus 1)])]
let decr   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, id); Decomp_devent (false , (B 1), imoin 1, iplus 1)])]
let elem   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule1, [Global_devent (true ,  I   , id, id, AC); Reified_devent (true, (B 2), id, id)]);
              Decomp (3, rule1, [Global_devent (true ,  V   , id, id, AC); Reified_devent (true, (B 3), id, id)]);
              Decomp (4, rule4, [Decomp_devent (false, (B 3), foralli, i_out); Decomp_devent (false, (B 2), forallt, t_out); Decomp_devent (true , (B 1), id, id)]);
              Decomp (4, rule4, [Decomp_devent (true , (B 3), foralli, i_out); Decomp_devent (false, (B 2), forallt, t_out); Decomp_devent (false, (B 1), id, id)])] 
let nvalues= [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (1, rule1, [Global_devent (true ,  N   , id, id, AC); Reified_devent (true, (B 4), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), id, i_out)]);
              Decomp (3, rule7, [Decomp_devent (true , (B 2), id, ont); Reified_devent (true, (B 4), imap [foralli;p_out], imap [i_out;t_out;forallp])])]
let atleastnvalues = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
                      Decomp (1, rule1, [Global_devent (true ,  N   , id, id, BC); Reified_devent (true, (B 4), id, id)]);
                      Decomp (2, rule4, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), foralli, i_out)]);
                      Decomp (3, rule6, [Decomp_devent (true , (B 2), id, ont); Reified_devent (true, (B 4), imap [foralli;p_out], imap [i_out;t_out;forallp])])]
let atmostnvalues  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
                      Decomp (1, rule1, [Global_devent (true ,  N   , id, id, BC); Reified_devent (true, (B 4), id, id)]);
                      Decomp (2, rule4, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), foralli, i_out)]);
                      Decomp (3, rule5, [Decomp_devent (true , (B 2), id, ont); Reified_devent (false, (B 4), imap [foralli;p_out], imap [i_out;t_out;forallp])])]
(*G8, demonstrated. `among(n,x,s)` counts the i with X_i in s. Its value set s
  was `D 4`: a per-decomposition counter the printer could not define, so W1-T2
  refused both of among's candidate branches and cata/among.tex shipped with no
  rule at all. s is not an anonymous set -- it is a parameter of among's own
  signature, exactly as `n` and `m` are -- so `DPar ("s", D 2)` says so and
  prints "t \in s,~s \subseteq [[1,m]]", which the artifact does define.
  NOT fixed here, and still true: among's count variable n has no rule, because
  ctr 3 uses the single-Decomp_devent rule7 shape instead of nvalues' N-channel.
  That is G5 in docs/DECOMP_FORMAT_NOTES.md, a decomposition bug, not a gap.*)
let among  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, ontin (DPar ("s",D 2))); Reified_devent (true, (B 2), id, t_out)]);
              Decomp (3, rule7, [Decomp_devent (true , (B 2), id, oni)])]
let regular= [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, id);Decomp_devent (false, (B 1), imap [imoin 1;tprimin (D 8)], imap [iplus 1;tprimin (D 9)])])]
let roots  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), id, ontin (D 5))]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), id, ontin (D 6))])]
let range  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule6, [Decomp_devent (true , (B 1), id, ontin (D 5))]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), id, ontin (D 6))])]
let table  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), id, imap [i_out])]);
              Decomp (4, rule4, [Decomp_devent (true , (B 2), id, onr)])]

(*==========================================================================
  G1, demonstrated. `at_most(c,x,v)` is `B_i <=> X_i = v` plus `sum_i B_i <= c`
  -- exactly alldifferent's shape (rule1 + rule5, one Decomp_devent, no
  Reified_devent), with alldifferent's implicit threshold of 1 replaced by a
  general c. That is the shape G1 named: `c` lived only in the author's head,
  so at_most(2,...) and at_most(3,...) printed the same LaTeX.

  DCard puts it in the index data. rule5's surviving branch reaches the summed
  family through `apprim`, which builds the sibling index i' from the ascending
  op's set -- so writing that set as "a subset S of [[1,n]] with |S| = c+1"
  makes the emitted premise quantify over S instead of over all of [[1,n]], and
  the threshold prints.

  WHY c+1 AND NOT c. `apprim` appends the PARENT index's own membership to the
  sibling's modifier list (this is why cata/alldifferent.tex ends its premise
  with `i \in [[1,n]]`), so the emitted premise says `i \in S` as well as
  `forall i' in S, i' <> i`. That is not a nuisance here, it is the hinge: with
  i inside S, the c+1 members of S other than i are exactly c witnesses, and
  at_most(c) then forbids X_i = v. Writing |S| = c with i excluded instead makes
  `i \in S` contradict the exclusion and the rule goes vacuous. Hence
  BPar ("c",1) -- and hence ind_bound carries an offset rather than a bare int.

  `t` is pinned to at_most's parameter value v by the seed event xacv below: the
  count of v is bounded, not the count of every value, and a rule schematic in t
  would be unsound for at_most. G3 (no variable-vs-variable comparison) is why
  v has to be a parameter; D-0003 says that is the right reading anyway.

  SOUNDNESS, by hand -- cata/at_most.tex is NOT covered by validator.ml, whose
  in_scope list is hardcoded and which this session does not own. Premise: some
  S subset of [[1,n]] with |S| = c+1 and i in S, and X_{i'} = v for every
  i' in S \ {i}. Those are c indices distinct from i all taking v, so at_most(c)
  leaves no room for X_i = v. Sound. NOT minimal in the droppability sense:
  `i \in S` can be dropped and the rule stays sound, because a premise with
  i not in S is unsatisfiable under the constraint. That redundant conjunct is
  apprim's, not the decomposition's, and removing it would change every other
  entry that reaches a summed family (W1-T13 territory, not G1).
  ========================================================================*)
let atmost = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule5, [Decomp_devent (true , (B 1), id, oniin (DCard ("S",D 1,EQ,BPar ("c",1))))])]

(*==========================================================================
  G8's other half, demonstrated: EXCLUSION. `all_different_except(x,{v})` is
  alldifferent restricted to the values other than v, so its decomposition is
  alldiff's and the only thing that changes is the set the value index ranges
  over -- which is precisely what G8 said could not be written down. DExc says
  it: `[[1,m]] \ {v}`. The emitted rule is alldifferent's with that side
  condition, so it inherits alldifferent's verdict, including the reason it only
  ever fires at n=2 (minimality is premise-droppability, not power; W1-T13).
  ========================================================================*)
let alldiffexc = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
                  Decomp (2, rule5, [Decomp_devent (true , (B 1), id, oni)])]


(*==========================================================================
  G3, TESTED rather than argued (session X-max, 2026-09-22).

  decomps/maximum.md and catalog/maximum.md both said: "Both conjuncts compare
  two decision variables (m and x_i) ... No decomposition can be authored in
  the current encoding -- this is not a derivation gap, it is a missing
  primitive."  THAT CLAIM IS WRONG, and it is wrong because it fixes on ONE
  decomposition of maximum, the direct one:

      forall i: m >= x_i    and    exists i: m = x_i

  which does compare two variables.  But the generator's BC events already ARE
  the order encoding, and under the order encoding maximum is stated entirely
  with variable-against-value literals:

      m >= t   <=>   \/_i (x_i >= t)          (equivalently m < t <=> /\_i x_i < t)

  Every atom here is `variable {>=,<} threshold`, which is exactly what
  Global_event (_,_,_,BC) means.  So the shape is gccn's three-step channel --
  reify the array literals, combine them, channel the combination into a SECOND
  global variable -- with rule4 (disjunction) where gccn uses rule6 (Boolean
  sum >=):

      D1  rule1   X_i >= t  <=>  B1_{i,t}                (BC)
      D2  rule4   B2_t      <=>  \/_{i in [[1,n]]} B1_{i,t}
      D3  rule1   O >= t    <=>  B2_t                    (BC)

  D2 is byte-for-byte nvalues' constraint 2 with a BC B1 instead of an AC one;
  D3 is gccn's constraint 3 with a single value index instead of (t,p).  No new
  constructor, no new schema, no new printer case: `maximum` is authorable with
  the language exactly as it stands, and the "missing primitive" reading is
  refuted by this value existing and generating rules.

  WHAT IS BORROWED, AND WHAT IT COSTS.  `m` is printed as `O`, because var_name
  (line 3) has no constructor meaning "this constraint's own scalar bound"; O is
  gcc's occurrence variable and printvartex routes it down the same
  printglobal_eventtex path as X.  That is gap G2 -- a legibility cost on a
  borrowed letter, already recorded, not a blocker.  A second, smaller G2 cost:
  m carries ONE index (the threshold t), so `left` in printglobal_eventtex is
  empty and the literal prints as `O_{} \geq t` rather than `O \geq t`.  Empty
  braces are a no-op in LaTeX, so the artifact is well-formed; the braces are
  still noise and they are the printer's, not the decomposition's.

  WHAT G3 REALLY BLOCKS, then: not maximum, but the constraints whose var-var
  comparison does NOT factor through a shared threshold.  m >= x_i factors (both
  sides are thresholded independently and the order encoding joins them);
  x_i = y_{p_i}, a variable-valued INDEX, does not.  See the report for the
  sharpened statement.
  ========================================================================*)
let maxi   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), id, i_out)]);
              Decomp (3, rule1, [Global_devent (true ,  O   , id, id, BC); Reified_devent (true, (B 2), id, id)])]

(*global events*) 
let xbc = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [])], BC)
let xac = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [])], AC)
let nbc = Global_event (true, N, [Ind (P 1, [])], BC)
let nac = Global_event (true, N, [Ind (P 1, [])], AC)
let i   = Global_event (true, I, [Ind (I 1, [])], AC)
let v   = Global_event (true, V, [Ind (T 1, [])], AC)
let ngbc= Global_event (true, O, [Ind (T 1, []); Ind (P 1, [])], BC)
let x3ac= Global_event (true, X, [Ind (I 1, []); Ind (T 1, []);Ind (R 1, [])], AC)
(*G1/G8 seeds: the value index carries its own side condition, so the printed
  rule states which values it is about. xacv pins t to at_most's parameter v;
  xacx excludes all_different_except's exempt value v from [[1,m]].*)
let xacv = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [Set (T 1,IN,DPar ("\\{v\\}",D 2))])], AC)
let xacx = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [Set (T 1,IN,DExc (D 2,[EPar "v"]))])], AC)
(*G3 seed: maximum's own bound variable. One index -- the threshold t -- because
  m is a scalar, so this is `O >= t` with no array position. Borrowed letter: G2.*)
let mbc = Global_event (true, O, [Ind (T 1, [])], BC)

let _ = explain xbc incr

let _ = explainall [xbc] alleq "cata/allequal.tex"
let _ = explainall [xac] alldiff "cata/alldifferent.tex"
let _ = explainall [xbc] cumul "cata/cumulative.tex"
let _ = explainall [xac;ngbc] gccn "cata/gcc.tex"
let _ = explainall [xbc] decr "cata/decreasing.tex"
let _ = explainall [xbc] incr "cata/increasing.tex"
let _ = explainall [xac;i;v] elem "cata/element.tex"
let _ = explainall [xac;nac] nvalues "cata/nvalues.tex"
let _ = explainall [xac;nbc] atleastnvalues "cata/atleastnvalues.tex"
let _ = explainall [xac;nbc] atmostnvalues "cata/atmostnvalues.tex"
let _ = caveat := [
  "CAVEAT (G-1, 2026-09-22). These two rules exist again only because G8 landed:";
  "the value set s used to be `D 4`, which W1-T2 refused, so this file shipped with";
  "no rule. G8 made the set printable; it did NOT make the rules right. BOTH RULES";
  "ARE UNSOUND, measured by exhaustive check over all n,m <= 4 and all s: rule 1 has";
  "3374 firing cases and fails in all 3374; rule 2 fires 16832 times and fails in 4462.";
  "The cause is G5, not G8: ctr 3 uses the single-Decomp_devent rule7 shape, so among's";
  "count variable n is channelled nowhere, no rule concludes anything about it, and a";
  "rule over X alone is sound only if it is a tautology -- among restricts X only";
  "JOINTLY with its count. Fixing it means giving among nvalues' N-channel";
  "(docs/DECOMP_FORMAT_NOTES.md G5), which is a decomposition repair, not a gap." ];
    explainall [xac] among "cata/among.tex"
let _ = explainall [xac] regular "cata/regular.tex"
let _ = explainall [xac] roots "cata/roots.tex"
let _ = explainall [xac] range "cata/range.tex"
let _ = explainall [x3ac] table "cata/table.tex"
let _ = caveat := [
  "CAVEAT (G-1, 2026-09-22). New entry, the G1 demonstrator: the premise states the";
  "threshold (|S|=c+1) that at_most's rules could not previously mention.";
  "NOT covered by validator.ml, whose in_scope list is hardcoded. Measured instead by";
  "exhaustive check over all n,m <= 4, all v and all c: SOUND, 4706 firing cases, no";
  "counterexample. NOT minimal: dropping `i in S` leaves it sound (same 4706 cases),";
  "because a premise with i outside S is unsatisfiable under at_most(c). That conjunct";
  "is appended by apprim, not written by the decomposition." ];
    explainall [xacv] atmost "cata/at_most.tex"
let _ = caveat := [
  "CAVEAT (G-1, 2026-09-22). New entry, the G8 exclusion demonstrator: alldifferent's";
  "own decomposition with the value index ranging over [[1,m]] minus the exempt value.";
  "NOT covered by validator.ml. Measured by exhaustive check over all n,m <= 4 and all";
  "v: SOUND for n >= 2 (100 firing cases, no counterexample). At n = 1 the universally";
  "quantified premise is vacuously true and the rule concludes from nothing -- the";
  "SHIPPED alldifferent rule does exactly the same (240 -> 140 firing cases, 30";
  "counterexamples, all of them at n = 1), so this entry inherits alldifferent's";
  "verdict and its weakness, including firing only when the others are already pinned." ];
    explainall [xacx] alldiffexc "cata/alldifferent_except.tex"

let _ = caveat := [
  "CAVEAT (X-max, 2026-09-22). New entry, the G3 counter-example: maximum written";
  "with NO variable-vs-variable atom, by using the order encoding the BC events";
  "already are -- m >= t <=> \\/_i (x_i >= t). decomps/maximum.md's claim that no";
  "decomposition is authorable in this language was WRONG; it held only for the";
  "direct reading (forall i: m >= x_i, exists i: m = x_i).";
  "NOT covered by validator.ml, whose in_scope list is hardcoded (W1-T18). Measured";
  "instead by exhaustive check over ALL assignments for every n,m in {1,2,3,4,5} --";
  "n = 1 INCLUDED, which is where the shipped alldifferent rule fails (W1-T19).";
  "ALL FOUR RULES SOUND, no counterexample: firing counts at n,m <= 4 are";
  "359 / 652 / 1592 / 192 in file order; at n,m <= 5, 4173 / 10488 / 23903 / 2296;";
  "at n = 1 alone 20 / 10 / 20 / 10 firings and 0 failures. ALL FOUR MINIMAL: every";
  "premise, dropped, produces a counterexample. Cross-checked by a store sweep over";
  "all domain stores for n,m in {1,2,3} (277 / 1908 / 4379 / 196 firing stores, 0";
  "counterexamples); the two instruments agree. No rule here binds an index twice,";
  "so there is no quantifier-ambiguity reading to resolve (D-0009).";
  "G2 COST, stated: m is printed as O -- var_name has no constructor for a";
  "constraint's own scalar bound, so gcc's occurrence letter is borrowed -- and it";
  "prints as `O_{} >= t` because m has no array position and printglobal_eventtex";
  "emits the subscript unconditionally. Both are legibility, not soundness." ];
    explainall [xbc;mbc] maxi "cata/maximum.tex"

(*W1-T3 — the run's own census. Nothing here changes a rule; it stops the
  generator from being silent about what it discarded.*)
let _ =
  printf "\n== generator census (W1-T3) ==\n";
  printf "  files %d, events %d, rules emitted %d\n" !gen_files !gen_events !gen_rules;
  printf "  branches dropped: %d F (constraint not reified: legitimate), %d cut by cycle detection, %d duplicate\n"
    !gen_dropF !gen_dropR !gen_dup;
  printf "  events with NO rule at all  : %d\n" !gen_norule;
  printf "  rules with an EMPTY premise : %d   (W1-T4)\n" !gen_empty;
  printf "  rules binding an index twice: %d   (D-0009, W1-T7)\n" !gen_ambig;
  printf "  branches REFUSED, undefined index set: %d   (W1-T2)\n" !gen_undef;
  printf "  IM and FE now raise instead of printing as '?'; neither occurred in this run.\n"
