(*Moulinette by Arthur GONTIER 2020 (explenation generator from constraint decomposition)*) 
open List 
type var_name = X | B of int | T | I | V | N | O
(*index modifications*) 
type ind_name = I of int | T of int | P of int | R of int
type ind_set = D of int | D2 of ind_name list
type ind_const = C of int 
type ind_symbols = PLUS|MINUS|IN|NEQ|LEQ|GEQ|EQ 
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
let op_set s = match s with D a -> "D"^string_of_int a | D2 _ -> "D(list)"
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

(*Print explanation in string*) 
let rec printprim n = match n with 1 -> "" | _ ->"'"^printprim (n-1)
let printind_name_int a = match a with 1 -> "" | 2 -> "'" | 3 -> "''" | _ -> "_{"^string_of_int a^"}"
let printind_name i = match i with I a -> "i"^printind_name_int a | T a -> "t"^printind_name_int a | P a -> "p"^printind_name_int a | R a -> "r"^printind_name_int a
let printind_set_int a = match a with 1 -> "\\llbracket1,n\\rrbracket" | 2 -> "\\llbracket1,m\\rrbracket" | 3 -> "\\llbracket1,n\\rrbracket" | _ -> "D_{"^string_of_int a ^"}"
let printind_set s = match s with D a -> printind_set_int a | D2 _ -> "setfils" 
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
  | B i -> "ERROR B " 
  | T -> "ERROR T " 
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
  | B i -> "ERROR B " 
  | T -> "ERROR T " 
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
exception Generator_failure of string

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
let rec branch_ambig l = match l with
  | [] -> []
  | c::tl -> (match c with
      | Var v -> repeated (binders_indexes (index_list v)) @ branch_ambig tl
      | _ -> branch_ambig tl)

(*Replaces removeimp. Returns the surviving branches and a census:
  (kept, duplicate, dropped-F, cut-R, empty-premise, ambiguous-binder).*)
let rec filter_branches where ll = match ll with
  | [] -> ([], (0,0,0,0,0,0))
  | l::tl ->
    let (kept,(nk,nd,nf,nr,nemp,nam)) = filter_branches where tl in
    (match blocking_leaf l with
     | BFE -> raise (Generator_failure (where^" — a rule schema was applied to a constraint shape it does not handle (FE); branch ["^String.concat "+" (branch_tag l)^"]"))
     | BIM -> raise (Generator_failure (where^" — dead-end event: no constraint in the decomposition explains it (IM); branch ["^String.concat "+" (branch_tag l)^"]"))
     | BR  -> (kept,(nk,nd,nf,nr+1,nemp,nam))
     | BF  -> (kept,(nk,nd,nf+1,nr,nemp,nam))
     | BNone ->
       if inl l tl then (kept,(nk,nd+1,nf,nr,nemp,nam))
       else (removesame l::kept,
             (nk+1,nd,nf,nr,
              nemp + (if has_lit l then 0 else 1),
              nam  + (match branch_ambig l with [] -> 0 | _ -> 1))))

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
let footer : string list ref = ref []
let note s = footer := !footer @ [s]

(*Output event explanation LateX rule from a global event and a decomposition*)
let emit_event e dec fic =
  let lbl = printvartex e in
  let cl = ctrs e dec in
  let tree = EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (vars e (decomp_event_list c))) cl)) in
  let (kept,(nk,nd,nf,nr,nemp,nam)) = filter_branches lbl (an tree) in
  let _ = printfraqtex (map (fun l-> printetex l) kept) e fic in
  gen_events := !gen_events + 1;
  gen_rules  := !gen_rules  + nk;
  gen_dropF  := !gen_dropF  + nf;
  gen_dropR  := !gen_dropR  + nr;
  gen_dup    := !gen_dup    + nd;
  gen_empty  := !gen_empty  + nemp;
  gen_ambig  := !gen_ambig  + nam;
  printf "  %-30s %d candidate(s) -> %d rule(s); dropped: F %d, cycle %d, duplicate %d\n"
    lbl (nk+nd+nf+nr) nk nf nr nd;
  note (sprintf "%s : %d candidate(s) -> %d rule(s); dropped F %d, cycle %d, duplicate %d"
          lbl (nk+nd+nf+nr) nk nf nr nd);
  if nk = 0 then begin
    gen_norule := !gen_norule + 1;
    printf "      NO RULE EMITTED — %s\n"
      (if nf+nr > 0
       then "every candidate branch was blocked: this is 'no explanation exists', not a silent success"
       else "the decomposition produced no candidate branch at all");
    note (sprintf "  ** NO RULE EMITTED for %s: %d candidate(s), all blocked **" lbl (nf+nr))
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
  footer := []

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
let among  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, ontin (D 4)); Reified_devent (true, (B 2), id, t_out)]);
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


(*global events*) 
let xbc = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [])], BC)
let xac = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [])], AC)
let nbc = Global_event (true, N, [Ind (P 1, [])], BC)
let nac = Global_event (true, N, [Ind (P 1, [])], AC)
let i   = Global_event (true, I, [Ind (I 1, [])], AC)
let v   = Global_event (true, V, [Ind (T 1, [])], AC)
let ngbc= Global_event (true, O, [Ind (T 1, []); Ind (P 1, [])], BC)
let x3ac= Global_event (true, X, [Ind (I 1, []); Ind (T 1, []);Ind (R 1, [])], AC)

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
let _ = explainall [xac] among "cata/among.tex"
let _ = explainall [xac] regular "cata/regular.tex"
let _ = explainall [xac] roots "cata/roots.tex"
let _ = explainall [xac] range "cata/range.tex"
let _ = explainall [x3ac] table "cata/table.tex"

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
  printf "  IM and FE now raise instead of printing as '?'; neither occurred in this run.\n"
