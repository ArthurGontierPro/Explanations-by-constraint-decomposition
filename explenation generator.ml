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
type event = | Global_event of bool*var_name*index list*consistancy
             | Decomp_event of bool*var_name*index list
type decomp_event = | Global_devent  of bool*var_name*(index list->index list)*(index list->index list)*consistancy
                    | Decomp_devent  of bool*var_name*(index list->index list)*(index list->index list)
                    | Reified_devent of bool*var_name*(index list->index list)*(index list->index list)
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


let id  x = x(*identity function*) 
let n   e = match e with(*negation of event x*) 
  | Global_event (b,n,l,c)-> Global_event (not b,n,l,c)
  | Decomp_event (b,n,l) -> Decomp_event (not b,n,l)
(*apply index modification functions on an event*) 
let ap  e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(index_propagate de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(index_propagate de) ((index_update dep) (index_list e)))
(*apply index modification functions with negation*) 
let nap e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(index_propagate de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(index_propagate de) ((index_update dep) (index_list e)))
(*apply index modification functions with particularities for sum, bigvee and bigwedge*)
let addexists de = (fun ill -> (match ((index_propagate de) []) with Ind (i,il)::[]->Ind (i,EXEXISTS i::il)|_->failwith "missing index set exist")::ill)
let addforall de = (fun ill -> (match ((index_propagate de) []) with Ind (i,il)::[]->Ind (i,EXFORALL i::il)|_->failwith "missing index set forall")::ill)
let addprim   de = (fun ill -> (match ((index_propagate de) []) with Ind (i,il)::[]->Ind (prim i,EXFORALL (prim i)::Rel (prim i,NEQ,i)::Set (prim i,IN,match il with Set (_,_,d)::[]->d|_->failwith "missing index set" )::il)|_->failwith "missing index set prim")::ill)
let apexists e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addexists de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addexists de) ((index_update dep) (index_list e)))
let apforall e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addforall de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addforall de) ((index_update dep) (index_list e)))
let apprim e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addprim de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addprim de) ((index_update dep) (index_list e)))
let napexists e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addexists de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addexists de) ((index_update dep) (index_list e)))
let napforall e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addforall de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addforall de) ((index_update dep) (index_list e)))
let napprim e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addprim de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addprim de) ((index_update dep) (index_list e)))

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
      | dee::[] -> EXOR  (e,fnre re e de c dec ch::[find (apprim e dee de) c dec ch]) 
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
      | dee::[] -> EXOR  (e,fre re e de c dec ch::[find (napprim e dee de) c dec ch]) 
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
let rec imp l = (*detect impossibles literals*) 
  match l with []->false | c::tl -> match c with |F|IM|FE|R -> true | _ -> imp tl 
let rec removeimp ll = (*remove explenation with impossible literals*) 
  match ll with []->[]|l::tl->if imp l || inl l tl then removeimp tl else [removesame l]@(removeimp tl) 
 
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
(*Output event explanation LateX rule from a global event and a decomposition*) 
let explain e dec = 
  let fic = open_out "exp.tex" in 
  let cl = ctrs e dec in  
  let _ = printfraqtex (map (fun l-> printetex l) (removeimp (an (EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (vars e (decomp_event_list c))) cl)))))) e fic in
  close_out fic 
let rec explainallaux el dec fic =
  match el with []->() | e::tl -> 
    let cl = ctrs e dec in  
    let _ = printfraqtex (map (fun l-> printetex l) (removeimp (an (EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (vars e (decomp_event_list c))) cl)))))) e fic in
    let e = n e in
    let _ = printfraqtex (map (fun l-> printetex l) (removeimp (an (EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (vars e (decomp_event_list c))) cl)))))) e fic in
    explainallaux tl dec fic
let explainall el dec str = 
  let fic = open_out str in 
  let _ = explainallaux el dec fic in
  close_out fic 


(*Constructors for index modification functions*) 
let iprim i = Ind (prim (ind_name i), ind_modifs_list i) 
let iprimneqi i = Ind (prim (ind_name i), Rel (prim (ind_name i),NEQ,ind_name i)::ind_modifs_list i) 
let addint i sym int = Ind (prim (ind_name i), [Addint (prim (ind_name i), ind_name i, sym, int)]@ind_modifs_list i) 
let addcst i sym cst i2 = Ind (prim (ind_name i), [Addcst (prim (ind_name i), ind_name i, sym, cst, ind_name i2)]@ind_modifs_list i) 
let rec uniqueset i set iml = match iml with [] -> [Set (i,IN,set)] | Set (j,_,d)::tl -> if i!=j||set!=d then uniqueset i set tl else [] | _ -> []
let sum i d = Ind (prim (ind_name i), [EXFORALL (prim (ind_name i)); Set (prim (ind_name i),IN,d); Rel (prim (ind_name i), NEQ, ind_name i)]@ind_modifs_list i) 
(*Index finders applyers and removals*)
let rec iii il = match il with [] -> failwith "Index i has left the building" | i::tl -> match i with Ind (I _,_) -> i | _ -> iii tl
let rec ttt il = match il with [] -> failwith "Index t has left the building" | i::tl -> match i with Ind (T _,_) -> i | _ -> ttt tl
let rec ppp il = match il with [] -> failwith "Index p has left the building" | i::tl -> match i with Ind (P _,_) -> i | _ -> ppp tl
let rec iap f il = match il with [] -> [] | i::tl -> match i with Ind (I _,_) -> f i::iap f tl | _ -> i::iap f tl
let rec tap f il = match il with [] -> [] | i::tl -> match i with Ind (T _,_) -> f i::tap f tl | _ -> i::tap f tl
let rec pap f il = match il with [] -> [] | i::tl -> match i with Ind (P _,_) -> f i::pap f tl | _ -> i::pap f tl
let rec i_out il = match il with [] -> [] | i::tl -> match i with Ind (I _,_) -> tl | _ -> i::i_out tl
let rec t_out il = match il with [] -> [] | i::tl -> match i with Ind (T _,_) -> tl | _ -> i::t_out tl
let rec p_out il = match il with [] -> [] | i::tl -> match i with Ind (P _,_) -> tl | _ -> i::p_out tl
let oni il = Ind (I 1,Set (I 1,IN,D 1)::[])::[]
let ont il = Ind (T 1,Set (T 1,IN,D 2)::[])::[]
let onp il = Ind (P 1,Set (P 1,IN,D 3)::[])::[]
let onr il = Ind (R 1,Set (R 1,IN,D 4)::[])::[]
let oniin set = fun il -> Ind (I 1,Set (I 1,IN,set)::[])::[]
let ontin set = fun il -> Ind (T 1,Set (T 1,IN,set)::[])::[]
let onpin set = fun il -> Ind (P 1,Set (P 1,IN,set)::[])::[]
let onrin set = fun il -> Ind (R 1,Set (R 1,IN,set)::[])::[]

(*Index modification functions*)
let sumiin set = iap (function x -> sum x set) 
let sumtin set = tap (function x -> sum x set) 
let sumpin set = pap (function x -> sum x set) 
let sumi = iap (function x -> sum x (D 1)) 
let sumt = tap (function x -> sum x (D 2)) 
let sump = pap (function x -> sum x (D 3)) 
let foralliin set = function il -> Ind (I 1,[EXFORALL (I 1);Set (I 1,IN,set)])::il 
let foralltin set = function il -> Ind (T 1,[EXFORALL (T 1);Set (T 1,IN,set)])::il 
let forallpin set = function il -> Ind (P 1,[EXFORALL (P 1);Set (P 1,IN,set)])::il 
let foralli = function il -> Ind (I 1,[EXFORALL (I 1);Set (I 1,IN,D 1)])::il 
let forallt = function il -> Ind (T 1,[EXFORALL (T 1);Set (T 1,IN,D 2)])::il 
let forallp = function il -> Ind (P 1,[EXFORALL (P 1);Set (P 1,IN,D 3)])::il 
let iplus int = iap (function x -> addint x PLUS int)
let imoin int = iap (function x -> addint x MINUS int)
let tplus int = tap (function x -> addint x PLUS int)
let tmoin int = tap (function x -> addint x MINUS int)
let tplusci c = function il -> tap (function x -> addcst x PLUS c (iii il)) il
let tmoinci c = function il -> tap (function x -> addcst x MINUS c (iii il)) il
let tprimin d = tap (function x -> Ind (prim (ind_name x), [Set (prim (ind_name x),IN,d); Rel (prim (ind_name x), NEQ, ind_name x)]@ind_modifs_list x))
let rec imap l = match l with []->failwith "empty im list" | f::[] -> (fun il -> f il) | f::tl -> (fun il -> f ((imap tl) il))

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
let gccn   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule6, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), imap [foralli;p_out], imap [i_out;forallp])]);
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
