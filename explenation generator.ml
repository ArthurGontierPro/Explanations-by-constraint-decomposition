(*Moulinette by Arthur GONTIER 2020 (explenation generator from constraint decomposition)*) 
open List 
type var_name = X | B of int | T | I | V | N | O
(*index modifications*) 
type ind_name = I of int | T of int | P of int
type ind_set = D of int 
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
    then EXAND (e, fel del e de c dec ch) 
    else EXOR  (e,fnel del e de c dec ch) 
  else  
    let del = match del with _::[] -> del | _ ->  subl de del in
    if sign e = dsign de
    then fre re e de c dec ch 
    else EXAND (e,[fnre re e de c dec ch]@(fel del e de c dec ch)) 

and rule4 e de c dec ch = (*disjunction*) 
  let re = reified_devent (decomp_event_list c) in
  let del = subl re (decomp_event_list c) in
  if dname de = dname re
  then if dsign de = sign e 
    then EXOR  (e, fel del e de c dec ch) 
    else EXAND (e,fnel del e de c dec ch) 
  else  
    let del = match del with _::[] -> del | _ ->  subl de del in
    if sign e = dsign de
    then EXAND (e,[fre re e de c dec ch]@(fnel del e de c dec ch)) 
    else fnre re e de c dec ch 

and rule5 e de c dec ch = (*Bool sum<=c*) 
  let re = reified_devent (decomp_event_list c) in
  let del = subl re (decomp_event_list c) in
  if dname de = dname re
  then if dsign de = sign e 
    then EXAND (e,fnel del e de c dec ch) 
    else EXAND (e,fel del e de c dec ch)
  else  
    let del = match del with _::[] -> del | _ -> failwith "sommes multiples pas encore implémentés" in
    if sign e = dsign de
    then EXAND (e,[fnre re e de c dec ch]@(fnel del e de c dec ch)) 
    else EXAND (e,[ fre re e de c dec ch]@( fel del e de c dec ch)) 
    
 and rule6 e de c dec ch = (*Bool sum=>c*) 
  let re = reified_devent (decomp_event_list c) in
  let del = subl re (decomp_event_list c) in
  if dname de = dname re
  then if dsign de = sign e 
    then EXAND (e, fel del e de c dec ch) 
    else EXAND (e,fnel del e de c dec ch)
  else  
    let del = match del with _::[] -> del | _ -> failwith "sommes multiples pas encore implémentés" in
    if sign e = dsign de
    then EXAND (e,[ fre re e de c dec ch]@(fnel del e de c dec ch)) 
    else EXAND (e,[fnre re e de c dec ch]@( fel del e de c dec ch))  
 
and rule7 e de c dec ch = (*Bool sum=c*) 
  let re = reified_devent (decomp_event_list c) in
  let del = subl re (decomp_event_list c) in
  if dname de = dname re
  then if dsign de = sign e 
    then EXAND (e,(fel del e de c dec ch)@(fnel del e de c dec ch))(*incohérent?*) 
    else EXOR  (e,(fel del e de c dec ch)@(fnel del e de c dec ch))(*incohérent?*) 
  else  
    let del = match del with _::[] -> del | _ -> failwith "sommes multiples pas encore implémentés" in
    if sign e = dsign de
    then EXAND (e,[fre re e de c dec ch]@(fnel del e de c dec ch)) 
    else EXAND (e,[fre re e de c dec ch]@( fel del e de c dec ch)) 

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
  let x = hd (subl re (decomp_event_list c)) in 
  if dsign de = sign e 
  then  fre re e de c dec ch
  else fnre re e de c dec ch

(*Print explanation in string*) 
let rec printprim n = match n with 1 -> "" | _ ->"'"^printprim (n-1)
let printind_name i = match i with I a -> "i_{"^string_of_int a^"}" | T a -> "t_{"^string_of_int a  ^"}" | P a -> "p_{"^string_of_int a  ^"}"
let printind_set s = match s with D a -> "D_{"^string_of_int a ^"}"
let printind_const c = match c with C a -> "c_{"^string_of_int a ^"}"
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
let printevent_var v = match name v with 
  | X -> "   X"^printind_name (ind_name (hd (index_list v)))^(printcons v)^(match index_list v with a::b::_ -> printind_name (ind_name b)^" "^printiopl (ind_modifs_list b)^printiopl (ind_modifs_list a) | _ ->failwith "what?") 
  | B i -> "ERROR B " 
  | T -> "ERROR T " 
  | I -> "   I"^printcons v^printi (hd (index_list v)) 
  | V -> "   V"^printcons v^printi (hd (index_list v)) 
  | N -> "   N"^printcons v^printi (hd (index_list v)) 
  | O -> "   X"^printind_name (ind_name (hd (index_list v)))^(printcons v)^(match index_list v with a::b::_ -> printind_name (ind_name b)^" "^printiopl (ind_modifs_list b)^printiopl (ind_modifs_list a) | _ ->failwith "what?") 
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
  | EXFORALL ind1 ->"~\\forall "^printind_name ind1 
  | EXEXISTS ind1 ->"~\\exists "^printind_name ind1 
let rec printiopltex il = match il with []->""|i::tl->printioptex i^",~"^printiopltex tl 
let printitex i = printind_name (ind_name i)^" "^printiopltex (ind_modifs_list i) 
let printconstex v = match cons v with AC -> if sign v then "=" else " \\neq " | BC -> if sign v then " \\geq " else "<"
let printvartex v = match name v with 
  | X -> "X_{"^printind_name (ind_name (hd (index_list v)))^"}"^(printconstex v)^(match index_list v with a::b::_ -> printind_name (ind_name b)^"~"^printiopltex (ind_modifs_list b)^printiopltex (ind_modifs_list a) | _ ->failwith "what?") 
  | B i -> "ERROR B " 
  | T -> "ERROR T " 
  | I -> "I"^printconstex v^printitex (hd (index_list v)) 
  | V -> "V"^printconstex v^printitex (hd (index_list v)) 
  | N -> "N"^printconstex v^printitex (hd (index_list v)) 
  | O -> "O_{"^printind_name (ind_name (hd (index_list v)))^"}"^(printconstex v)^(match index_list v with a::b::_ -> printind_name (ind_name b)^"~"^printiopltex (ind_modifs_list b)^printiopltex (ind_modifs_list a) | _ ->failwith "what?") 
let rec printetex el = match el with []->"" | e::tl -> match e with  
  |F|IM|FE|R -> "? "^printetex tl 
  | T -> printetex tl
  | Var v -> printvartex v^"~~~"^printetex tl

(*Output fraction in tex file*) 
open Printf 
let rec printfraqtex el x fic = match el with  
  | [] -> () 
  | e::tl -> fprintf fic "%s" ("$\\frac{"^e^"}{"^printvartex x^"}$ ");printfraqtex tl x fic 

(*Output event explanation LateX rule from a global event and a decomposition*) 
let explain e dec = 
  let fic = open_out "exp.tex" in 
  let cl = ctrs e dec in  
  let _ = printfraqtex (map (fun l-> printetex l) (removeimp (an (EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (vars e (decomp_event_list c))) cl)))))) e fic in
  close_out fic 

(*Constructors for index modification functions*) 
let prim i = match i with I a -> I (a+1) | T a -> T (a+1) 
let iprim i = Ind (prim (ind_name i), ind_modifs_list i) 
let addint i sym int = Ind (prim (ind_name i), [Addint (prim (ind_name i), ind_name i, sym, int)]@ind_modifs_list i) 
let addcst i sym cst i2 = Ind (prim (ind_name i), [Addcst (prim (ind_name i), ind_name i, sym, cst, ind_name i2)]@ind_modifs_list i) 
let sum i d = Ind (prim (ind_name i), [EXFORALL (prim (ind_name i)); Set (prim (ind_name i), IN, d); Rel (prim (ind_name i), NEQ, ind_name i); Set (ind_name i, IN, d)]@ind_modifs_list i) 
 
(*Index modification functions*)  
let itmc1i il = 
  match il with i::t::_ -> i::addcst t MINUS (C 1) i::[](*cumul*) 
let itpc1i il = 
  match il with i::t::_ -> i::addcst t PLUS (C 1) i::[](*cumul*) 
let sumid1t il = 
  match il with i::t::_ -> sum i (D 1)::t::[](*sums*) 
let i_out il = 
  match il with i::t::_ -> t::[](*elem*) 
let t_out il = 
  match il with i::t::_ -> i::[]
let tfor_in il = 
  match il with i::_ -> i::Ind ((T 1), [EXFORALL (T 1)])::[] 
let ifor_in il = 
  match il with t::_ -> Ind ((I 1), [EXFORALL (I 1)])::t::[] 
let isumtd1 il = 
  match il with i::t::_ -> i::sum t (D 1)::[](*roots*) 
let isumtd2 il = 
  match il with i::t::_ -> i::sum t (D 2)::[](*roots*) 
let sumid2t il = 
  match il with i::t::_ -> sum i (D 2)::t::[](*alleq2*)  
let id1_in_t il = 
  match il with t::_ -> Ind ((I 1), [Set (I 1,IN,D 1)])::t::[]
let id2_in_t il = 
  match il with t::_ -> Ind ((I 1), [Set (I 1,IN,D 2)])::t::[]
let ip1t il = 
  match il with i::t::_ -> addint i PLUS 1::t::[](*incr*) 
let im1t il = 
  match il with i::t::_ -> addint i MINUS 1::t::[](*incr*) 
let sumtd2 il = 
  match il with t::_ -> sum t (D 2)::[](*nvalue*) 
let sumtd3 il = 
  match il with t::_ -> sum t (D 3)::[](*nvalue*) 
let tt10_in il = 
  match il with t::_ -> t::Ind ((T 10), [Set (T 10,IN,D 3)])::[](*nvalue*) 
let t1_in_t il = 
  match il with t::_ -> Ind ((T 1), [Set (T 1,IN,D 2)])::t::[](*nvalue[EXFORALL (T 1);Set (T 1,IN,D 2)]*) 
let tm1 il = 
  match il with t::_ -> addint t MINUS 1::[](*nvalue*) 
let tp1 il = 
  match il with t::_ -> addint t PLUS 1::[](*nvalue*) 
let sumtd2tprim_out il = 
  match il with t::tt::_ -> sum t (D 2)::[](*nvalue*) 
let i_intp il = (*gcc n variable*) 
  match il with t::p::_ -> Ind ((I 1), [Set (I 1,IN,D 1)])::t::p::[]
let i_outtp il = 
  match il with i::t::p::_ -> t::p::[]
let itp_out il = 
  match il with i::t::p::_ -> i::t::[]
let sumid1tp_in il = 
  match il with i::t::_ -> sum i (D 1)::t::Ind ((P 1), [Set (P 1,IN,D 3)])::[]

(*Decompositions*) 
let alleq  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id,  AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), sumid1t, id); Reified_devent (true, (B 2), t_out, id1_in_t)]);
              Decomp (2, rule3, [Decomp_devent (false, (B 1), sumid2t, id); Reified_devent (true, (B 3), t_out, id2_in_t)]);
              Decomp (3, rule4, [Decomp_devent (true , (B 2), id, id); Decomp_devent (true, (B 3), id, id)])]

let alldiff= [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule5, [Decomp_devent (true , (B 1), sumid1t, id)])]

let cumul  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), itpc1i, itmc1i); Decomp_devent (false, (B 1), id,id); Reified_devent (true, (B 2), id, id)]);
              Decomp (3, rule5, [Decomp_devent (true , (B 2), sumid1t, id)])]

let gcc    = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), sumid1t, id)])]

let gccn   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule6, [Decomp_devent (true , (B 1), sumid1tp_in, itp_out); Reified_devent (true, (B 2), i_intp, i_outtp)]);
              Decomp (3, rule1, [Global_devent (true ,  O   , id, id, BC); Reified_devent (true, (B 2), id, id)])]

let incr   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (false, (B 1), id, id); Decomp_devent (true , (B 1), ip1t, im1t)])]

let elem   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule1, [Global_devent (true ,  I   , id, id, AC); Reified_devent (true, (B 2), id, id)]);
              Decomp (3, rule1, [Global_devent (true ,  V   , id, id, AC); Reified_devent (true, (B 3), id, id)]);
              Decomp (4, rule4, [Decomp_devent (false, (B 3), i_out, ifor_in); Decomp_devent (false, (B 2), t_out, tfor_in); Decomp_devent (true , (B 1), id, id)]);
              Decomp (4, rule4, [Decomp_devent (true , (B 3), i_out, ifor_in); Decomp_devent (false, (B 2), t_out, tfor_in); Decomp_devent (false, (B 1), id, id)])]  

let nvalues= [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (1, rule1, [Global_devent (true ,  N   , id, id, AC); Reified_devent (true, (B 4), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), sumid1t, id); Reified_devent (true, (B 2), i_out, id1_in_t)]);
              Decomp (3, rule7, [Decomp_devent (true , (B 2), sumtd2tprim_out, t1_in_t); Reified_devent (true, (B 4), t_out, tt10_in)])]

let atleastnvalues = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
                      Decomp (1, rule1, [Global_devent (true ,  N   , id, id, BC); Reified_devent (true, (B 4), id, id)]);
                      Decomp (2, rule4, [Decomp_devent (true , (B 1), sumid1t, id); Reified_devent (true, (B 2), i_out, id1_in_t)]);
                      Decomp (3, rule5, [Decomp_devent (true , (B 2), sumtd2tprim_out, t1_in_t); Reified_devent (true, (B 4), t_out, tt10_in)])]

(*global events*) 
let xbc = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [])], BC)
let xac = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [])], AC)
let nbc = Global_event (true, N, [Ind (T 10, [])], BC)
let nac = Global_event (true, N, [Ind (T 10, [])], AC)
let i   = Global_event (true, X, [Ind (I 1, [])], AC)
let v   = Global_event (true, X, [Ind (T 1, [])], AC)
let ngbc= Global_event (true, O, [Ind (T 1, []); Ind (P 1, [])], BC)

let _ = explain ngbc gccn
