(*Moulinette by Arthur GONTIER 2020 (explenation genarator from constraint decomposition)*)
open List
type name = X | B of int | T | I | V 
(*indice options*)
type ind  = I of int | T of int
type set = D of int
type cst = C of int
type sym = PLUS|MINUS|IN|NEQ|LEQ|GEQ|EQ
type iop = | Set of ind*sym*set 
           | Rel of ind*sym*ind
           | Addint of ind*sym*int
           | Addcst of ind*sym*cst*ind
           | EXFORALL of ind
           | EXEXISTS of ind
type cons = AC | BC
(*Global indice type*)
type lou = {ind:ind;opl:iop list}
(*variable*)
type var = { s:bool; n:name;i:lou list}
(*variables in ctrs (fid and fau are indices modification functions)*)
type car = {cs:bool;cn:name;fid:lou list->lou list;fau:lou list->lou list}
(*explanation tree*)
type lit = Var of var | T | F | IM | R | FE
type arb = | Lit of lit
           | EXOR of var*arb list 
           | EXAND of var*arb list
(*constraint with id, explanation rule and car list*)
type ctr = {id:int;r:var->car->ctr->ctr list->var list->arb;cvl:car list}

(*fast constructors*)
let var b n il = {s=b;n=n;i=il}
let car b n f fa = {cs=b;cn=n;fid=f;fau=fa}
let ctr id r cvl = {id=id;r=r;cvl=cvl}
let ind i opl = {ind=i;opl=opl}

(*Affichage en chaine de carractère*)
let rec printprim n = match n with 1 -> "" | _ ->"'"^printprim (n-1)
let printind i = match i with I a -> "i"^printprim a | T a -> "t"^printprim a 
let printset s = match s with D a -> "D"^printprim a
let printcst c = match c with C a -> "c"^printprim a
let printsym s = match s with PLUS-> "+"|MINUS->"-"|IN->"∈"|NEQ->"≠"|LEQ->"<="|GEQ->">="|EQ->"="
let printiop op= match op with
  | Set (ind,sym,set) ->printind ind^printsym sym^printset set
  | Rel (ind,sym,ind2) ->printind ind^printsym sym^printind ind2
  | Addint (ind,sym,int) ->printind ind^"="^printind ind^printsym sym^string_of_int int
  | Addcst (ind,sym,cst,ind2) ->printind ind^"="^printind ind^printsym sym^printcst cst^printind ind2
  | EXFORALL ind ->"∀"^printind ind
  | EXEXISTS ind -> "∃"^printind ind
let rec printiopl il = match il with []->""|i::tl->printiop i^","^printiopl tl
let printi i = printind i.ind^" "^printiopl i.opl
let printcons c v = match c with AC -> if v.s then "=" else "≠" | BC -> if v.s then "≥" else "<"
let printvar cons v = match v.n with
  | X -> "   X"^printind (hd v.i).ind^(printcons cons v)^(match v.i with a::b::_ -> printind b.ind^" "^printiopl b.opl^printiopl a.opl | _ ->failwith "what?")
  | B i -> "ERROR B "
  | T -> "ERROR T "
  | I -> "   I"^printcons cons v^printi (hd v.i)
  | V -> "   V"^printcons cons v^printi (hd v.i)
let rec printe el cons = match el with []->"" | e::tl -> match e with 
  |F|IM|FE|R -> "? "^printe tl cons
  | T -> printe tl cons
  | Var v -> printvar cons v^printe tl cons
(*Affichage en code LaTex*)
let printsymtex s = match s with PLUS-> "+"|MINUS->"-"|IN->" \\in "|NEQ->" \\neq "|LEQ->" \\leq "|GEQ->" \\geq "|EQ->"="
let printioptex op= match op with
  | Set (ind,sym,set) ->printind ind^printsymtex sym^printset set
  | Rel (ind,sym,ind2) ->printind ind^printsymtex sym^printind ind2
  | Addint (ind,sym,int) ->printind ind^"="^printind ind^printsymtex sym^string_of_int int
  | Addcst (ind,sym,cst,ind2) ->printind ind^"="^printind ind^printsymtex sym^printcst cst^"_{"^printind ind2^"}"
  | EXFORALL ind ->" \\forall "^printind ind
  | EXEXISTS ind -> " \\exists "^printind ind
let rec printiopltex il = match il with []->""|i::tl->printioptex i^",~"^printiopltex tl
let printitex i = printind i.ind^" "^printiopltex i.opl
let printconstex c v = match c with AC -> if v.s then "=" else " \\neq " | BC -> if v.s then " \\geq " else "<"
let printvartex cons v = match v.n with
  | X -> "X_{"^printind (hd v.i).ind^"}"^(printconstex cons v)^(match v.i with a::b::_ -> printind b.ind^"~"^printiopltex b.opl^printiopltex a.opl | _ ->failwith "what?")
  | B i -> "ERROR B "
  | T -> "ERROR T "
  | I -> "I"^printconstex cons v^printitex (hd v.i)
  | V -> "V"^printconstex cons v^printitex (hd v.i)
let rec printetex el cons = match el with []->"" | e::tl -> match e with 
  |F|IM|FE|R -> "? "^printetex tl cons
  | T -> printetex tl cons
  | Var v -> printvartex cons v^"~~~"^printetex tl cons

let id  x = x(*identity function*)
let n   x = if x.s then var false x.n x.i else var true x.n x.i(*negation of var x*)
(*apply indices function on a variable*)
let ap  v cv cvp = var cv.cs cv.cn (cv.fid (cvp.fau v.i))
(*apply indices functions with negation*)
let nap v cv cvp = var (not cv.cs) cv.cn (cv.fid (cvp.fau v.i))

(*Utilitary functions*)
let rec invars v cvl = (* var v in car list? *)
  match cvl with [] -> false | cv::tl -> if cv.cn=v.n then true else invars v tl
let rec vars v cvl = (* vars list with the same name as v*)
  match cvl with [] -> [] | cv::tl -> if cv.cn=v.n then cv::vars v tl else vars v tl
let rec ctrs v dec = (* constraint list where v is*)
  match dec with [] -> [] | c::tl -> if invars v c.cvl then c::ctrs v tl else ctrs v tl
let rec subl v l = (* var list without variable v*)
  match l with [] -> [] | c::tl -> if (v.cs=c.cs)&&(v.cn=c.cn) then subl v tl else c::subl v tl
let rec subc v l = (* ctr list without constraint v*)
  match l with [] -> [] | c::tl -> if v.id=c.id then subc v tl else c::subc v tl
let rec inl v l = (* v in l? *)
  match l with [] -> false | c::tl -> if v=c then true else inl v tl

(*find and call rules that explain varriable v*)
let rec find v dec prec ch = 
  if inl v ch || inl (n v) ch then Lit R else
  let cl = ctrs v dec in
  let cl = subc prec cl in
  if cl = [] then Lit IM else
  EXOR (v,flatten (map (fun c-> map (fun cv -> c.r v cv c dec ch) (vars v c.cvl)) cl))

and fvr vr v cv dec c ch = (*explication par la variable réifiée*)
  if vr.cn = T then Lit T else EXAND (v,[find (ap v vr cv) dec c (ch@[v])])
and fnvr vr v cv dec c ch = (*explication par la négations de la variable réifiée*)
  if vr.cn = T then Lit F else EXAND (v,[find (nap v vr cv) dec c (ch@[v])])
and fvl vl v cv dec c ch = (*explication par la liste de littéraux positifs*)
  map (fun cv2-> find (ap v cv2 cv) dec c (ch@[v])) vl
and fnvl vl v cv dec c ch = (*explication par la liste de littéraux négatifs*)
  map (fun cv2-> find (nap v cv2 cv) dec c (ch@[v])) vl

(*Explenation rules*)
and rule1 v cv c dec ch =
  let b = hd c.cvl in
  let x = hd (tl c.cvl) in
  if b.cn = v.n 
  then if v.s = cv.cs
    then EXAND (v,[Lit (Var ( ap v x b))])
    else EXAND (v,[Lit (Var (nap v x b))])
  else Lit FE

and rule3 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if v.s = cv.cs
    then EXAND (v,fvl (tl c.cvl) v cv dec c ch)
    else EXOR (v,fnvl (tl c.cvl) v cv dec c ch)
  else 
    let cvl = if not ((tl (tl c.cvl))=[]) then subl cv (tl c.cvl) else c.cvl in
    if v.s = cv.cs
    then fvr vr v cv dec c ch
    else EXAND (v,[fnvr vr v cv dec c ch]@(fvl cvl v cv dec c ch))

and rule4 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if v.s = cv.cs
    then EXOR (v,fvl (tl c.cvl) v cv dec c ch)
    else EXAND (v,fnvl (tl c.cvl) v cv dec c ch)
  else 
    let cvl = if not ((tl (tl c.cvl))=[]) then subl cv (tl c.cvl) else c.cvl in
    if v.s = cv.cs
    then EXAND (v,[fvr vr v cv dec c ch]@(fnvl cvl v cv dec c ch))
    else fnvr vr v cv dec c ch

and rule5 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if cv.cs = vr.cs
    then EXAND (v,fnvl (tl c.cvl) v cv dec c ch)
    else Lit IM
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      failwith "sommes multiples pas encore implémentés"
    else 
      if v.s = cv.cs
      then Lit IM
      else EXAND (v,[fvr vr v cv dec c ch]@(fvl (tl c.cvl) v cv dec c ch))

and rule6 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if cv.cs = vr.cs 
    then EXAND (v,fvl (tl c.cvl) v cv dec c ch)
    else Lit IM
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      failwith "sommes multiples pas encore implémentés"
    else 
      if v.s = cv.cs
      then EXAND (v,[fvr vr v cv dec c ch]@(fnvl (tl c.cvl) v cv dec c ch))
      else Lit IM

and rule7 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if cv.cs = vr.cs 
    then Lit IM
    else EXAND (v,(fvl (tl c.cvl) v cv dec c ch)@(fnvl (tl c.cvl) v cv dec c ch))(*incohérent?*)
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      failwith "sommes multiples pas encore implémentés"
    else 
      if v.s = cv.cs
      then EXAND (v,[fvr vr v cv dec c ch]@(fnvl (tl c.cvl) v cv dec c ch))
      else EXAND (v,[fvr vr v cv dec c ch]@(fvl (tl c.cvl) v cv dec c ch))

let rec imp l = (*detect impossibles literals*)
  match l with []->false | c::tl -> match c with |F|IM|FE|R -> true | _ -> imp tl
let rec removeimp ll = (*remove explenation with impossible literals*)
  match ll with []->[]|l::tl->if imp l then removeimp tl else [l]@(removeimp tl)

let rec concat l = (*Concaténation d'un EXAND de EXOR*)
  match l with []-> [] | l1::[]-> l1 | l1::tl -> fold_left (fun l1 l2 -> flatten (map (fun x -> map (fun y -> x@y) l1) l2)) l1 tl
(*Tests concat*)
let ei = concat [[[1];[2]]; [[3];[4]]; [[5];[6]]]
let eo = ei = [[5;3;1]; [5;3;2]; [5;4;1]; [5;4;2]; [6;3;1]; [6;3;2]; [6;4;1]; [6;4;2]]
let ei = concat [[[1]];[[]]]

let rec an a = (*Extraction des explications de l'arbre*)
  match a with
    | Lit x -> [[x]]
    | EXOR (_,l) -> flatten (map an l)
    | EXAND (_,l) -> concat (map an l)

(*Constructeurs utilitaires de fonctions d'indices*)
let prim i = match i with I a -> I (a+1) | T a -> T (a+1)
let iprim i = ind (prim i.ind) i.opl
let addint i sym int = ind i.ind ([Addint (i.ind,sym,int)]@i.opl)
let addcst i sym cst i2 = ind i.ind ([Addcst (i.ind,sym,cst,i2.ind)]@i.opl)
let sum i d = ind (prim i.ind) ([EXFORALL (prim i.ind);Set (prim i.ind,IN,d);Rel (prim i.ind,NEQ,i.ind);Set (i.ind,IN,d)]@i.opl)

(*Fonctions des modifications d'indices*)
let ij il = match il with i::t::_ -> [iprim i;t]

let ci il = match il with i::t::_ -> [i;addcst t MINUS (C 1) i](*cumul*)
let ic il = match il with i::t::_ -> [i;addcst t PLUS (C 1) i](*cumul*)

let cs il = match il with i::t::_ -> [sum i (D 1);t](*sums*)

let ii il = [hd il](*elem*)
let vv il = [hd (tl il)]
let iv il = [hd il;ind (T 1) [EXFORALL (T 1)]]
let vi il = [ind (I 1) [EXFORALL (I 1)];hd il]

let ir il = match il with i::t::_ -> [i;sum t (D 1)](*roots*)
let ri il = match il with i::t::_ -> [i;sum t (D 2)](*roots*)

let s1 il = match il with i::t::_ -> [sum i (D 1);t](*alleq1*)
let s2 il = match il with i::t::_ -> [sum i (D 2);t](*alleq2*)

let po il = match il with i::t::_ -> [addint i PLUS 1;t](*incr*)
let mo il = match il with i::t::_ -> [addint i MINUS 1;t](*incr*)

(*Décompositions*)
let alleq  = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule3 [car true  (B 2) vv vi;car true  (B 1) s1 id];
              ctr 2 rule3 [car true  (B 3) vv vi;car false (B 1) s2 id];
              ctr 4 rule4 [car true   T    id id;car true  (B 2) id id;car true  (B 3) id id]]
let alldif = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule5 [car true   T    id id;car true  (B 1) cs id]]
let cumul  = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule3 [car true  (B 2) id id;car false (B 1) id id;car true (B 1) ci ic];
              ctr 3 rule5 [car true   T    id id;car true  (B 2) cs id]]
let gcc    = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule7 [car true   T    id id;car true  (B 1) cs id]]
let incr   = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 4 rule4 [car true   T    id id;car false (B 1) id id;car true  (B 1) po mo]]
let elem   = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule1 [car true  (B 2) id id;car true   I    id id];
              ctr 3 rule1 [car true  (B 3) id id;car true   V    id id];
              ctr 4 rule4 [car true   T    id id;
                           car false (B 3) vv vi;car false (B 2) ii iv;car true  (B 1) id id];
              ctr 4 rule4 [car true   T    id id;
                           car true  (B 3) vv vi;car false (B 2) ii iv;car false (B 1) id id]]
let roots  = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule7 [car true   T    id id;car true  (B 1) ir id];
              ctr 2 rule7 [car true   T    id id;car true  (B 1) ri id]]
let range  = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule6 [car true   T    id id;car true  (B 1) s2 id];
              ctr 2 rule7 [car true   T    id id;car true  (B 1) ir id]]

(*Tests*)
let x  = var true  (B 1) [ind (I 1) [];ind (T 1) []]
let i  = var true  (B 2) [ind (I 1) []]
let v  = var true  (B 3) [ind (T 1) []]
let printac l = printe l AC
let printbc l = printe l BC
let alleqx   = map printbc (an (find    x  alleq (hd alleq) []))
let alleqnx  = map printbc (an (find (n x) alleq (hd alleq) []))
let alldifx  = map printac (an (find    x  alldif (hd alldif) []))
let alldifnx = map printac (an (find (n x) alldif (hd alldif) []))
let cumulx   = map printbc (an (find    x  cumul (hd cumul) []))
let cumulnx  = map printbc (an (find (n x) cumul (hd cumul) []))
let gccx     = map printac (an (find    x  gcc (hd gcc) []))
let gccnx    = map printac (an (find (n x) gcc (hd gcc) []))
let incrx    = map printbc (an (find    x  incr (hd incr) []))
let incrnx   = map printbc (an (find (n x) incr (hd incr) []))
let elemx    = map printac (an (find    x  elem (hd elem) []))
let elemnx   = map printac (an (find (n x) elem (hd elem) []))
let elemi    = map printac (an (find    i  elem (hd (tl elem)) []))
let elemni   = map printac (an (find (n i) elem (hd (tl elem)) []))
let elemv    = map printac (an (find    v  elem (hd (tl (tl elem))) []))
let elemnv   = map printac (an (find (n v) elem (hd (tl (tl elem))) []))
let rootsx   = map printac (an (find    x  roots (hd roots) []))
let rootsnx  = map printac (an (find (n x) roots (hd roots) []))
let rangex   = map printac (an (find    x  range (hd range) []))
let rangenx  = map printac (an (find (n x) range (hd range) []))


(*sortie dans un fichier tex*)
open Printf
let rec printfraqtex el x cons fic = match el with 
  | [] -> ()
  | e::tl -> fprintf fic "%s" ("$$\\frac{"^e^"}{"^printvartex cons x^"}$$ ");printfraqtex tl x cons fic
let explain x dec cons = 
  let fic = open_out "exp.tex" in
  let exptex = map (fun l-> printetex l cons ) (removeimp (an (find x dec (hd dec) []))) in
  let a = printfraqtex exptex (var x.s X [ind (I 1) [];ind (T 1) []]) cons fic in
  close_out fic



let a = explain (x) cumul BC
