(*Moulinette by Arthur GONTIER 2020 (explenation genarator from constraint decomposition)*)
open List
type name = X | B | B2 | N | T | V 
(*indice options*)
type ind  = I of int
type set = D of int
type cst = C of int
type sym = PLUS|MINUS|IN|NEQ|LEQ|GEQ|EQ
type iop = | Set of ind*sym*set 
           | Rel of ind*sym*ind
           | Addint of ind*sym*int
           | Addcst of ind*sym*cst*ind
           | EXFORALL of ind
           | EXEXISTS of ind
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
    then EXAND (v,fvl (tl c.cvl) v cv dec c ch)(*forall*)
    else EXAND (v,fnvl (tl c.cvl) v cv dec c ch)(*exists*)
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      if v.s = cv.cs
      then fvr vr v cv dec c ch
      else EXAND (v,[fnvr vr v cv dec c ch]@(fvl cvl v cv dec c ch))(*forall*)
    else failwith "bigwedge pas encore implémentés"

and rule4 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if v.s = cv.cs
    then EXAND (v,fvl (tl c.cvl) v cv dec c ch)(*exists*)
    else EXAND (v,fnvl (tl c.cvl) v cv dec c ch)(*forall*)
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      if v.s = cv.cs
      then EXAND (v,[fvr vr v cv dec c ch]@(fvl cvl v cv dec c ch))(*forall*)
      else fnvr vr v cv dec c ch
    else failwith "bigvee pas encore implémentés"

and rule5 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if cv.cs = vr.cs
    then EXAND (v,fnvl (tl c.cvl) v cv dec c ch)(*forall*)
    else Lit IM
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      failwith "sommes multiples pas encore implémentés"
    else 
      if v.s = cv.cs
      then Lit IM
      else EXAND (v,[fvr vr v cv dec c ch]@(fvl (tl c.cvl) v cv dec c ch))(*forall*)

and rule6 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if cv.cs = vr.cs 
    then EXAND (v,fvl (tl c.cvl) v cv dec c ch)(*forall*)
    else Lit IM
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      failwith "sommes multiples pas encore implémentés"
    else 
      if v.s = cv.cs
      then EXAND (v,[fvr vr v cv dec c ch]@(fnvl (tl c.cvl) v cv dec c ch))(*forall*)
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
      then EXAND (v,[fvr vr v cv dec c ch]@(fnvl (tl c.cvl) v cv dec c ch))(*forall*)
      else EXAND (v,[fvr vr v cv dec c ch]@(fvl (tl c.cvl) v cv dec c ch))(*forall*)

let rec concat l = (*Concaténation d'un EXAND de EXOR*)
  match l with l1::tl -> fold_left (fun l1 l2 -> flatten (map (fun x -> map (fun y -> x@y) l1) l2)) l1 tl

let rec an a = (*Extraction des explications de l'arbre*)
  match a with
    | Lit x -> [[x]]
    | EXOR (x,l) -> map (fun x->flatten (an x)) l
    | EXAND (x,l) -> concat (map an l)

(*Fonctions des modifications d'indices*)
let ij il = [ind (I 2) [];ind (I 0) []]
let ji jl = [ind (I 2) [];ind (I 0) []]
let ci il = let i = hd il in let t = hd(tl il) in
  [i]@[ind t.ind ([Addcst (t.ind,MINUS,C 1,i.ind)]@t.opl)]
let ic il = let i = hd il in let t = hd(tl il) in
  [i]@[ind t.ind ([Addcst (t.ind,PLUS,C 1,i.ind)]@t.opl)]
let cs il = 
  [ind (I 2) ([EXFORALL (I 2);Set (I 2,IN,D 1);Rel (I 2,NEQ,(hd il).ind);Set ((hd il).ind,IN,D 1)]@(hd il).opl)]@(tl il)

(*Décompositions*)
let alleq  = [ctr 1 rule1 [car true B  id id;car true  X  id id];
              ctr 2 rule3 [car true T  id id;car false B  ij id; car true B ij id]]
let alldif = [ctr 1 rule1 [car true B  id id;car true  X  id id];
              ctr 2 rule4 [car true T  id id;car false B  ij id; car true B ij id]]
let cumul  = [ctr 1 rule1 [car true B  id id;car true  X  id id];
              ctr 2 rule3 [car true B2 id id;car false B  id id; car true B ci ic];
              ctr 3 rule5 [car true T  id id;car true  B2 cs id]]
let gcc    = [ctr 1 rule1 [car true B  id id;car true  X  id id];
              ctr 3 rule7 [car true T  id id;car true  B  cs id]]

(*Tests*)
let x = var true B [ind (I 1) [];ind (I 0) []]
let nx = var false B [ind (I 1) [];ind (I 0) []]

let z1 = find x alleq (hd alleq) []
let z2 = find nx alleq (hd alleq) []
let z3 = find x alldif (hd alleq) []
let z4 = find nx alldif (hd alleq) []
let z5 = find x cumul (hd cumul) []
let z6 = find nx cumul (hd cumul) []
let z7 = find x gcc (hd gcc) []
let z8 = find nx gcc (hd gcc) []

let a1 = an z1 
let a2 = an z2 
let a3 = an z3 
let a4 = an z4 
let a5 = an z5 
let a6 = an z6 
let a7 = an z7 
let a8 = an z8 

(*Tests concat*)
let ei = concat [[[1];[2]]; [[3];[4]]; [[5];[6]]]
let eo = ei = [[5;3;1]; [5;3;2]; [5;4;1]; [5;4;2]; [6;3;1]; [6;3;2]; [6;4;1]; [6;4;2]]


(*Sortie : 

val a5 : lit List.t List.t =
  List.(::)
   (List.(::)
     (Var
       {s = true; n = X;
        i = [{ind = I; opl = []}; {ind = T; opl = [Addcst (T, MINUS, C, I)]}]},
     [Var
       {s = true; n = X;
        i =
         [{ind = J;
           opl =
            [EXFORALL J; Set (J, IN, D); Rel (J, NEQ, I); Set (I, IN, D)]};
          {ind = T; opl = [Addcst (T, MINUS, C, J)]}]};
      Var
       {s = false; n = X;
        i =
         [{ind = J;
           opl =
            [EXFORALL J; Set (J, IN, D); Rel (J, NEQ, I); Set (I, IN, D)]};
          {ind = T; opl = []}]};
      T]),
   [List.(::) (IM, [])])
*)
