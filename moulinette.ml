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
      then EXAND (v,[fvr vr v cv dec c ch]@(fnvl cvl v cv dec c ch))(*forall*)
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
let ij il = [ind (I 2) [];ind (T 1) []]
let ji jl = [ind (I 2) [];ind (T 1) []]

let ci il = (*cumul*)
  let i = hd il in 
  let t = hd(tl il) in
  [i]@[ind t.ind ([Addcst (t.ind,MINUS,C 1,i.ind)]@t.opl)]
let ic il = 
  let i = hd il in 
  let t = hd(tl il) in
  [i]@[ind t.ind ([Addcst (t.ind,PLUS,C 1,i.ind)]@t.opl)]

let cs il = (*sums*)
  [ind (I 2) ([EXFORALL (I 2);Set (I 2,IN,D 1);Rel (I 2,NEQ,(hd il).ind);Set ((hd il).ind,IN,D 1)]@(hd il).opl)]@(tl il)

let ii il = [hd il](*elem*)
let vv il = [hd (tl il)]
let iv il = [ind (I 1) [];ind (T 1) []](*on peut faire ça mieux*)

let ir il = (*roots*)
[hd il]@[ind (T 2) ([EXFORALL (T 2);Set (T 2,IN,D 1);Rel (T 2,NEQ,(hd il).ind);Set ((hd il).ind,IN,D 1)]@(hd il).opl)]
let ri il = 
[hd il]@[ind (T 2) ([EXFORALL (T 2);Set (T 2,IN,D 2);Rel (T 2,NEQ,(hd il).ind);Set ((hd il).ind,IN,D 2)]@(hd il).opl)]

(*Décompositions*)
let alleq  = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule3 [car true   T    id id;car false (B 1) ij id;car true (B 1) ij id]]
let alldif = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule4 [car true   T    id id;car false (B 1) ij id;car true (B 1) ij id]]
let cumul  = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule3 [car true  (B 2) id id;car false (B 1) id id;car true (B 1) ci ic];
              ctr 3 rule5 [car true   T    id id;car true  (B 2) cs id]]
let gcc    = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule7 [car true   T    id id;car true  (B 1) cs id]]
let elem   = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule1 [car true  (B 2) id id;car true   I    id id];
              ctr 3 rule1 [car true  (B 3) id id;car true   V    id id];
              ctr 4 rule4 [car true   T    id id;
                           car false (B 3) vv iv;car false (B 2) ii iv; car true (B 1) id id];
              ctr 4 rule4 [car true   T    id id;
                           car true  (B 3) vv iv;car false (B 2) ii iv; car false (B 1) id id]]
let roots  = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule7 [car true   T    id id;car true  (B 1) ir id];
              ctr 2 rule7 [car true   T    id id;car true  (B 1) ri id]]
let range  = [ctr 1 rule1 [car true  (B 1) id id;car true   X    id id];
              ctr 2 rule6 [car true   T    id id;car true  (B 1) cs id];
              ctr 2 rule7 [car true   T    id id;car true  (B 1) ir id]]

(*Tests*)
let x  = var true  (B 1) [ind (I 1) [];ind (T 1) []]
let nx = var false (B 1) [ind (I 1) [];ind (T 1) []]

let alleqx   = an (find x  alleq (hd alleq) [])
let alleqnx  = an (find nx alleq (hd alleq) [])
let alldifx  = an (find x  alldif (hd alleq) [])
let alldifnx = an (find nx alldif (hd alleq) [])
let cumulx   = an (find x  cumul (hd cumul) [])
let cumulnx  = an (find nx cumul (hd cumul) [])
let gccx     = an (find x  gcc (hd gcc) [])
let gccnx    = an (find nx gcc (hd gcc) [])
let elemx    = an (find x  elem (hd elem) [])
let elemnx   = an (find nx elem (hd elem) [])
let elemi    = an (find (var true  (B 2) [ind (I 1) []]) elem (hd (tl elem)) [])
let elemni   = an (find (var false (B 2) [ind (I 1) []]) elem (hd (tl elem)) [])
let elemv    = an (find (var true  (B 3) [ind (T 1) []]) elem (hd (tl (tl elem))) [])
let elemnv   = an (find (var false (B 3) [ind (T 1) []]) elem (hd (tl (tl elem))) [])
let rootsx   = an (find x  roots (hd roots) [])
let rootsnx  = an (find nx roots (hd roots) [])
let rangex   = an (find x  range (hd range) [])
let rangenx  = an (find nx range (hd range) [])
(*Tests concat*)
let ei = concat [[[1];[2]]; [[3];[4]]; [[5];[6]]]
let eo = ei = [[5;3;1]; [5;3;2]; [5;4;1]; [5;4;2]; [6;3;1]; [6;3;2]; [6;4;1]; [6;4;2]]


(*Sortie : 
val cumulx : lit List.t List.t =
  List.(::)
   (List.(::)
     (Var
       {s = true; n = X;
        i =
         [{ind = I 1; opl = []};
          {ind = T 1; opl = [Addcst (T 1, MINUS, C 1, I 1)]}]},
     [Var
       {s = true; n = X;
        i =
         [{ind = I 2;
           opl =
            [EXFORALL (I 2); Set (I 2, IN, D 1); Rel (I 2, NEQ, I 1);
             Set (I 1, IN, D 1)]};
          {ind = T 1; opl = [Addcst (T 1, MINUS, C 1, I 2)]}]};
      Var
       {s = false; n = X;
        i =
         [{ind = I 2;
           opl =
            [EXFORALL (I 2); Set (I 2, IN, D 1); Rel (I 2, NEQ, I 1);
             Set (I 1, IN, D 1)]};
          {ind = T 1; opl = []}]};
      T]),
   [List.(::) (IM, [])])

val elemni : lit List.t List.t =
  List.(::)
   (List.(::)
     (Var
       {s = false; n = X; i = [{ind = I 1; opl = []}; {ind = T 1; opl = []}]},
     [Var {s = true; n = V; i = [{ind = T 1; opl = []}]}; T]),
   [List.(::)
     (Var
       {s = true; n = X; i = [{ind = I 1; opl = []}; {ind = T 1; opl = []}]},
     [Var {s = false; n = V; i = [{ind = T 1; opl = []}]}; T])])
*)
