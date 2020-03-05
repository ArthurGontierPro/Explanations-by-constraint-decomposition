open List
type name = X | B | B2 | N | T | V 
type ind  = I | J | K | L | T | D |TPDI|TMDI
type var = { s:bool; n:name;i:ind}
type car = {cs:bool;cn:name;fid:ind->ind;fau:ind->ind}
type lit = Var of var | T | F | IM | R | FE
type arb = | Lit of lit
           | EXOR of arb list 
           | EXAND of var * arb list
type ctr = {id:int;r:var->car->ctr->ctr list->var list->arb;cvl:car list}

let var b n il = {s=b;n=n;i=il}
let car b n f fa = {cs=b;cn=n;fid=f;fau=fa}
let ctr id r cvl = {id=id;r=r;cvl=cvl}

let id  x = x
let n   x = if x.s then var false x.n x.i else var true x.n x.i
let ap  v cv cvp = var cv.cs cv.cn (cv.fid (cvp.fau v.i))
let nap v cv cvp = var (not cv.cs) cv.cn (cv.fid (cvp.fau v.i))

let rec invars v cvl = 
  match cvl with [] -> false | cv::tl -> if cv.cn=v.n then true else invars v tl
let rec vars v cvl = 
  match cvl with [] -> [] | cv::tl -> if cv.cn=v.n then cv::vars v tl else vars v tl
let rec ctrs v dec = 
  match dec with [] -> [] | c::tl -> if invars v c.cvl then c::ctrs v tl else ctrs v tl
let rec subl v l = 
  match l with [] -> [] | c::tl -> if (v.cs=c.cs)&&(v.cn=c.cn) then subl v tl else c::subl v tl
let rec subc v l = 
  match l with [] -> [] | c::tl -> if v.id=c.id then subc v tl else c::subc v tl
let rec inl v l = 
  match l with [] -> false | c::tl -> if v=c then true else inl v tl

let rec find v dec prec ch = 
  if inl v ch || inl (n v) ch then Lit (R) else
  let cl = ctrs v dec in
  let cl = subc prec cl in
  EXOR (flatten (map (fun c-> map (fun cv -> c.r v cv c dec ch) (vars v c.cvl)) cl))

and fvr vr v cv dec c ch = 
  if vr.cn = T then Lit (T) else EXAND (v,[find (ap v vr cv) dec c (ch@[v])])
and fnvr vr v cv dec c ch = 
  if vr.cn = T then Lit (F) else EXAND (v,[find (nap v vr cv) dec c (ch@[v])])
and fvl vl v cv dec c ch = 
  map (fun cv2-> find (ap v cv2 cv) dec c (ch@[v])) vl
and fnvl vl v cv dec c ch = 
  map (fun cv2-> find (nap v cv2 cv) dec c (ch@[v])) vl

and rule1 v cv c dec ch =
  let b = hd c.cvl in
  let x = hd (tl c.cvl) in
  if b.cn = v.n 
  then if v.s = cv.cs
    then EXAND (v,[Lit (Var ( ap v x b))])
    else EXAND (v,[Lit (Var (nap v x b))])
  else Lit (FE)

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
    else Lit (IM)
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      failwith "sommes multiples pas encore implémentés"
    else 
      if v.s = cv.cs
      then Lit (IM)
      else EXAND (v,[fvr vr v cv dec c ch]@(fvl (tl c.cvl) v cv dec c ch))(*forall*)

and rule6 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if cv.cs = vr.cs 
    then EXAND (v,fvl (tl c.cvl) v cv dec c ch)(*forall*)
    else Lit (IM)
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      failwith "sommes multiples pas encore implémentés"
    else 
      if v.s = cv.cs
      then EXAND (v,[fvr vr v cv dec c ch]@(fnvl (tl c.cvl) v cv dec c ch))(*forall*)
      else Lit (IM)

and rule7 v cv c dec ch =
  let vr = hd c.cvl in
  if cv.cn=vr.cn then
    if cv.cs = vr.cs 
    then Lit (IM)
    else EXAND (v,(fvl (tl c.cvl) v cv dec c ch)@(fvl (tl c.cvl) v cv dec c ch))(*incohérent?*)
  else 
    let cvl =subl cv (tl c.cvl) in
    if not (cvl=[]) then
      failwith "sommes multiples pas encore implémentés"
    else 
      if v.s = cv.cs
      then EXAND (v,[fvr vr v cv dec c ch]@(fnvl (tl c.cvl) v cv dec c ch))(*forall*)
      else EXAND (v,[fvr vr v cv dec c ch]@( fvl (tl c.cvl) v cv dec c ch))(*forall*)

let rec coherent l = 
  match l with [] -> true | v::tl -> if v=F then false else coherent tl

let rec an a = 
  match a with
    | Lit x -> [[x]]
    | EXOR (l) -> map (fun x->flatten (an x)) l 
    | EXAND (x,l) -> map (fun x->flatten (an x)) l

let ij i = J
let ji j = J
let ic i = TPDI
let ci i = TMDI

(*Décompositions*)
let alleq  = [ctr 1 rule1 [car true B  id id;car true  X  id id];
              ctr 2 rule3 [car true T  id id;car false B  ij id; car true B ij id]]
let alldif = [ctr 1 rule1 [car true B  id id;car true  X  id id];
              ctr 2 rule4 [car true T  id id;car false B  ij id; car true B ij id]]
let cumul  = [ctr 1 rule1 [car true B  id id;car true  X  id id];
              ctr 2 rule3 [car true B2 id id;car false B  id id; car true B ci ic];
              ctr 3 rule5 [car true T  id id;car false B2 ij id]]

(*Tests*)
let x = var true B I
let nx = var false B I

let z1 = find x alleq (hd alleq) []
let z2 = find nx alleq (hd alleq) []
let z3 = find x alldif (hd alleq) []
let z4 = find nx alldif (hd alleq) []
let z5 = find x cumul (hd cumul) []
let z6 = find nx cumul (hd cumul) []

let a1 = an z1 
let a2 = an z2 
let a3 = an z3 
let a4 = an z4 
let a5 = an z5 
let a6 = an z6 

type set = D
type sym = PLUS|MINUS|IN|NEQ|LEQ|GEQ|EQ
type cst = C
type iop = | Set of ind*sym*set
           | Rel of ind*sym*ind
           | Addint of ind*sym*int
           | Addcst of ind*sym*cst*ind*iop list
           | EXFORALL of ind
           | EXEXISTS of ind

let x = (J,[EXFORALL (J);Set (J,IN,D);Rel (I,NEQ,J);Set (I,IN,D)])
let xx = (I,[Addint (I,PLUS,1)])
let xxx = (T,[Addcst (T,PLUS,C,I,[])])
