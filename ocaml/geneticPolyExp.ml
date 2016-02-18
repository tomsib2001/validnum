open Basicdefs;;
open Poly;;
open Error;;
open Printing;;
open Reification;;
open Random;;


let mI = makeIntervalle;;
let zero = IntervalQuasiRing.zero;;
let one = IntervalQuasiRing.one;;

type 'a poly =
| Const of 'a
| Var of int
| Add of 'a poly * 'a poly
| Sub of 'a poly * 'a poly
| Mul of 'a poly * 'a poly
| Opp of 'a poly
| Pow of 'a poly * int
| Square of 'a poly

let polyToString (soc : 'a -> string) p =
  let rec aux res = function
    | Const a -> res^(soc a)
    | Var i -> res^"x_{"^(string_of_int i)^"}"
    | Add(p1,p2) -> (aux ((aux (res^"(") p1)^"+") p2)^")"
    | Sub(p1,p2) -> (aux ((aux (res^"(") p1)^"-") p2)^")"
    | Mul(p1,p2) -> aux ((aux res p1)^"*") p2
    | Opp p -> aux (res^"-") p
    | Pow(p,i) -> (aux res p)^(string_of_int i)
    | Square(p) -> (aux res p)^(string_of_int 2)
  in aux "" p;;

let t = (Add(Mul(Var 1,Add(Var 2, Const 3)),Mul(Add(Var 0,Var 1),Var 2)));;
polyToString (string_of_int) t;;
let t1 = Sub(Mul(Var 0,Var 1),Mul(Var 0,Var 2));;
print_string (polyToString (string_of_int) t1);;


type path = bool list

let eval (p : 'a poly) (eval_const : 'a -> intervalle ) (li : intervalle list) =
  let rec aux = function
    | Const a -> eval_const a
    | Var i -> List.nth li i
    | Add(p1,p2) -> iPlus (aux p1) (aux p2)
    | Sub(p1,p2) -> iSub (aux p1) (aux p2)
    | Mul(p1,p2) -> iMult (aux p1) (aux p2)
    | Opp p -> iNeg (aux p)
    | Pow(p,j) -> iPow (aux p) j
    | Square(p) -> iPow (aux p) 2
  in aux p;;

let build_subtrees t =
  let h = Hashtbl.create 100 in
  let hash path subtree = Hashtbl.add h (List.rev path) subtree in
  let rec aux (cur_path : path) x = match x with
    | Const a -> hash (cur_path) x
    | Var i -> hash (cur_path) x
    | Add(p1,p2) -> hash cur_path x; aux (true::cur_path) p1; aux (false::cur_path) p2
    | Mul(p1,p2) -> hash cur_path x; aux (true::cur_path) p1; aux (false::cur_path) p2
    | Sub(p1,p2) -> hash cur_path x; aux (true::cur_path) p1; aux (false::cur_path) p2
    | Opp p -> hash cur_path x; aux (true::cur_path) p
    | Pow(p,j) -> hash cur_path x; aux (true::cur_path) p
    | Square(p) -> hash cur_path x; aux (true::cur_path) p
  in aux [] t; h;;

let get_list h = Hashtbl.fold (fun x y z -> (x,y)::z) h [];;

let get_subtree path h = Hashtbl.find h path;;

let subst path large newsubtree =
  let rec aux cur_tree cur_path = match (cur_tree,cur_path) with
    | (_,[]) -> newsubtree
    | (t,true::l) ->
      (match t with
      | Add(p1,p2) -> Add(aux p1 l,p2)
      | Sub(p1,p2) -> Sub(aux p1 l,p2)
      | Mul(p1,p2) -> Mul(aux p1 l,p2)
      | Opp p -> Opp(aux p l)
      | Pow(p,j) -> Pow(aux p l,j)
      | Square p -> Square (aux p l)
      | _ -> failwith "path should end here")
    | (t,false::l) ->
      (match t with
      | Add(p1,p2) -> Add(p1,aux p2 l)
      | Sub(p1,p2) -> Sub(p1,aux p2 l)
      | Mul(p1,p2) -> Mul(p1,aux p2 l)
      | Opp p -> Opp(aux p l)
      | Pow(p,j) -> Pow(aux p l,j)
      | Square p -> Square (aux p l)
      | _ -> failwith "path should end here")
  in aux large path
;;

(* sanity check *)
let t = (Add(Mul(Var 1,Add(Var 2, Const 3)),Mul(Add(Var 0,Var 1),Var 2)));;
polyToString (string_of_int) t;;
let t1 = Sub(Mul(Var 0,Var 1),Mul(Var 0,Var 2));;
let t2 = Mul(Var 0, Sub(Var 1,Var 2));;
print_string (polyToString (string_of_int) t1);;
let h = build_subtrees t;;
let list_subtrees = get_list h;;
let check_list = (List.map (fun (path,subtree) -> (subst path t subtree)) list_subtrees);;
assert(List.for_all (fun x -> x=t) check_list);;
let subtree = get_subtree [false;true] h;;
subst [false; true] t (Var 17);;
subst [false; false] t (Var 17);;
(* end sanity check *)

let pick_rand l =
  let n = List.length l in
  let index = Random.int n in
  List.nth l index;;

type rule = AddA | AddC | OppD | MulA | MulC  | MulNL | MulNR | R1 | R2 | R3 | R4 | SubIsAdd | OppK ;;

type revRule = Rev of rule;;

let list_rules = [AddA ; AddC ; OppD ; MulA ; MulC; MulNL ; MulNR; R1; R2; R3; R4 ; SubIsAdd; OppK];;

let rules tree =
  let aux res rule =
    match rule with
    | AddA -> (match tree with
      | Add(Add(x,y),z) -> (rule,Add(x,Add(y,z)))::res
      | _ -> res)
    | AddC -> (match tree with
      | Add(x,y) -> (rule,Add(y,x))::res
      | _ -> res)
    | MulA -> (match tree with
      | Mul(Mul(x,y),z) -> (rule,Mul(x,Mul(y,z))) ::res
      | _ -> res)
    | MulC -> (match tree with
      | Mul(x,y) -> (rule,Mul(y,x))::res
      | _ -> res)
    | OppD -> (match tree with
      | Add(Opp x,Opp y) -> (rule,Opp(Add(x,y)))::res
      | _ -> res)
    | MulNL -> (match tree with
      | Mul(Opp x,y) -> (rule,Opp(Mul(x,y)))::res
      | _ -> res)
    | MulNR -> (match tree with
      | Mul(x,Opp y) -> (rule,Opp(Mul(x,y)))::res
      | _ -> res)
    | R1 -> (match tree with
      | Add(Mul(x,y),Mul(z,t)) when x = z -> (rule,Mul(x,Add(y,t)))::res
      | _ -> res)
    | R2 -> (match tree with
      | Add(Mul(x,y),Mul(z,t)) when y=t -> (rule,Mul(Add(x,z),t))::res
      | _ -> res)
    | R3 -> (match tree with
      | Add(Mul(x,y),Mul(t,z)) when x = z -> (rule,Mul(x,Add(y,t)))::res
      | _ -> res)
    | R4 -> (match tree with
      | Add(Mul(x,y),Mul(z,t)) when y=z -> (rule,Mul(Add(x,t),y))::res
      | _ -> res)
    | SubIsAdd -> (match tree with
      | Sub(x,y) -> (rule,Add(x,Opp y))::res
      | _ -> res)
    | OppK -> (match tree with
      | Opp(Opp(x)) -> (rule,x)::res
      | _ -> res)
  in
  let revAux res rule =
    match rule with
    | AddA -> (match tree with
      | Add(x,Add(y,z)) -> (rule,Add(Add(x,y),z))::res
      | _ -> res)
    | AddC -> (match tree with
      | Add(x,y) -> (rule,Add(y,x))::res
      | _ -> res)
    | MulA -> (match tree with
      | Mul(x,Mul(y,z)) -> (rule,Mul(Mul(x,y),z)) ::res
      | _ -> res)
    | MulC -> (match tree with
      | Mul(x,y) -> (rule,Mul(y,x))::res
      | _ -> res)
    | OppD -> (match tree with
      | Opp(Add(x,y)) -> (rule,Add(Opp x,Opp y))::res
      | _ -> res)
    | MulNL -> (match tree with
      | Opp(Mul(x,y)) -> (rule,Mul(Opp x,y))::res
      | _ -> res)
    | MulNR -> (match tree with
      | Opp(Mul(x,y)) -> (rule,Mul(x,Opp y))::res
      | _ -> res)
    | R1 -> (match tree with
      | Mul(x,Add(y,t)) -> (rule,Add(Mul(x,y),Mul(x,t)))::res
      | _ -> res)
    | R2 -> (match tree with
      | Mul(Add(x,z),t) -> (rule,Add(Mul(x,t),Mul(z,t)))::res
      | _ -> res)
    | R3 -> (match tree with
      | Mul(x,Add(y,t)) -> (rule,Add(Mul(x,y),Mul(t,x)))::res
      | _ -> res)
    | R4 -> (match tree with
      | Mul(Add(x,t),y)-> (rule,Add(Mul(x,y),Mul(y,t)))::res
      | _ -> res)
    | SubIsAdd -> (match tree with
      | Add(x,Opp y) -> (rule,Sub(x,y))::res
      | _ -> res)
    | OppK -> res
  in
  List.fold_right (fun x y -> (revAux y x)) list_rules
  (List.fold_right (fun x y -> (aux y x)) list_rules []);;


t;;
rules t;;

let mutation t =
  let h = build_subtrees t in
  let l = get_list h in
  let subtree = pick_rand l in
  let (path,subtree) = subtree in
  let candidateRules = rules subtree in
  if candidateRules <> [] then
  let (rule,newSubTree) = pick_rand candidateRules in
  let newTree = subst path t newSubTree in
  newTree else t;;
  (* (rule,newSubTree,newTree);; *)
(* rule *)

(* t;; *)

(* mutation t;; *)

let iter f n x =
  let rec aux res = function
    | 0 -> res
    | k -> aux (f res) (k-1)
  in aux x n;;

let newTrees = List.map (iter mutation 30) [t1;t1;t1;t1;t1;t1;t1;t1];;

t2;;

List.map (fun x -> eval x (fun i -> thin (float_of_int i)) [(0.,1.);(1.,1.);(1.,1.)]) newTrees;;