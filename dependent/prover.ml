(** Variables. *)
type var = string

(** Expressions. *)
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

let rec to_string exp =
  match exp with
  | Type -> "Type"
  | Var x -> x
  | App (a, b) -> "(" ^ to_string a ^ " => " ^ to_string b ^ ")"
  | Abs (a, b, c) -> "(fun (" ^ a ^ " : " ^ to_string b ^ ") -> " ^ to_string c ^ ")"
  | Pi (a, b, c) -> "Pi(" ^ a ^ ", " ^ to_string b ^ ", " ^ to_string c ^ ")"
  | _ -> "Not implemented yet"

let fresh_constant = ref 0 ;;

let fresh_var _ = 
  fresh_constant := !fresh_constant + 1;
  ("x" ^ string_of_int(!fresh_constant))

let rec subst x ex1 ex2 =
  match ex2 with 
  | Type -> Type
  | Var var when var = x -> ex1
  | App (exA, exB) -> App (subst x ex1 exA, subst x ex1 exB)
  | Abs (var, exA, exB) -> (
    match var with
    | y when y = x -> Abs (x, exA, subst x ex1 exB)
    | _ -> 
      match ex2 with
      | Var z when z = var ->
        let new_var = fresh_var () in 
        let new_Var = Var new_var in
        Abs (new_var, exA, subst x ex1 (subst z new_Var ex2))
      | _ -> Abs (var, exA, subst x ex1 exB)
  )
  | Pi (var, exA, exB) -> (
    match var with
    | y when y = x -> Pi (x, exA, exB)
    | _ -> Pi (x, subst x ex1 exA, subst x ex1 exB)
  )
  | _ -> Type (*"not yet implemented"*)

type context = (var * (expr * expr option)) list

let rec string_of_context ctx =
  match ctx with
  | [] -> ""
  | (var, (exp1, exp2)) :: l -> 
    match exp2 with
    | Some x -> 
      var ^ " : " ^ to_string exp1 ^ " = " ^ to_string x ^ "\n" ^ string_of_context l
    | None -> 
      var ^ " : " ^ to_string exp1 ^ "\n" ^ string_of_context l

exception Type_error of string

let rec in_ctx ctx var =
  match ctx with
  | [] -> raise (Type_error ("Not in ctx"))
  | (x, (exp1, exp2)) :: l -> (
    if var = x then match exp2 with
      | Some x -> x
      | None -> exp1
    else in_ctx l var
  )

let rec normalize ctx exp = 
  match exp with 
  | Type -> Type
  | Var x -> in_ctx ctx x
  | App (exA, exB) -> (
    match exA with
    | Abs (y, _, exBbs) -> subst y (normalize ctx exB) (normalize ctx exBbs) (*assumed that its well typed, so don't care about type of y (exAbs)*)
    | _ -> App (normalize ctx exA, normalize ctx exB)
  )
  | Abs (y, exA, exB) -> Abs (y, normalize ctx exA, normalize ctx exB)
  | Pi (y, exA, exB) -> Pi (y, normalize ctx exA, normalize ctx exB)
  | _ -> Type (*Not yet implemented*)

let rec alpha exp1 exp2 =
  match (exp1, exp2) with
  | (Var v1, Var v2) -> v1 = v2
  | (App (e1, e2), App (f1, f2)) -> (alpha e1 e2) && (alpha f1 f2)
  | (Abs (y, e1, e2), Abs(z, f1, f2)) -> (
    let check_var = alpha e1 f1 in
    let f22 = subst z (Var y) f2 in 
    check_var && (alpha e2 f22)
  )
  | (Pi (y, e1, e2), Pi(z, f1, f2)) -> (
    let f12 = subst z (Var y) f2 in 
    let f22 = subst z (Var y) f1 in
    (alpha e1 f12) && (alpha e2 f22)
  )
  | _ -> false (*prob not yet implemented*)

let conv ctx exp1 exp2 =
  alpha (normalize ctx exp1) (normalize ctx exp2)

let rec infer ctx exp =
  match normalize ctx exp with
  | Type -> Type
  | Var x -> in_ctx ctx x (*The type error is thrown from in_ctx*)
  | App (exA, exB) -> App (infer ctx exA, infer ctx exB)
  | Abs (y, exA, exB) -> Pi (y, infer ctx exA, infer ctx exB)
  | Pi (_, _, _) -> Type
  | _ -> raise (Type_error "not yet implemented")

let check ctx exp1 exp2 =
  if conv ctx exp1 exp2 then () else
    raise (Type_error "Term does not match type")
