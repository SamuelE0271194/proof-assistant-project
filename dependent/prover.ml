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
  | (var, (exp1)) :: l -> 
    var ^ " : " ^ to_string exp1 ^ "\n" ^ string_of_context l
  | (var, (exp1, exp2)) :: l -> 
    var ^ " : " ^ to_string exp1 ^ " = " ^ to_string exp2 ^ "\n" ^ string_of_context l
