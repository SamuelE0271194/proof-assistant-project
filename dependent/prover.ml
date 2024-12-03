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
  Var ("x" ^ string_of_int(!fresh_constant))