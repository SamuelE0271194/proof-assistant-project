(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | Var of var
  | Imp of ty * ty

(** lambda terms *)
type tm =
  | Varm of var
  | Appm of tm * tm
  | Absm of tm * ty * tm  (* the middle term is a type not a lambda term*)

let rec string_of_ty typ =
  match typ with
  | Var y -> y
  | Imp (a, b) -> "(" ^ string_of_ty a ^ " ⇒ " ^ string_of_ty b ^ ")"

let rec string_of_tm tmp =
  match tmp with
  | Varm y -> y
  | Appm (a, b) -> "(" ^ string_of_tm a ^ " " ^ string_of_tm b ^ ")" 
  | Absm (a, b, c) -> "(λ (" ^ string_of_tm a ^ " : " ^ string_of_ty b ^ ") -> " ^ string_of_tm c ^ ")"

type context = (var * ty) list

exception Type_error



(** Test codes *)

(* 
let () = 
  let a = Var ("A") in
  let b = Var ("B") in
  let c = Var ("C") in
  print_endline (string_of_ty (Imp (Imp (a, b), Imp(a, c)))); 
  (*Input : (A → B) → A → C*) 
  (*Expected : ((A ⇒ B) ⇒ (A ⇒ C))*)
  let x = Varm ("x") in
  let f = Varm ("f") in
  print_endline (string_of_tm (Absm (f, Imp(a, b), Absm(x, a, Appm(f, x)))));
  (*Input : λ(f : A → B).λ(x : A).fx*)
  (*Expected : (λ (f : (A ⇒ B)) -> (λ (x : A) -> (f x)))*)
  *)