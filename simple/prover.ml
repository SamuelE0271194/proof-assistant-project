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
  | Absm of var * ty * tm  (* the middle term is a type not a lambda term*)

let rec string_of_ty typ =
  match typ with
  | Var y -> y
  | Imp (a, b) -> "(" ^ string_of_ty a ^ " ⇒ " ^ string_of_ty b ^ ")"

let rec string_of_tm tmp =
  match tmp with
  | Varm y -> y
  | Appm (a, b) -> "(" ^ string_of_tm a ^ " " ^ string_of_tm b ^ ")" 
  | Absm (a, b, c) -> "(λ (" ^ a ^ " : " ^ string_of_ty b ^ ") -> " ^ string_of_tm c ^ ")"

type context = (var * ty) list

exception Type_error

let rec find ctx t =
  match ctx with
  | [] -> raise (Type_error)
  | (y, typ) :: rest -> 
    match t with
    | x when x = y -> typ
    | _ -> find rest t

let rec infer_type ctx tm =
  match tm with 
  | Varm x -> find ctx x
  | Appm (fn, vari) -> (
    let tfn = infer_type ctx fn in
    let tvar = infer_type ctx vari in
    match tfn with  (*if the type of the function is not imp, its an error*)
    | Imp (a, b) -> (
      match a with
      | a' when a' = tvar -> b
      | _ -> raise (Type_error) 
    )
    | _ -> raise (Type_error)
  )
  | Absm (lam, tlam, fn) -> (
    let ctx_with_var = (lam, tlam) :: ctx in
    Imp (tlam, infer_type ctx_with_var fn)
  )

(** Test codes *)
 
let () = 
  
  (*1.3*) 
  let a = Var ("A") in
  let b = Var ("B") in
  let c = Var ("C") in
  print_endline (string_of_ty (Imp (Imp (a, b), Imp(a, c)))); 
  (*Input : (A → B) → A → C*) 
  (*Expected : ((A ⇒ B) ⇒ (A ⇒ C))*)
  let x = ("x") in
  let f = ("f") in
  print_endline (string_of_tm (Absm (f, Imp(a, b), Absm(x, a, Appm(Varm f, Varm x)))));
  (*Input : λ(f : A → B).λ(x : A).fx*)
  (*Expected : (λ (f : (A ⇒ B)) -> (λ (x : A) -> (f x)))*)
  
  (*1.4*)
  let g = ("g") in
  let gfx = Absm (f, Imp(a, b), Absm(g, Imp(b, c), Absm(x, a, Appm(Varm g, Appm(Varm f, Varm x))))) in 
  let ctx = [] in
  print_endline (string_of_ty (infer_type ctx gfx));
  let tyer1 = Absm (f, a, Varm x) in
  let tyer2 = Absm (f, a, Absm(x, b, Appm(Varm f, Varm x))) in
  let tyer3 = Absm (f, Imp(a, b), Absm(x, b, Appm(Varm f, Varm x))) in
  try 
    let ctx = [] in
    print_endline (string_of_ty (infer_type ctx tyer1));
  with
  | Type_error -> print_endline("Type Error with tyer1");
  try 
    let ctx = [] in
    print_endline (string_of_ty (infer_type ctx tyer2));
  with
  | Type_error -> print_endline("Type Error with tyer2");

 try 
    let ctx = [] in
    print_endline (string_of_ty (infer_type ctx tyer3));
  with
  | Type_error -> print_endline("Type Error with tyer3");
  (*Expecting gfx to pass and Tyer = Type error to fail*)

