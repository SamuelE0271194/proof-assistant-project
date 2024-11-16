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

let check_type ctx tm ty =
  match infer_type ctx tm with 
  | x when x = ty -> ()
  | _ -> raise (Type_error)

(** Test codes *)
let () = 
  
 (*Constants that are used in some tests*)
  let a = Var ("A") in
  let b = Var ("B") in
  let c = Var ("C") in
  
  let x = ("x") in
  let f = ("f") in
  let g = ("g") in
  
  (*1.3*) 
  print_endline (string_of_ty (Imp (Imp (a, b), Imp(a, c)))); 
  (*Input : (A → B) → A → C*) 
  (*Expected : ((A ⇒ B) ⇒ (A ⇒ C))*)
  print_endline (string_of_tm (Absm (f, Imp(a, b), Absm(x, a, Appm(Varm f, Varm x)))));
  (*Input : λ(f : A → B).λ(x : A).fx*)
  (*Expected : (λ (f : (A ⇒ B)) -> (λ (x : A) -> (f x)))*)
  
  (*1.4*)
  let gfx = Absm (f, Imp(a, b), Absm(g, Imp(b, c), Absm(x, a, Appm(Varm g, Appm(Varm f, Varm x))))) in 
  let ctx = [] in
  print_endline (string_of_ty (infer_type ctx gfx));
  let tyer1 = Absm (f, a, Varm x) in
  let tyer2 = Absm (f, a, Absm(x, b, Appm(Varm f, Varm x))) in
  let tyer3 = Absm (f, Imp(a, b), Absm(x, b, Appm(Varm f, Varm x))) in
  try 
    let ctx = [] in
    let temp = infer_type ctx tyer1 in
    print_endline ("This should be an error");
  with
  | Type_error -> print_endline("Type Error with tyer1");
  try 
    let ctx = [] in
    let temp = infer_type ctx tyer2 in
    print_endline ("This should be an error");
  with
  | Type_error -> print_endline("Type Error with tyer2");

 try 
    let ctx = [] in
    let temp = (infer_type ctx tyer3) in
    print_endline("no problems");
  with
  | Type_error -> print_endline("Type Error with tyer3");
  (*Expecting gfx to pass and Tyer = Type error to fail*)

  (*1.5*)
  let ctx = [] in
  let checkty = Absm(x, a, Varm x) in
  let temp = check_type ctx checkty (Imp(a, a)) in
  print_endline ("check is type A -> A");
 
  try 
    let ctx = [] in
    let temp = check_type ctx checkty (Imp(b, b)) in 
    print_endline ("check has type B -> B (this should be an error)");
  with
  | Type_error -> print_endline("check is not type B -> B");
 
  try 
    let ctx = [] in
    let temp = check_type ctx (Varm x) a in 
    print_endline ("x has type A (this should be an error)");
  with
  | Type_error -> print_endline("x is not type A");
 











