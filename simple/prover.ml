open Expr
(*
(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | Var of tvar
  | Imp of ty * ty
  | Conj of ty * ty
  | Truth
  | Disj of ty * ty
  | False
  | Unit

(** lambda terms *)
type tm =
  | Varm of var
  | Appm of tm * tm
  | Absm of var * ty * tm  (* the middle term is a type not a lambda term*)
  | Pairm of tm * tm (*Conjunction*)
  | Fstm of tm
  | Sndm of tm
  | Casem of tm * var * tm * var *tm (*Disjunction*)
  | Rcasem of tm * ty
  | Lcasem of tm * ty
  | Trum
  | Falm of tm * ty
  | Unitm
*)

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)
let tm_of_stirng s = Parser.tm Lexer.token (Lexing.from_string s)

let rec string_of_ty typ =
  match typ with
  | Var y -> y
  | Imp (a, b) -> "(" ^ string_of_ty a ^ " ⇒ " ^ string_of_ty b ^ ")"
  | Conj (a, b) -> "(" ^ string_of_ty a ^ " /\\ " ^ string_of_ty b ^ ")"
  | Disj (a, b) -> "(" ^ string_of_ty a ^ " \\/ " ^ string_of_ty b ^ ")"
  | Truth -> "T"
  | False -> "⊥"
  | Unit -> "()"

let rec string_of_tm tmp =
  match tmp with
  | Varm y -> y
  | Appm (a, b) -> "(" ^ string_of_tm a ^ " " ^ string_of_tm b ^ ")" 
  | Absm (a, b, c) -> "(λ (" ^ a ^ " : " ^ string_of_ty b ^ ") -> " ^ string_of_tm c ^ ")"
  | Fstm a -> string_of_tm a
  | Sndm b -> string_of_tm b
  | Pairm (a, b) -> "(" ^ string_of_tm a ^ " /\\ " ^ string_of_tm b ^ ")"
  | Casem (t, x, u, y, v) -> 
    "case(" ^ string_of_tm t ^ ", " ^
     x ^ "->" ^ string_of_tm u ^ ", " ^
      y ^ "->" ^ string_of_tm v ^ ")"
  | Rcasem (x, a) -> "(incl R, ty:" ^ string_of_ty a ^ " term: " ^ string_of_tm x ^ ")"
  | Lcasem (x, a) -> "(incl L, ty:" ^ string_of_ty a ^ " term: " ^ string_of_tm x ^ ")"
  | Trum -> "T"
  | Falm (tm, ty) -> "(" ^ string_of_tm tm ^ " = " ^ string_of_ty ty ^ ")"
  | Unitm -> string_of_ty Unit

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
  | Appm (fn, inp) -> 
    let tfn = infer_type ctx fn in
    (match tfn with 
    | Imp (a, b) -> (
      match check_type ctx inp a with (*just trying to catch an error*)
      | _ -> b
    )
    | _ -> raise (Type_error)
    )
  | Absm (lam, tlam, fn) -> (
    let ctx_with_var = (lam, tlam) :: ctx in
    Imp (tlam, infer_type ctx_with_var fn)
  )
  | Pairm (f, s) -> Conj (infer_type ctx f, infer_type ctx s)
  | Fstm fst -> (
    let tfst = infer_type ctx fst in
    match tfst with 
    | Conj (a, _) -> a
    | _ -> raise (Type_error)
  )
  | Sndm snd -> (
    let tsnd = infer_type ctx snd in
    match tsnd with 
    | Conj (_, b) -> b
    | _ -> raise (Type_error)
  )
  | Trum -> Truth
  | Casem (t, x, u, y, v) -> (
    match infer_type ctx t with
    | Disj (tyl, tyr) -> (
      let ctx1 = (x, tyl) :: ctx in
      let ctx2 = (y, tyr) :: ctx in
      match infer_type ctx1 u with
      | w when w = infer_type ctx2 v -> w
      | _ -> raise (Type_error)
    )
    | _ -> raise (Type_error)
  )
  | Lcasem (tm, ty) ->
    Disj (infer_type ctx tm, ty)
  | Rcasem (tm, ty) -> 
    Disj (ty, infer_type ctx tm)
  | Falm (tm, ty) -> (
    match infer_type ctx tm with
    | False -> ty
    | _ -> raise (Type_error)
  )
  | Unitm -> Unit

and check_type ctx tm ty =
  match tm with 
  | Falm (tm, _) -> check_type ctx tm False
  | _ ->
    match infer_type ctx tm with 
    | x when x = ty -> Unitm
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
    print_endline ("This should be an error " ^ string_of_ty temp);
  with
  | Type_error -> print_endline("Type Error with tyer1");
  try 
    let ctx = [] in
    let temp = infer_type ctx tyer2 in
    print_endline ("This should be an error " ^ string_of_ty temp);
  with
  | Type_error -> print_endline("Type Error with tyer2");

 try 
    let ctx = [] in
    let temp = (infer_type ctx tyer3) in
    print_endline("This should be an error " ^ string_of_ty temp);
  with
  | Type_error -> print_endline("Type Error with tyer3");
  (*Expecting gfx to pass and Tyer = Type error to fail*)

  (*1.5*)
  let ctx = [] in
  let checkty = Absm(x, a, Varm x) in
  let temp = check_type ctx checkty (Imp(a, a)) in
  print_endline ("check is type A -> A" ^ string_of_tm temp);
 
  try 
    let ctx = [] in
    let temp = check_type ctx checkty (Imp(b, b)) in
    print_endline ("check has type B -> B (this should be an error)" ^ string_of_tm temp);
  with
  | Type_error -> print_endline("check is not type B -> B");
 
  try 
    let ctx = [] in
    let temp = check_type ctx (Varm x) a in 
    print_endline ("x has type A (this should be an error)" ^ string_of_tm temp);
  with
  | Type_error -> print_endline("x is not type A"); 

  (*1.8*)
  let and_comm = Absm (x, Conj(a, b), Pairm (Sndm (Varm x), Fstm (Varm x))) in
  print_endline (string_of_ty (infer_type [] and_comm));

  (*1.9*)
  let t_a_a = Absm (f, Imp (Truth, a), Appm(Varm f, Trum)) in
  print_endline (string_of_ty (infer_type [] t_a_a));
 
  (*1.10*)
  let disj_comm = Absm (x, Disj(a, b), 
                    Casem (Varm x, 
                      "u", Rcasem (Varm "u", b),
                      "v", Lcasem (Varm "v", a))) in
  print_endline (string_of_ty (infer_type [] disj_comm));

  (*1.11*)
  let a_and_a_false = Absm (x, Conj(a, Imp(a, False)), 
                      Falm (Appm (Sndm (Varm x), Fstm (Varm x)), b)) in
  print_endline (string_of_ty (infer_type [] a_and_a_false));  
  (*You could get the final bit to say B instead of Anything,
   but you have force the output of Falm -> the term needs a type too*)










