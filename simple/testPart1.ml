(*Part 1*)
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

(** Test codes *)
(*
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
*)
(*
let () =
  let l = [
    "A => B";
    "A ⇒ B";
    "A /\\ B";
    "A ∧ B";
    "T";
    "A \\/ B";
    "A ∨ B";
    "_";
    "not A";
    "¬ A";
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))
    ) l

let () =
  let l = [
    "t u v";
    "fun (x : A) -> t";
    "λ (x : A) → t";
    "(t , u)";
    "fst(t)";
    "snd(t)";
    "()";
    "case t of x -> u | y -> v";
    "left(t,B)";
    "right(A,t)";
    "absurd(t,A)"
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))
    ) l
*)