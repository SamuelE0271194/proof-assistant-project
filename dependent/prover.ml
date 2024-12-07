open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

let rec to_string exp =
  match exp with
  | Type -> "Type"
  | Var x -> x
  | App (inp, out) -> "(" ^ to_string inp ^ " " ^ to_string out ^ ")"
  | Abs (x, tyX, exp) -> "(fun (" ^ x ^ " : " ^ to_string tyX ^ ") -> " ^ to_string exp ^ ")"
  | Pi (x, tyX, tyB) -> "((" ^ x ^ " : " ^ to_string tyX ^ ") -> " ^ to_string tyB ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S x -> "(S " ^ to_string x ^ ")"
  | Ind (p, z, s, n) -> "ind pred: " ^ to_string p ^ ", base: " ^ to_string z ^ ", if P(n) then P(n+1): " ^ to_string s ^ ", term: " ^ to_string n
  | _ -> "Not implemented yet"

let fresh_constant = ref 0 ;;

let fresh_var _ = 
  fresh_constant := !fresh_constant + 1;
  ("x" ^ string_of_int(!fresh_constant))

let rec subst var ex1 ex2 =
  match ex2 with 
  | Type -> Type
  | Var x -> if x = var then ex1 else (ex2)
  | App (exA, exB) -> App (subst var ex1 exA, subst var ex1 exB)
  (*Note that x does not appear in tyX*)
  | Abs (x, tyX, exp) -> (
    match x with
    | varx when varx = var -> Abs (x, subst x ex1 tyX, exp)
    | _ -> Abs (x, subst var ex1 tyX, subst var ex1 exp)
  )
  | Pi (x, tyX, tyB) -> (
    match x with
    | varx when varx = var -> Pi (x, subst x ex1 tyX, tyB)
    | _ -> Pi (x, subst var ex1 tyX, subst var ex1 tyB)
  )
  | Nat -> Nat
  | Z -> Z
  | S x -> S (subst var ex1 x)
  | Ind (p, z, s, n) -> Ind (subst var ex1 p, subst var ex1 z, subst var ex1 s, subst var ex1 n)
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

let rec normalize ctx exp = 
  (*assumed is well-typed*)
  (*print_endline("normalizing " ^ to_string exp);*)
  match exp with
  | Type -> Type
  | Var x -> ( (*Expect that x is in the context since well typed*)
    match ctx with
    | [] -> Type (*Should never reach here, prob should replace with error*)
    | (var, (_, exp2)) :: l -> (
      match var with
      | y when y = x -> (
        match exp2 with 
        | Some y -> y
        | _ -> Var x
      )
      | _ -> normalize l (Var x)
    )
  )
  | App (exp1, exp2) -> ( (*No need check type*)
    match normalize ctx exp1 with 
    | Abs (x, _, expAbs) -> normalize ctx (subst x exp2 expAbs)
    | Pi (x, _, tyB) -> normalize ctx (subst x exp2 tyB)
    | _ -> App (normalize ctx exp1, normalize ctx exp2) 
  )
  | Abs (x, tyX, expAbs) -> (
    let ctx1 = (x, (tyX, None)) :: ctx in
    Abs (x, normalize ctx tyX, normalize ctx1 expAbs)
  )
  | Pi (x, tyX, tyB) -> (
    let ctx1 = (x, (tyX, None)) :: ctx in
    Pi (x, normalize ctx tyX, normalize ctx1 tyB)
  )
  | Z -> Z
  | S x -> S (normalize ctx x)
  (*s takes n and p(n) -> p(S(n)), note the number comes first*)
  | Ind (p, z, s, n) -> (
    match n with
    | Z -> z
    | S x -> normalize ctx (App (App (s, x), Ind (p, z, s, x)))
    | _ -> Ind (normalize ctx p, normalize ctx z, normalize ctx s, normalize ctx n)
  )
  | _ -> Type (*Not yet implemented stuff*)

let rec alpha exp1 exp2 = 
  match (exp1, exp2) with
  | (Var v1, Var v2) -> v1 = v2
  | (App (e1, e2), App (f1, f2)) -> (alpha e1 e2) && (alpha f1 f2)
  | (Abs (y, tyY, e1), Abs(z, tyZ, e2)) -> (
    let check_var = alpha tyY tyZ in
    let new_var = fresh_var () in
    let sube1 = subst y (Var new_var) e1 in 
    let sube2 = subst z (Var new_var) e2 in 
    check_var && (alpha sube1 sube2)
  )
  | (Pi (y, tyY, ty1), Pi(z, tyZ, ty2)) -> (
    let check_var = alpha tyY tyZ in
    let new_var = fresh_var () in
    let sty1 = subst y (Var new_var) ty1 in
    let sty2 = subst z (Var new_var) ty2 in
    check_var && (alpha sty1 sty2)
  )
  | (Type, Type) -> true
  | (Nat, Nat) -> true
  | (Z, Z) -> true
  | (S x, S y) -> alpha x y
  | (Ind (p1, z1, s1, n1), Ind (p2, z2, s2, n2)) -> 
    (alpha p1 p2) && (alpha z1 z2) && (alpha s1 s2) && (alpha n1 n2)
  | _ -> false (*maybe not yet implemented *)

let conv ctx exp1 exp2 = 
  (*print_endline("comparing");
  print_endline(to_string (normalize ctx exp1));
  print_endline(to_string (normalize ctx exp2));*)
  alpha (normalize ctx exp1) (normalize ctx exp2)

exception Type_error of string

let rec infer ctx exp = 
  (*print_endline ("infering type of " ^ to_string exp);*)
  match exp with
  | Type -> Type
  | Var x -> (
    match ctx with 
    | [] -> raise (Type_error ("Variable <" ^ x ^ "> not in context"))
    | (y, (tyY, _)) :: l ->
      match y with
      | z when z = x -> tyY
      (*I'm comparing variable names x and y, so ok to not use conv here*)
      | _ -> (infer l (Var x))
  )
  | App (exp1, exp2) -> (
    match infer ctx exp1 with 
    (*Abs should not appear since we are dealing with types*)
    | Pi (x, tyX, tyB) -> (
      (*print_endline ("input " ^ x ^ " : " ^ to_string tyX );
      print_endline ("exp2 " ^ " : " ^ to_string (infer ctx exp2) );
      print_endline ("exp2 " ^ " : " ^ to_string (exp2) );*)
      let tyC = infer ctx exp2 in 
      if (conv ctx tyX tyC) then subst x exp2 tyB else
        raise (Type_error "fx, x does not have type matching f input")
    )
    | _ -> raise (Type_error "application of non function")
  )
  | Abs (x, tyX, expAbs) -> (
    let ctx1 = (x, (tyX, None)) :: ctx in
    Pi (x, tyX, infer ctx1 expAbs)
  )
  | Pi (x, tyX, tyB) -> (
    let tyIn = infer ctx tyB in
    let ctx1 = (x, (tyX, None)) :: ctx in
    let tyOut = infer ctx1 tyB in
    if (conv ctx1 tyIn Type) && (conv ctx1 tyOut Type) then Type else
      raise (Type_error "Input or output of Pi is not a Type")
  )
  | Nat -> Type
  | Z -> Nat
  | S x -> if conv ctx (infer ctx x) Nat then Nat else
    raise (Type_error "Successor to non Nat")
  | Ind (p, z, s, n) -> (
    (*first check if n is nat*)
    if (not (conv ctx Nat (infer ctx n))) then raise (Type_error "recursing on non Nat") 
    else
      let tyP = infer ctx p in
      let tyZ = infer ctx z in
      let tyS = infer ctx s in
      (*check if P takes Nat -> Type*)
      let tempN = fresh_var () in
      (*check base case*) 
      if (not (conv ctx (Pi (tempN, Nat, Type)) tyP)) then raise (Type_error "Pred does not have correct type") 
      else if 
        (not (conv ctx (App (p, Z)) tyZ)) then raise (Type_error "Base case does not match p(Z)") 
      else
        (*check suc n -> P(n) -> P(s(n))*)
        let tempN = fresh_var() in
        let tempH = fresh_var() in
        let prfHyp = Pi (tempH, App (p, Var tempN), App (p, S (Var tempN))) in
        if (not (conv ctx (Pi (tempN, Nat, prfHyp)) tyS)) then raise (Type_error "induction term type does not match") 
        else
          (*if not all is good and just return P(n)*)
          App (p, n)
  )
  | _ -> raise (Type_error "Unknown type")

let check ctx exp1 exp2 = (*not infering the type of 2nd exp*)
  if conv ctx (infer ctx exp1) (exp2) then () else (
    raise (Type_error "Types don't match")
  )

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
        let x, sa = split ':' arg in
        let a = of_string sa in
        (*if alpha a Type then print_endline("good") else print_endline("bad");*)
        check !env a Type;
        env := (x,(a,None)) :: !env;
        print_endline (x^" assumed of type "^to_string a)
      | "define" ->
        let x, st = split '=' arg in
        let t = of_string st in
        let a = infer !env t in
        env := (x,(a,Some t)) :: !env;
        print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
        print_endline (string_of_context !env)
      | "type" ->
        let t = of_string arg in
        let a = infer !env t in
        print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
        let t, a = split '=' arg in
        let t = of_string t in
        let a = of_string a in
        check !env t a;
        print_endline "Ok."
      | "eval" ->
        let t = of_string arg in
        let _ = infer !env t in
        print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
    | Type_error err -> print_endline ("Typing error :"^err^".")
    | Parsing.Parse_error -> print_endline ("Parsing error.")
  done;
  print_endline "Bye."
