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
  | Eq (e1, e2) -> "(" ^ to_string e1 ^ " = " ^ to_string e2 ^ ")"
  | Refl e -> "Refl " ^ to_string e
  | J (p, r, x, y, e) -> "elim p: " ^ to_string p ^ ", r: " ^ to_string r ^ ", x: " ^ to_string x ^ ", y: " ^ to_string y ^ ", e: " ^ to_string e

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
    let new_var = fresh_var () in
    match x with
    | varx when varx = var -> Abs (new_var, tyX, subst x (Var new_var) exp) (*when x is the var we are subsituting*)
    | _ -> Abs (x, subst var ex1 tyX, subst var ex1 exp)
  )
  | Pi (x, tyX, tyB) -> (
    let new_var = fresh_var () in
    match x with
    | varx when varx = var -> Pi (new_var, tyX, subst x (Var new_var) tyB)
    | _ -> Pi (x, subst var ex1 tyX, subst var ex1 tyB)
  )
  | Nat -> Nat
  | Z -> Z
  | S x -> S (subst var ex1 x)
  | Ind (p, z, s, n) -> Ind (subst var ex1 p, subst var ex1 z, subst var ex1 s, subst var ex1 n)
  | Eq (e1, e2) -> Eq (subst var ex1 e1, subst var ex1 e2)
  | Refl e -> Refl (subst var ex1 e)
  | J (p, r, x, y, e) -> J (subst var ex1 p, subst var ex1 r, subst var ex1 x, subst var ex1 y, subst var ex1 e)

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
    | _ -> 
      App (normalize ctx exp1, normalize ctx exp2) 
  )
  | Abs (x, tyX, expAbs) -> (
    let new_var = fresh_var () in
    let ctx1 = (new_var, (tyX, None)) :: ctx in
    Abs (new_var, normalize ctx tyX, normalize ctx1 (subst x (Var new_var) expAbs))
  )
  | Pi (x, tyX, tyB) -> (
    let new_var = fresh_var () in
    let ctx1 = (new_var, (tyX, None)) :: ctx in
    Pi (new_var, normalize ctx tyX, normalize ctx1 (subst x (Var new_var) tyB))
  )
  | Nat -> Nat
  | Z -> Z
  | S x -> S (normalize ctx x)
  (*s takes n and p(n) -> p(S(n)), note the number comes first*)
  | Ind (p, z, s, n) -> (
    let np = normalize ctx p in
    let nz = normalize ctx z in
    let ns = normalize ctx s in
    let nn = normalize ctx n in
    match nn with
    | Z -> nz
    | S x -> normalize ctx (App (App (ns, x), Ind (np, nz, ns, x)))
    | _ -> Ind (normalize ctx p, normalize ctx z, normalize ctx s, normalize ctx n)
  )
  | Eq (e1, e2) -> Eq (normalize ctx e1, normalize ctx e2)
  | Refl e -> Refl (normalize ctx e)
  | J (p, r, x, y, e) -> (
    let nx = normalize ctx x in
    let ny = normalize ctx y in
    let ne = normalize ctx e in
    match e with 
    | Refl ex when ((ex = nx) && (ex = ny)) -> normalize ctx (App (r, nx))
    | _ -> J (p, r, nx, ny, ne)
  )

let rec alpha exp1 exp2 = 
  match (exp1, exp2) with
  | (Var v1, Var v2) -> if (v1 = v2) then true else (
    print_endline("Var : " ^ to_string exp1);
    print_endline("~~~~~~~~~~~~~");
    print_endline("Var : " ^ to_string exp2);
    print_endline("------------");
    false
  )
  | (App (e1, e2), App (f1, f2)) -> if ((alpha e1 e2) && (alpha f1 f2)) then true else (
    print_endline("Application :" ^ to_string exp1);
    print_endline("~~~~~~~~~~~~~");
    print_endline("Application :" ^ to_string exp2);
    print_endline("------------");
    false
  )

  | (Abs (y, tyY, e1), Abs(z, tyZ, e2)) -> (
    let check_var = alpha tyY tyZ in
    let new_var = fresh_var () in
    let sube1 = subst y (Var new_var) e1 in 
    let sube2 = subst z (Var new_var) e2 in 
    if (check_var && (alpha sube1 sube2)) then true else (
      print_endline("Abstraction :" ^ to_string exp1);
      print_endline("~~~~~~~~~~~~~");
      print_endline("Abstraction :" ^ to_string exp2);
      print_endline("------------");
      false
    )
  )
  | (Pi (y, tyY, ty1), Pi(z, tyZ, ty2)) -> (
    let check_var = alpha tyY tyZ in
    let new_var = fresh_var () in
    let sty1 = subst y (Var new_var) ty1 in
    let sty2 = subst z (Var new_var) ty2 in
    if (check_var && (alpha sty1 sty2)) then true else (
      print_endline("Pi : " ^ to_string exp1);
      print_endline("~~~~~~~~~~~~~");
      print_endline("Pi : " ^ to_string exp2);
      print_endline("------------");
      false
    )
  )
  | (Type, Type) -> true
  | (Nat, Nat) -> true
  | (Z, Z) -> true
  | (S x, S y) -> alpha x y
  | (Ind (p1, z1, s1, n1), Ind (p2, z2, s2, n2)) -> 
    (alpha p1 p2) && (alpha z1 z2) && (alpha s1 s2) && (alpha n1 n2)
  | (Eq (e1, e2), Eq(f1, f2)) -> (alpha e1 f1) && (alpha e2 f2)
  | (Refl e1, Refl e2) -> alpha e1 e2
  | (J (p1, r1, x1, y1, e1), J (p2, r2, x2, y2, e2)) -> (alpha p1 p2) && 
                                                        (alpha r1 r2) &&
                                                        (alpha x1 x2) &&
                                                        (alpha y1 y2) &&
                                                        (alpha e1 e2) 
  | _ -> 
    print_endline("Not matching types"); (*maybe not yet implemented *)
    print_endline("!!!!!!!");
    print_endline("exp1 : " ^ to_string exp1);
    print_endline("!!!!!!!");
    print_endline("exp2 : " ^ to_string exp2);
    print_endline("!!!!!!!");
    false

let conv ctx exp1 exp2 = 
  (*print_endline("comparing");
  print_endline("exp1 : " ^ to_string exp1) ;
  print_endline("exp2 : " ^ to_string exp2);
  print_endline("nexp1 : " ^ to_string (normalize ctx exp1));
  print_endline("nexp2 : " ^ to_string (normalize ctx exp2));
  print_endline("------------");*)
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
      if (conv ctx tyX tyC) then (normalize ctx (subst x exp2 tyB)) else
        raise (Type_error "fx, x does not have type matching f input")
    )
    | _ -> 
      print_endline ("exp1 " ^ " : " ^ to_string (exp1) );
      print_endline ("exp2 " ^ " : " ^ to_string (infer ctx exp2) );
      raise (Type_error "application of non function")
  )
  | Abs (x, tyX, expAbs) -> (
    let new_var = fresh_var () in
    let ctx1 = (new_var, (tyX, None)) :: ctx in
    Pi (new_var, tyX, infer ctx1 (subst x (Var new_var) expAbs))
  )
  | Pi (x, tyX, tyB) -> (
    let new_var = fresh_var () in
    let tyIn = infer ctx tyX in
    let ctx1 = (new_var, (tyX, None)) :: ctx in
    let tyOut = infer ctx1 (subst x (Var new_var) tyB) in
    if (conv ctx1 tyIn Type) && (conv ctx1 tyOut Type) then Type else (
      print_endline ("input :" ^ to_string(tyIn));
      print_endline ("output :" ^ to_string(tyOut));
      raise (Type_error "Input or output of Pi is not a Type")
    )
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
          normalize ctx App (p, n)
  )
  | Eq (e1, e2) -> 
    if (conv ctx (infer ctx e1) (infer ctx e2)) then Type else (
      print_endline ("exp : " ^ to_string (exp));
      print_endline ("exp1 : " ^ to_string (infer ctx e1));
      print_endline ("exp2 : " ^ to_string (infer ctx e2));
      raise (Type_error "eq terms do not have same type")
    )
  | Refl e -> Eq (e, e)
  | J (p, r, x, y, e) -> (
    (*gonna infer type A from x*)
    let tyA = infer ctx x in
    (*check if y has the same type*)
    if (not (conv ctx (infer ctx y) tyA)) then raise (Type_error "x and y have different types") 
    else
      let tempX = fresh_var () in
      let tempY = fresh_var () in
      let tempE = fresh_var () in
      let ctx1 = (tempX, (tyA, None)) :: ctx in
      let ctx1 = (tempY, (tyA, None)) :: ctx1 in
      let ctx1 = (tempE, (Eq (Var tempX, Var tempY), None)) :: ctx1 in
      let tyP = infer ctx p in
      let tyR = infer ctx r in
      (*Check type of e*)
      let _ = infer ctx e in
      (*Check type of p*)
      if (not (conv ctx1 (Pi (tempX, tyA, (Pi (tempY, tyA, Pi (tempE, Eq (Var tempX, Var tempY), Type))))) tyP)) then raise (Type_error "p does not have the right type")
      else
        (*check type of r*)
        if (not (conv ctx1 (Pi (tempX, tyA, (App( App( App(p, Var tempX), Var tempX), (Refl x))))) tyR)) then raise (Type_error "proof r does not have the right type")
        else 
          normalize ctx (App( App( App(p, x), y), e))
  )

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
