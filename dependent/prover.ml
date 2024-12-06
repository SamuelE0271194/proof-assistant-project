open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

let rec to_string exp =
  match exp with
  | Type -> "Type"
  | Var x -> x
  | App (inp, out) -> "(" ^ to_string inp ^ " " ^ to_string out ^ ")"
  | Abs (x, tyX, exp) -> "(fun (" ^ x ^ " : " ^ to_string tyX ^ ") -> " ^ to_string exp ^ ")"
  | Pi (x, tyX, tyB) -> "((" ^ x ^ " : " ^ to_string tyX ^ ") -> " ^ to_string tyB ^ ")"
  | _ -> "Not implemented yet"

let fresh_constant = ref 0 ;;

let fresh_var _ = 
  fresh_constant := !fresh_constant + 1;
  ("x" ^ string_of_int(!fresh_constant))

let rec subst var ex1 ex2 =
  match ex2 with 
  | Type -> Type
  | Var x when x = var -> ex1
  | App (exA, exB) -> App (subst var ex1 exA, subst var ex1 exB)
  (*Note that x does not appear in tyX*)
  | Abs (x, tyX, exp) -> (
    let new_var = fresh_var () in
    Abs (new_var, subst var ex1 tyX, subst var ex1 (subst x (Var new_var) exp))
  )
  | Pi (x, tyX, tyB) -> (
    let new_var = fresh_var () in
    Pi (new_var, subst var ex1 tyX, subst var ex1 (subst x (Var new_var) tyB))
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
  | _ -> Type (*Not yet implemented stuff*)

let rec alpha exp1 exp2 = 
  match (exp1, exp2) with
  | (Var v1, Var v2) -> v1 = v2
  | (App (e1, e2), App (f1, f2)) -> (alpha e1 e2) && (alpha f1 f2)
  | (Abs (y, tyY, e1), Abs(z, tyZ, e2)) -> (
    let check_var = alpha tyY tyZ in
    let sube2 = subst z (Var y) e2 in 
    check_var && (alpha e1 sube2)
  )
  | (Pi (y, tyY, ty1), Pi(z, tyZ, ty2)) -> (
    let check_var = alpha tyY tyZ in
    let new_var = fresh_var () in
    let sty1 = subst y (Var new_var) ty1 in
    let sty2 = subst z (Var new_var) ty2 in
    check_var && (alpha sty1 sty2)
  )
  | (Type, Type) -> true
  | _ -> false (*maybe not yet implemented *)

let conv ctx exp1 exp2 = 
  (*print_endline("comparing");
  print_endline(to_string exp1);
  print_endline(to_string exp2);*)
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
      match infer ctx exp2 with
      | Pi (y, tyY, tyC) -> (
        let ctx1 = (y, (tyY, None)) :: ctx in 
        let ctx1 = (x, (tyC, None)) :: ctx1 in 
        if (conv ctx1 tyX tyC) then Pi (y, tyY, tyB) else
          raise (Type_error "fg, g does not have output matching f input")
      )
      | tyC -> (
        let ctx1 = (x, (tyX, None)) :: ctx in
        if (conv ctx1 tyX tyC) then (subst x tyC tyB) else
          raise (Type_error "fx, x does not have type matching f input")
      )
    )
    | _ -> raise (Type_error "application of non function")
  )
  | Abs (x, tyX, expAbs) -> (
    let ctx1 = (x, (tyX, None)) :: ctx in
    Pi (x, tyX, infer ctx1 expAbs)
  )
  | Pi (_, _, _) -> Type
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
