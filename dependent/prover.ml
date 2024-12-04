open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

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
  | (var, (exp1, exp2)) :: l -> 
    match exp2 with
    | Some x -> 
      var ^ " : " ^ to_string exp1 ^ " = " ^ to_string x ^ "\n" ^ string_of_context l
    | None -> 
      var ^ " : " ^ to_string exp1 ^ "\n" ^ string_of_context l

exception Type_error of string

let rec in_ctx ctx var =
  match ctx with
  | [] -> raise (Type_error (" Not in ctx " ^ var))
  | (x, (exp1, exp2)) :: l -> (
    if var = x then match exp2 with
      | Some x -> x
      | None -> exp1
    else in_ctx l var
  )

let rec normalize ctx exp = 
  match exp with 
  | Type -> Type
  | Var x -> in_ctx ctx x
  | App (exA, exB) -> (
    match exA with
    | Abs (y, exAbs, exBbs) -> (
      let ctx1 = (y,(exAbs,None)) :: ctx in
      subst y (normalize ctx1 exB) (normalize ctx1 exBbs) (*assumed that its well typed, so don't care about type of y (exAbs)*)
    )
    | _ -> App (normalize ctx exA, normalize ctx exB)
  )
  | Abs (y, exA, exB) -> (
    let ctx1 = (y,(exA,None)) :: ctx in
    Abs (y, normalize ctx1 exA, normalize ctx1 exB)
  )
  | Pi (y, exA, exB) -> Pi (y, normalize ctx exA, normalize ctx exB)
  | _ -> Type (*Not yet implemented*)

let rec alpha exp1 exp2 =
  match (exp1, exp2) with
  | (Var v1, Var v2) -> v1 = v2
  | (App (e1, e2), App (f1, f2)) -> (alpha e1 e2) && (alpha f1 f2)
  | (Abs (y, e1, e2), Abs(z, f1, f2)) -> (
    let check_var = alpha e1 f1 in
    let f22 = subst z (Var y) f2 in 
    check_var && (alpha e2 f22)
  )
  | (Pi (y, e1, e2), Pi(z, f1, f2)) -> (
    let f12 = subst z (Var y) f2 in 
    let f22 = subst z (Var y) f1 in
    (alpha e1 f12) && (alpha e2 f22)
  )
  | (Type, Type) -> true
  | _ -> false (*prob not yet implemented*)

let conv ctx exp1 exp2 =
  alpha (normalize ctx exp1) (normalize ctx exp2)

let rec infer ctx exp =
  match normalize ctx exp with
  | Type -> Type
  | Var x -> in_ctx ctx x (*The type error is thrown from in_ctx*)
  | App (exA, exB) -> App (infer ctx exA, infer ctx exB)
  | Abs (y, exA, exB) -> (
    let ctx1 = (y,(exA,None))::ctx in
    Abs (y, infer ctx exA, infer ctx1 exB)
  )
  | Pi (y, exA, exB) -> (
    let ctx1 = (y,(exA,None))::ctx in
    Pi (y, infer ctx exA, infer ctx1 exB)
  )
  | _ -> raise (Type_error " not yet implemented")

let check ctx exp1 exp2 =
  if conv ctx exp1 exp2 then () else
    raise (Type_error (" Term does not match type (" ^ to_string exp1 ^ " : " ^ to_string exp2 ^ ")"))


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
