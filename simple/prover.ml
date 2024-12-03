open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)
let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let rec string_of_ty typ =
  match typ with
  | Var y -> y
  | Imp (a, b) -> "(" ^ string_of_ty a ^ " => " ^ string_of_ty b ^ ")"
  | Conj (a, b) -> "(" ^ string_of_ty a ^ " /\\ " ^ string_of_ty b ^ ")"
  | Disj (a, b) -> "(" ^ string_of_ty a ^ " \\/ " ^ string_of_ty b ^ ")"
  | Truth -> "T"
  | False -> "_"
  | Unit -> "()"
  | Nat -> "Nat"

let rec string_of_tm tmp =
  match tmp with
  | Varm y -> y
  | Appm (a, b) -> "(" ^ string_of_tm a ^ " " ^ string_of_tm b ^ ")" 
  | Absm (a, b, c) -> "(fun (" ^ a ^ " : " ^ string_of_ty b ^ ") -> " ^ string_of_tm c ^ ")"
  | Fstm a -> "fst(" ^ string_of_tm a ^ ")"
  | Sndm b -> "snd(" ^ string_of_tm b ^ ")"
  | Pairm (a, b) -> "(" ^ string_of_tm a ^ " , " ^ string_of_tm b ^ ")"
  | Casem (t, x, u, y, v) -> 
    "case " ^ string_of_tm t ^ " of " ^
     x ^ " -> " ^ string_of_tm u ^ " | " ^
      y ^ " -> " ^ string_of_tm v 
  | Rcasem (x, a) -> "right(" ^ string_of_ty a ^ "," ^ string_of_tm x ^ ")"
  | Lcasem (x, a) -> "left(" ^ string_of_tm x ^ "," ^ string_of_ty a ^ ")"
  | Trum -> "T"
  | Falm (tm, ty) -> "absured(" ^ string_of_tm tm ^ "," ^ string_of_ty ty ^ ")"
  | Unitm -> string_of_ty Unit
  | Zero -> "Zero"
  | Suc x -> "Suc(" ^ string_of_tm x ^ ")"
  | Rec (t, u, x, y, v) -> 
    "Rec(" ^ string_of_tm t ^ ", " ^ string_of_tm u ^ ", " ^
      "(" ^ x ^ "," ^ y ^ ")-> " ^ string_of_tm v


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
  | Zero -> Nat
  | Suc x -> (
    match infer_type ctx x with
    | Nat -> Nat
    | _ -> (
      print_endline("here"); 
      raise (Type_error)
    )
  )
  | Rec (t, u, x, y, v) -> (
    match infer_type ctx t with
    | Nat -> ( 
      let tyu = infer_type ctx u in

      let ctx1 = (x, Nat) :: ctx in
      let ctx1 = (y, tyu) :: ctx1 in

      match infer_type ctx1 v with
      | w when w = tyu -> w
      | _ -> raise (Type_error)
    )
    | _ -> (
      print_endline("t is not a Nat");
      raise (Type_error)
    )
  )


and check_type ctx tm ty =
  match tm with 
  | Falm (tm, _) -> check_type ctx tm False
  | _ ->
    match infer_type ctx tm with 
    | x when x = ty -> Unitm
    | _ -> (
      (*print_endline("missmatch with " ^ string_of_tm tm ^ " and " ^ string_of_ty ty);*)
      raise (Type_error)
    )

(*Part 2*)
let rec string_of_ctx ctx =
  match ctx with 
  | [] -> ""
  | (var, ty) :: [] -> var ^ " : " ^ string_of_ty ty
  | (var, ty) :: t -> string_of_ctx t ^ " , " ^ var ^ " : " ^ string_of_ty ty 

type sequent = context * ty

let string_of_seq seq =
  match seq with
  | (ctx, ty) -> string_of_ctx ctx ^ " |- " ^ string_of_ty ty

(* Tests
let () = 
  let a = Var "A" in 
  let b = Var "B" in
  let c = Var "C" in

  let ctx : context = [
    ("x", Imp(a, b)); ("y", Conj(a, b)); ("Z", Truth);
  ] in
  print_endline (string_of_ctx ctx);

  let seq = (ctx, c) in
  print_endline (string_of_seq seq);
*)

(*Copied from proving.ml*)
let rec prove env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "exact" ->
    (
    let t = tm_of_string arg in
    if infer_type env t <> a then error "Not the right type." else
      let _ = print_endline ("exact " ^ string_of_tm t) in
      t;
    )
  | "intro" ->
    (
    match a with
    | Imp (a, b) ->
      if arg = "" then error "Please provide an argument for intro." else
        let x = arg in
        print_endline ("intro " ^ x); 
        let t = prove ((x,a)::env) b in
        Absm (x, a, t);
    | Conj (a, b) -> 
      print_endline ("intro ");
      let l = prove env a in
      let r = prove env b in
      Pairm(l, r);
    | Truth ->
      print_endline ("intro truth");
      Trum;
    | Nat ->
      if arg = "zero" then (
        print_endline ("intro zero");
        Zero;
      ) else if arg = "suc" then (
        print_endline ("intro suc");
        let n = prove env a in
        Suc(n);
      ) else error "Don't know how to introduce this."
    | _ ->
       error "Don't know how to introduce this."
    )
  | "fst" ->
    (
    let t = tm_of_string arg in
    match infer_type env t with
    | Conj (l, _) ->
      let x = arg in
      print_endline ("fst " ^ x);
      if l <> a then
        let t = prove ((x, l)::env) a in
        Fstm t;
      else 
        Fstm t;
    | _ -> error "Don't know how to use first here"
    )
  | "snd" ->
    (
    let t = tm_of_string arg in
    match infer_type env t with
    | Conj (_, r) ->
      let x = arg in
      print_endline ("snd " ^ x);
      if r <> a then
        let t = prove ((x, r)::env) a in
        Sndm t;
      else 
        Sndm t;
    | _ -> error "Don't know how to use second here"
    )
  | "left" ->
    (
    match a with
    | Disj(l, r) ->
      print_endline("left ");
      let t = prove env l in
      Lcasem (t, r); 
    | _ -> error "Don't know how to use left here"
    )
  | "right" ->
    (
    match a with
    | Disj(l, r) ->
      print_endline("right ");
      let t = prove env r in
      Rcasem (t, l); 
    | _ -> error "Don't know how to use right here"
    )
  | "elim" ->
    (
    let cases = String.split_on_char ' ' arg in
    let t = tm_of_string (List.nth cases 0) in
    match infer_type env t with
    | Imp (input, output) -> 
      (
      match a with 
      | x when x = output -> 
        print_endline ("elim " ^ arg);
        let input = prove env input in
        Appm (t, input);
      | _ -> 
        error "Don't know how to eliminate with this." 
      )
    | Disj (l, r) ->
      print_endline ("elim " ^ arg);
      let left = prove ((arg, l)::env) a in
      let right = prove ((arg, r)::env) a in
      Casem (tm_of_string arg, arg, left, arg, right)
    | False -> 
      print_endline ("elim " ^ arg);
      Falm (t, a)
    | Nat ->
      if List.length cases < 4 then error "Too little arguments (provide term, base case, var x, var y, recursion fn)" else (
        print_endline ("elim " ^ arg); (*Input [t, base, x, y, rec]*)
        
        let base = tm_of_string(List.nth cases 1) in
        let tyb = infer_type env base in
        let env1 = (List.nth cases 2, Nat) :: env in
        let env1 = (List.nth cases 3, tyb) :: env1 in
        let recur = tm_of_string(List.nth cases 4) in
        print_endline("Proof of base case (" ^ List.nth cases 1 ^ "): ");
        let pf_base = prove env tyb in
        print_endline("Proof of recursion function (" ^ List.nth cases 4 ^ "): ");
        let pf_recur = prove env1 (infer_type env1 recur) in

        Rec (t, pf_base, List.nth cases 2, List.nth cases 3, pf_recur);
      )
    | _ -> 
      error "Don't know how to eliminate this."
    )
  | "cut" ->
    (
    let t = ty_of_string arg in
    print_endline ("cut " ^ arg);
    let a = prove env (Imp (t, a)) in
    let t = prove env t in
    Appm(a, t);
    )
  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."



