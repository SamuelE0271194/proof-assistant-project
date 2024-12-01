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
  | Nat

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
  | Zero
  | Suc of tm
  | Rec of tm * tm * var * var * tm (*t, u, xy -> v --see notes 4.3.6*)
