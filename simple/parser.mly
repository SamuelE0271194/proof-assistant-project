%{
open Expr
%}

%token IMP AND OR TRUE FALSE NOT
%token FUN TO CASE OF
%token LPAR RPAR COLON COMMA BAR
%token FST SND LEFT RIGHT ABSURD
%token <string> IDENT
%token EOF

%right IMP
%right OR
%right AND
%nonassoc NOT

%start ty
%start tm
%type <Expr.ty> ty
%type <Expr.tm> tm
%%

/* A type */
ty:
  | IDENT     { Var $1 }
  | ty IMP ty { Imp ($1, $3) }
  | ty AND ty { Conj ($1, $3) }
  | ty OR ty  { Disj ($1, $3) }
  | NOT ty    { Imp ($2, False) }
  | TRUE      { Truth }
  | FALSE     { False }
  | LPAR ty RPAR { $2 }

/* A term */
tm:
  | atm                                    { $1 }
  | FUN LPAR IDENT COLON ty RPAR TO tm     { Absm ($3, $5, $8) }
  | CASE tm OF IDENT TO tm BAR IDENT TO tm { Casem ($2, $4, $6, $8, $10) }

/* An application */
atm:
  | stm     { $1 }
  | atm stm { Appm ($1, $2) }

/* A simple term */
stm:
  | IDENT                        { Varm $1 }
  | LPAR tm RPAR                 { $2 }
  | FST stm                      { Fstm $2 }
  | SND stm                      { Sndm $2 }
  | LPAR RPAR                    { Unitm }
  | LPAR tm COMMA tm RPAR        { Pairm ($2, $4) }
  | LEFT LPAR tm COMMA ty RPAR   { Lcasem ($3, $5) }
  | RIGHT LPAR tm COMMA ty RPAR  { Rcasem ($3, $5) }
  | ABSURD LPAR tm COMMA ty RPAR { Falm ($3, $5) }

