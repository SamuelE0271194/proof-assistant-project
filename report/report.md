---
title: Report for the _proof assistant project_
author: Samuel Hon
---

The report below is a summary of the proof assisatnt project.

# What was implemented in the project
In the project, I managed to implement all the all the requirerd portions except for the associativity and commutativity of multiplication. 
The code is primarly divided into 2 sections, one for simple types and another for dependent types.
Both proof assistants the support for logical connectives as well as natural numbers.
Along side the main implementaiton, there are also error messages explaining the errors when writing the proof, which can hint the user on what would be an appropriate blank to fill in, this is further elaborated in the later sections.

## Simple types

Simple types are defined as follows 
```ocaml 
(** Type variables. *)
type tvar = string
type ty =
  | Var of tvar
  | Imp of ty * ty
  | Conj of ty * ty
  | Truth
  | Disj of ty * ty
  | False
  | Unit
  | Nat
```
Here we define a type (in ocaml) tvar which is just a string, this is done so we are able to distinguish between the various strings which may appear later on.
For the remaining simple types, they are defined as a type (in ocaml) as ty, the types and their defintions are as follows :
1. Var - which takes a tvar(string) as input, this is simple a name to call the various types we encounter
2. Imp - whch takes two types (A, B), this represents an implication between simple types (A -> B) 
3. Conj - which takes two types (A, B), this represents a conjunction (A \and B)
4. Truth - a type for truth which is represented as "T" when printed.
5. Disj - which takes two types (A, B), this represents a disjunction (A \or B)
6. False - a type for false represetned by "⊥"
7. Unit - a type for unit represented by "()"
8. Nat - a type for natural numbers

In addition to the types there are also the terms defined as follows
```ocaml
type var = string
type tm =
  | Varm of var
  | Appm of tm * tm
  | Absm of var * ty * tm
  | Pairm of tm * tm
  | Fstm of tm
  | Sndm of tm
  | Casem of tm * var * tm * var *tm 
  | Rcasem of tm * ty
  | Lcasem of tm * ty
  | Trum
  | Falm of tm * ty
  | Unitm
  | Zero
  | Suc of tm
  | Rec of tm * tm * var * var * tm 
```
Here we introduce a new type var which is just a string, but it serves to distinguish between strings and variables for terms, as tvar does for types.
For the remaining terms, they are defined as follows :
1. Varm - which takes a var(string), this representation for the terms which are introduced or encountered
2. Appm - taking 2 terms (a, b), this is a representation of a being applied to b "a(b)"
3. Absm - taking a var, a type and a term (x, ty, tm), this represents an abstraction with x being the name of the arbitrary variable in the term, ty being the type of x, and tm being the term which depends on x. "x (type ty) -> tm(x)" 
4. Pairm - taking two terms (a, b), this is a representation of a pair (b \times b)
5. Fstm - taking a Pairm(tm) (a, b), which represents the first term of the pair (a)
6. Sndm - taking a Pairm(tm) (a, b), which represents the second term of the pari (b)
6. Casem - taking a term (t) and variables with terms bounded to them (x -> u) (y -> v), which is a representation of case analysis 
7. Rcasem - taking a term and type, which represents the right case of a Casem term 
8. Lcasem - taking a term and type, which represents the left case of a Casem term
9. Trum - representing the truth term
10. Falm - which takes a term (a) and type (A), and represents a proof of A (which is anything) given that a is false.
11. Unitm - representing the unit term
12. Zero - the term representing the natural number 0
13. Suc - taking a term (n) (in particular a natural number), representing the successor of n
14. Rec - taking 2 terms (t, u), 2 variables (x, y) and another term (v), representing the recursor function for natural numbers

Using the proof assistant however would not require the knowledge of the terms and types above, but simply their existences. 
In the context of using the proof assistant, you can run
```bash
#Interactive mode 
make manual
#Proof from a file
make proof
```
where the manual mode will allow the user to manually type in the commands while proof mode allows the user to input a file, and running the commands in the file.

Firstly we need a statement to prove. The full list of syntaxes available are in the lexer.mll file
The various commands available are :
1.  exact, which takes an input variable, if the input variable is in the context, and the type of the variable corresponds to the type we are trying to prove, it completes the proof
2.  intro, if the type we are trying to prove has type 
  - Imp, then it also demands an input variable, it then associates the variable to the input type of the implication, and then asks for a proof of the output type of the implication
  - Conj, then it requests a proof for the first and second variable 
  - Truth, then it introduces a proof of true
  - Nat, then in also demands an input variable (which has to be a natural number in the context). If the variable is 0, then in introduces a proof of 0, if the variable is a successor of something (call it n), then it asks for a proof of n
3.  fst, which takes an input variable, if the variable is in the context and is of a type conj, it checks if the first term of the conjunction has the same type as the type we are trying to proof, and completes the proof if the type matches.
4.  snd, which does the same things as fst, but just on the second type of the conjunction.
5.  left, if the type we are proving is a disjunction, it asks for a proof of the left term
6.  right, the same as left, but for the right term of disjunction.
7.  elim, which requires at least an input, and if the first input has type
  - Imp, it checks the input type of the implication with the type we are trying to prove, if it matches, it only requires a proof of the output type of the Implication.
  - Disj, it gives a new variable in the context with type of the right term of the disjunction, after it has been used, it gives another variable with the type of the left term of the disjunction.
  - False, it returns a proof of false
  - Nat, it then requires 4 other arguments (in total 5), the base case, 2 variable x and y, and the recursion function which depends on x and y. It then asks for a proof of the base case, as well as the recursion function, given the variables x and y provided. If all the proves are given, it completes the proof of the first input (of type Nat)
8.  cut, which takes a variable, and introduces a the variable as a part of the functon.

Lets say we'd like to prove the commutativity of the and operator, then the following statements is a proof of the statement.
```
A /\ B => B /\ A
intro x
intro
snd x
fst x
```

## Dependent types

...

# Difficulties encountered

One of the biggest difficulties encountered was in the normalization of terms. 
There were many points in this project where the proofs I provided were not being accepted by the assistant.
However when inspecting the outputs, it was usually the result of certain terms remaining in their unnormalized form.
While it may seem like a simple fix, to just simple normalize the output where needed, it did not seem obvious when I was coding the project. 
There were certain outputs which already seemed normalized, as the outputs were composed of normalized terms.
However it was necessary to then normalize the term as a whole as there might be further normalization that could occur in the composition.

# Implementation choices

Detail

# Possible extensions

Imagine

# Conclusion

Conclude



Explain. You can write inline code `let x = 4`{.ocaml} or cite paragraphs of your code

```ocaml
let rec f x =
  let y = x + x in
  y * y
```

you have words in _italic_ or in **bold**.

