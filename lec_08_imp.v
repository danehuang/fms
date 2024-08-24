(** * IMP *)


(** ** References

   - https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html
   - https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

 *)


Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Strings.String.


(** ** Recap *)

(**
   - Last time, we saw the Turing maching (TM).
   - As a reminder, the operation that a TM added over a deterministic finite
     automata (DFA) was the ability to read/write to a tape.
   - We might wonder now: what is the corresponding language for a TM, similar
     to how a regular expression was the corresponding language for a DFA.
   - Today we will look at a simple language that is Turing complete:
     IMP (imperative programming) and some of its properties.
   - This language is a simple model of the languages that we normally
     program with.
   - This language will contain linguistic operations for reading and
     writing to state.
 *)


(** ** Goal for today

   - Introduce the IMP language.
   - Show how to model _state_ with total maps.
   - Introduce _big-step_ semantics for IMP.
   - Show that IMP is _deterministic_ and (informally) Turing complete.
   - Introduce _small-step_ semantics for IMP.

 *)


(** ** IMP *)


(** ** Factorial program in IMP

<<
  Z := X;                 (assign X to Z)
  Y := 1;                 (assign Y to 1)
  while ~(Z = 0) do       (while Z is not 0)
    Y := Y * Z;           (update Y with Y * Z)
    Z := Z - 1            (update Z with Z - 1)
  end
>>
*)


(** ** We need to define two pieces of syntax
   
   - expressions (arithmetic and boolean)
   - commands (this will be new)
 *)



(** ** Arithmetic expressions and identifiers

<<
   aexp ::= n 
          | x             (identifier, new)
          | aexp + aexp
          | aexp - aexp
          | aexp * aexp
>>
 *)

Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)        (* identifiers, new *)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).


(** *** Ignore me, just for writing syntax *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Open Scope com_scope.


(** *** Examples *)

Definition X : string := "X".

Definition ae1 : aexp :=
  <{
      1 + 2 + 3
    }>.
Print ae1.
Set Printing Coercions.
Print ae1.


(** *** Abstract Syntax

   - Note that we are simply writing *abstract syntax* down or *abstract syntax trees*
     (ASTs).
   - If we wanted a different order of parenthesization, we would need parentheses.
   - This is part of *surface syntax* and is not technically part of the AST.
 *)


Definition ae2 : aexp :=
  <{
      1 + (2 + 3)   (* note that the "(" and ")" are not part of the language *)
    }>.
Print ae2.


(** 
  - What about expressions with variables?
  - This expression might not make sense but it is a valid expression.
 *)

Definition still_ae : aexp :=
  <{
      1 - (2 * 3) + X
    }>.
Print still_ae.


(** 
    You might be wondering what the difference between  
      [1 + 2 + 3]
    and
      [ <{ 1 + 2 + 3 >} ]
    is.
 *)

Eval compute in 1 + 2 + 3.
Eval compute in ae2.


(** *** Terminology
   - _Object langauge_ is the language of study
   - _Meta-language_ is the language we use to study an object language.
   - We are using Coq (technically Gallina) as the meta-language.
   - We are studying IMP as the object-language.
   - Consequently, [1 + 2 + 3] is an expression in the meta-language
   - And [ <{ 1 + 2 + 3 >} ] is an expression in the meta-language as that is 
     an encoding of an expression in the object language.
 *)


Definition ae3 : aexp :=
  <{
      1 - (2 * 3)
    }>.
Print ae3.

(** 
  - Question: What if we wanted to add division?
 *)


(** *** Advanced topic: shallow embedding vs. deep embedding

  - _Shallow embedding_: use the expressions of the meta-language to
    directly encode expressions in the object language.
  - _Deep embedding_: define an abstract syntax tree (AST) in the meta-language
    to encode expressions in the object language. What we have done with [aexp]
    is a deep embedding.
  - The advantage of a shallow embedding is that we can take advantage of
    a powerful meta-language.
  - The disadvantage of a shallow embedding is that a meta-language may
    be too powerful that it makes reasoning about arbitrary meta-linguistic
    constructs when reasoning about an object language too difficult.
*)

Inductive aexp' : Type :=
| ANum' (n: nat)                (* natural numbers, same as before *)
| AId' (x: string)              (* identifiers, same as before *)
(* Different, using a Coq binary function, of which +/-/* are definable in.
   Thus this language is more powerful. *)
| AOp' (f: nat -> nat -> aexp') (x1: aexp') (x2: aexp')  
.


(**
   - The previous three examples with a shallow embedding.
 *)
Definition ae1' : aexp' :=
  AOp' (fun x y => ANum' (x + y)) (AOp' (fun x y => ANum' (x + y)) (ANum' 1) (ANum' 2)) (ANum' 3).

Definition ae2' : aexp' :=
  AOp' (fun x y => ANum' (x + y)) ((AOp' (fun x y => ANum' (x + y)) (ANum' 1) (ANum' 2))) (ANum' 3).

Definition ae3' : aexp' :=
  AOp' (fun x y => ANum' (x - y)) ((AOp' (fun x y => ANum' (x * y)) (ANum' 1) (ANum' 2))) (ANum' 3).


(** 
  - We get division for "free".
 *)
Definition ae4' : aexp' :=
  AOp' (fun x y => ANum' (x / y)) ((AOp' (fun x y => ANum' (x * y)) (ANum' 1) (ANum' 2))) (ANum' 3).


(** 
  - We also get a bunch of other stuff that we may not want.
 *)
Section BUNCH_OF_OTHER_STUFF_FOR_FREE.
  Variable foobar: nat -> nat -> aexp'.
  Variable bazbae: nat -> nat -> aexp'.
  
  Definition ae5' : aexp' :=
    AOp' foobar ((AOp' bazbae) (ANum' 1) (ANum' 2)) (ANum' 3).
End BUNCH_OF_OTHER_STUFF_FOR_FREE.



(** *** Extremely advanced topic

   - What if we tried to use Coq's variables to handle AId'?
   - This would be parametric higher-order abstract syntax (PHOAS).
   - We will run into this when we talk about lambda calculus.
*)


(** ** Boolean Expressions *)


(** *** Boolean expressions and identifiers

<<
   bexp ::= BTrue
          | BFalse
          | bexp = bexp
          | bexp <= bexp
          | ~ bexp
          | bexp && bexp
>>
 *)

Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)  (* refers to aexp *)
| BLe (a1 a2 : aexp)  (* refers to aexp *)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).


(** *** Ignore me, just some syntax *)

Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).


Definition be1 : bexp :=
  <{
      1 = 2
    }>.
Print be1.



Definition be2 : bexp :=
  <{
      1 = 2 && 1 <= 2 && ~false
    }>.
Print be2.


(** 
  - Exercise: shallow embedding for boolean expressions?
 *)


(** *** Aside: Computational Reflection

  - We can think of computational reflection as an embedding of bool in Prop!
 *)


(** ** State *)

(**
   - Previously, we just defined the _syntax_.
   - Now we need to define the _semantics_, i.e., what the syntax means.
   - We have seen two ways to define _semantics_ in Coq
      - With a function definition. Function definitions must terminate.
      - With a transition relation. Transition relations can handle
        non-terminiation and non-determinism.
   - Here we will choose to use a function definition.
   - Before we can define the evaluation function, we need to define
     how to interpret identifiers.
   - Enter the concept of _state_.
 *)


(** *** Total map

  - A total map is simply a function from strings to any type A.
 *)
Definition total_map (A: Type) := string -> A.


(** *** State

  - We define state as a *total* map from strings to A.
  - Thus we have an infinite amount of memory.
  - This should remind you of a TM tape.
  - But this is an unrealistic model of digital computer memory.
 *)
Definition state := total_map nat.


(** *** Aside: Finite State

  - We could define state as a partial map.
  - But note: this would mean that we no longer have a Turing complete language!
 *)
Definition partial_map (A: Type) := string -> option A.


(**  
   - An empty map by definition needs to map every string to a default value.
 *)
Definition t_empty {A: Type} (v: A): total_map A :=
  (fun _ => v).

Eval compute in t_empty 0.

(**
   - Looking up from a map is simply function application.
 *)
Definition hello: string := "hello".
Eval compute in (t_empty 0) (hello).

(**
   - Checking if two strings are equivalent is decidable.
 *)
Definition eqb_string (x y: string): bool :=
  if string_dec x y then true else false.

(**
   - This might be the strangest update function you've ever seen.
   - It relies on higher-order functions.
 *)
Definition t_update {A : Type} (m: total_map A) (x: string) (v: A) :=
  fun x' => if eqb_string x x' then v else m x'.

Eval compute in (t_empty 0) hello.
Eval compute in (t_update (t_empty 0) hello 1) hello.


(**
   - We can now define state as a total map whose default value is 0.
   - You can ignore all the notation.
 *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).


Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros.
  unfold t_update, eqb_string.
  remember (string_dec x x) as b.
  destruct b; auto.
  contradiction.
Qed.


Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update, eqb_string.
  remember (string_dec x1 x2) as b.
  destruct b; auto.
  contradiction.
Qed.


(**
   - Shallow embedding of state means we need functional extensionality.
 *)

From Coq Require Import Logic.FunctionalExtensionality.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  unfold t_update, eqb_string.
  apply functional_extensionality.  (* bad news with shallow embedding *)
  intros.  
  remember (string_dec x x0) as b.
  destruct b; auto.
Qed.


Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros.
  unfold t_update, eqb_string.
  apply functional_extensionality.
  intros.
  remember (string_dec x x0) as b.
  destruct b; subst; auto.
Qed.  


(** ** IMP Evaluation *)


(**
   - We need to define evaluation of arithmetic and boolean expressions.
   - Then we will define commands and evaluation on them.
 *)


(** *** Arithmetic and boolean expressions *)

(**
   - Every evaluation function will now carry state as an extra argument.
   - The state will be used to interpret the state.
   - You can think of the identifier as the "address" of the location in memory.
 *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x   (* lookup the identifier in the state *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.


Example aexp1 :
  aeval (X !-> 5) <{ 3 + (X * 2) }> = 13.
Proof.
  simpl.
  reflexivity.
Qed.


Definition Y: string := "Y".
Definition Z: string := "Z".

Example aexp2 :
  aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }> = 20.
Proof.
  simpl.
  reflexivity.
Qed.



(**
   - Similarly, we can define boolean evaluation.
   - We need to "thread" the state through evaluation of boolean expressions.
   - This is because this definition depends on evaluating arithmetic expressions.
 *)

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.


Example bexp1 :
  beval (X !-> 5) <{ true && ~(X <= 4) }> = true.
Proof.
  simpl.
  reflexivity.
Qed.


(** *** Commands *)

(**
   - Expressions produce values once they are evaluated.
   - In particular, there was no way to produce an effect on state.
   - We will need *commands* to produce effects on state.
   - To do this, we will need a language of commands.
 *)


(** *** Commands
    
    com := skip 
        | x := aexp                 (assign)
        | c1; c2                    (seq)
        | if bexp { c1 } { c2 }     (if)
        | while bexp { c }          (while)
 *)

Inductive com : Type :=
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).


(** *** Ignore me *)

Notation "'skip'" :=
  CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
  (CAsgn x y)
    (in custom com at level 0, x constr at level 0,
        y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (CSeq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (CIf x y z)
    (in custom com at level 89, x at level 99,
        y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (CWhile x y)
    (in custom com at level 89, x at level 99, y at level 99) : com_scope.


(** *** Examples *)

Definition fact_in_imp: com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.
Print fact_in_imp.


(**
   - As before, we are just defining AST.
 *)

Unset Printing Notations.
Print fact_in_imp.
Set Printing Notations.


(**
   - We can define an infinite loop in IMP.
   - We can not define an infinite loop in Coq directly.
 *)

Definition loop : com :=
  <{ while true do
       skip
     end }>.


(** *** Big-Step Semantics *)


(**
   - Unlike evaluation of arithmetic expressions or boolean expressions,
     we need to define a transition relation since we have infinite loops.
   - Nevertheless, we have a choice of a style of semantics between
     big-step and small-step semantics.
   - We start with big-step.
 *)


(** *** Inference rules *)
(*

    -------------------- E_Skip
      (st, Skip) => st


        aeval st a = n
  ----------------------------- E_Asgn
    (st, x := a) => st[x -> n]


    (st, c1) => st'  (st', c2) => st''
  -------------------------------------- E_Seq
            (st, c1;c2) => st''


    beval st b = true    (st, c1) => st'
  --------------------------------------- E_IfTrue
     (st, if b { c1 } { c2 }) => st'


    beval st b = false   (st, c2) => st'
  --------------------------------------- E_IfFalse
     (st, if b { c1 } { c2 }) => st'


        beval st b = false
  ------------------------------- E_WhileFalse
     (st, while b { c } ) => st


    beval st b = true    (st, c) => st'  (st', while b { c }) => st''
  -------------------------------------------------------------------- E_WhileTrue
                     (st, while b { c } ) => st''
 *)


Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').


(**
   - We can think of big-step semantics as a relational way to encode
     "evaluate" to a "value".
   - In this case, the "value" is a state.
*)


(**
   - Let's work out this example.
 *)

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  { (* c1 *)
    apply E_Asgn.
    reflexivity.
  }
  {
    (* c2 *)
    apply E_IfFalse. (* X <= 1 false *)
    - simpl.
      reflexivity.
    - apply E_Asgn.  (* Z := 4 *)
      simpl.
      reflexivity.
  }
Qed.



(**
   - More practice with inductive proofs.
 *)


(** *** Inference rules *)
(*

    -------------------- E_Skip
      (st, skip) => st


        aeval st a = n
  ----------------------------- E_Asgn
    (st, x := a) => st[x -> n]


    (st, c1) => st'  (st', c2) => st''
  -------------------------------------- E_Seq
            (st, c1;c2) => st''


    beval st b = true    (st, c1) => st'
  --------------------------------------- E_IfTrue
     (st, if b { c1 } { c2 }) => st'


    beval st b = false   (st, c2) => st'
  --------------------------------------- E_IfFalse
     (st, if b { c1 } { c2 }) => st'


        beval st b = false
  ------------------------------- E_WhileFalse
     (st, while b { c } ) => st


    beval st b = true    (st, c) => st'  (st', while b { c }) => st''
  -------------------------------------------------------------------- E_WhileTrue
                     (st, while b { c } ) => st''
 *)

Theorem ceval_deterministic:
  forall (c: com) (st st1: state),
    st =[ c ]=> st1 ->
    forall (st2: state),
      st =[ c ]=> st2 ->
      st1 = st2.
Proof.
  intros c st st1 E1.
  
  (* induction on the transition relation *)
  induction E1; intros st2 E2. 
  {
    (* case: E_Skip *)
    inversion E2; subst.
    reflexivity.
  }
  {
    (* case: E_Asgn *)
    inversion E2; subst.
    reflexivity.
  }
  {
    (* case: E_Seq *)
    inversion E2; subst.
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2.
    assumption.
  }
  {
    (* case: E_IfTrue *)
    inversion E2; subst.
    - apply IHE1.
      assumption.
    - rewrite H in H5.
      discriminate.
  }
  {
    (* case: E_IfFalse *)
    inversion E2; subst.
    - rewrite H in H5.
      discriminate.
    - apply IHE1.
      assumption.
  }
  {
    (* case: E_WhileFalse *)
    inversion E2; subst.
    - reflexivity.
    - rewrite H in H2.
      discriminate.
  }
  {
    (* case: E_WhileTrue *)
    inversion E2; subst.
    - rewrite H in H4.
      discriminate.
    - rewrite (IHE1_1 st'0 H3) in *.
      apply IHE1_2.
      assumption.
  }
Qed.


(** ** IMP is Turing Complete *)

(**
   - How can we argue that IMP is Turing complete?
   - By Reduction!
 *)


(**
   - We encode Turing machine in IMP.
   - How do we do this?
   - We can encode the tape in the state by mapping "i" to the ith cell of the tape.
   - We can encode the entire transition table as a giant if-else statement.
   - We can encode the position of the head in the state variable "head" which holds
     the cell number i.
   - We can encode the tape in the state variable "state" and use the bijection
     nat ~ list {0, 1}
   - Question: why can't we do the more direct mapping of "index" -> cell contents?
 *)


(** ** IMP Mixed-Step Semantics *)

(**
   - We can also give *mixed-step* semantics.
   - We use *small-step* semantics where possible.
   - We use "big-step" or evaluation semantics for arithmetic and boolean expressions.
 *)


(** *** Inference rules *)
(*
    
               aeval st a1 = n
   ---------------------------------------- CS_Asgn
    (i := a1, st) --> (skip, st[i -> n])


              (c1, st) --> (c1', st')
   ---------------------------------------- CS_SeqStep
        (c1; c2, st) --> (c1'; c2, st')


   ------------------------------- CS_SeqFinish
     (skip; c2, st) --> (c2, st)


                beval st b = true   
   ----------------------------------------- CS_IfTrue
     (if b { c1 } { c2 }, st) --> (c1, st)


                beval st b = false
   ----------------------------------------- CS_IfFalse
     (if b { c1 } { c2 }, st) --> (c2, st)


                
   ------------------------------------------------------------------------ CS_While
     (while b1 { c1 }, st) --> (if b1 { c1 } { skip }; while b1 { c1 }, st)
 *)


Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
| CS_Asgn : forall st i a (n : nat),
    aeval st a = n ->
    <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
| CS_SeqStep : forall st c1 c1' st' c2,
    c1 / st --> c1' / st' ->
    <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
| CS_SeqFinish : forall st c2,
    <{ skip ; c2 }> / st --> c2 / st
| CS_IfTrue : forall st b c1 c2,
    beval st b = true ->
      <{ if b then c1 else c2 end }> / st --> c1 / st
| CS_IfFalse : forall st b c1 c2,
    beval st b = false ->
    <{ if b then c1 else c2 end }> / st --> c2 / st
| CS_While : forall st b1 c1,
    <{ while b1 do c1 end }> / st
    -->
    <{ if b1 then c1; while b1 do c1 end else skip end }> / st
where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).


(**
   - We can think of small-step semantics as detailing each step of machine execution.
   - Thus small-step semantics gives us a more fine-grained view of what is going on.
 *)


Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem big_step_implies_small_step:
  forall st c st',
    st =[ c ]=> st' ->
    multi cstep (c, st) (CSkip, st').
Proof.
  (* Challenge! *)
Admitted.
  
(**
   - Question: What about small-step implies big-step?
*)


(** ** Summary 

   - We introduced the IMP language which adds state.
   - We gave big-step and small-step semantics for IMP.
   - We saw that IMP evaluation is deterministic and Turing complete.
 *)
