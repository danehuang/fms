(** ** Contents *)

(**
  - Part I: Introduction to Proof Assistants
  - Part II: Finite State Automata and Turing Machines
  - Part III: Programming Languages
 *)


(** ** Data and Functions in Coq *)

(**
  - We first need to learn how to use a proof assistant.
  - To do this, we will need to learn how to "program" in the proof assistant.
  - Lecture notes heavily based off
    - Introduction to Computational Logic: https://www.ps.uni-saarland.de/courses/cl-ss14/script/icl.pdf
    - Software Foundations: https://softwarefoundations.cis.upenn.edu/
  - Today's lecture notes will go over
    - https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
    - https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
 *)


(** ** Bool Types *)

(** 
  - Everything in Coq, including truth values and numbers, is built up from data.
  - That means before we can even work with mathematical objects, we must define them.
 *)

Inductive bool : Type :=
  | true
  | false.

(** 
  - [Inductive] is a keyword that describes a bunch of cases.
  - [bool] is the name of the inductive type.
  - [true] and [false] are the two cases.
  - [Type] is the type of bool.
 *)


(**
  - Every expression in Coq has a type describing what kind of value it computes.
  - The [Check] command prints the type of an expression.
 *)

Check bool.
(* 
    ===> [bool : Set]

    Don't worry about [Set] vs. [Type] for now. 
 *)


Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.


Check negb.
(*  
    ===> [negb: bool -> bool]

    So it is a function that takes in [bool] and produces [bool].
*)


(**
  - Expressions in Coq can be reduced.
  - The [Compute] command reduces an expression.
 *)
Compute negb true.
(*
    [===> false : bool]
*)

(** 
  - We should read this as the value is [false].
  - [false] is of type [bool].
  - And [bool] is of type [Set] / [Type] (Don't worry about this for now.)
 *)
Compute negb false.


Compute negb (negb true).



(* ================================================================= *)
(** ** Proofs *)

Lemma first_lemma :
  negb true = false.
Proof.
  simpl.         (* tactic [simpl] "simplifies" *)
  reflexivity.   (* tactic [reflexivity] finishes subgoal if identical *)
Qed.


Check first_lemma.
(* ===> first_lemma : nebg true = false *)


(** English version: double negation is idempotent (for any boolean). *)

Lemma negb_negb :
  forall x: bool, negb (negb x) = x.
Proof.
  intros x.       (* tactic [intros] introduces variable x *)
  destruct x.     (* tactic [destruct] does case analysis on inductive [bool] *)
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Definition andb (b1: bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.


Lemma andb_com :
  forall x y: bool, andb x y = andb y x.
Proof.
  intros x.
  intros y.
  destruct x.
  {
    destruct y.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  }
  {
    destruct y.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  }
Qed.

(**
  - That was a long proof.
  - We can simplify this with the chaining tactical [;].
 *)

Lemma andb_com' :
  forall x y: bool, andb x y = andb y x.
Proof.
  intros x y.
  destruct x; destruct y; reflexivity.
Qed.

(** Summary
  - [intros] tactic
  - [reflexivity] tactic
  - [destruct] tactic
  - [;] tactical
*)


(** ** Notation *)

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Compute orb true (andb true true).


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


(** ** If/Else 

    - You can program with if/then else statements in Coq
      just like in any ordinary programming language.
 *)

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

Lemma negb_negb':
  forall b: bool, negb b = negb' b.
Proof.
  intros b.
  destruct b.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Lemma andb_andb':
  forall b1 b2: bool, andb b1 b2 = andb' b1 b2.
Proof.
Admitted.

Lemma orb_orb':
  forall b1 b2: bool, andb b1 b2 = andb' b1 b2.
Proof.
Admitted.


(** ** Natural Numbers 

   - Everything in Coq is built from scratch based on inductive data-types.
   - This is true even for "basic concepts" such as natural numbers.
*)

Module MyNat.         (* Introduce a namespace. *)

  Inductive nat : Type :=
  | O : nat          (* 0 *)
  | S : nat -> nat.  (* successor, i.e., add 1 *)

  (** 
    - [nat] is an inductive type of type [Type].
    - [O] is a constructor of type [nat].
    - [S] is a constructor of type [nat -> nat].
   *)

  Check nat.
  Check O.
  Check S.

  Compute O. (* 0 *)

  Compute S O. (* 1 *)

  Compute S (S O). (* 2 *)

  Compute S (S (S (S O))). (* 4 *)

  (** 
    - At this point, [nat] is just some data.
    - We need to define operations like addition and subtraction if we
      want to interpret [nat] as a natural number.
   *)

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

  Compute pred O.

  Compute pred (S O).

  Compute pred (S (S O)).


  (** 
    - We need to define [plus] by structural recursion on it's arguments.
    - Note that [plus] can be an arbitrary function, but we are defining
      it to mirror what we expect addition on natural numbers to be.
   *)

  (* f(f(x)) = f(x) *)
  
  Fixpoint plus (x y : nat) : nat :=
    match x with
    | O => y
    | S x' => S (plus x' y)
    end.

  Compute plus (S (S O)) (S (S (S O))).


  (** 
    - Definining whether a natural number is even by structural recursion
      on it's arguments.
   *)

  Fixpoint even (n:nat) : bool :=
    match n with
    | O        => true
    | S O      => false
    | S (S n') => even n'
    end.

  Definition odd (n:nat) : bool :=
    negb (even n).

  Example test_odd1:
    odd (S O) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_odd2:
    odd (S (S (S (S O)))) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.


  (** 
    - We defined natural numbers and operations like [plus].
    - Now we need to "prove" that they have properties that we care about.
   *)

  Lemma plus_O:
    forall x: nat, plus O x = x.
  Proof.
    intros x.
    simpl.
    reflexivity.
  Qed.
  
  Lemma plus_O':
    forall x: nat, plus x O = x.
  Proof.
    intros x.
    simpl.
  Abort.

  (** 
    - Why did that fail?
    - The simplification mechanism in Coq works on the arguments from left
      to right.
    - A variable was in the left argument, so it cannot be simplified.
    - We need a more powerful tactic: [induction.
   *)

  Check nat.
  Print nat.
  Print nat_ind.

  Lemma plus_O'':
    forall x: nat, plus x O = x.
  Proof.
    induction x.
    - simpl. 
      reflexivity.
    - simpl.
      rewrite IHx.
      reflexivity.
  Qed.
End MyNat.
  

(** ** Natural Numbers in Coq Standard Library *)

(** 
  - That was laborious ...
  - Thankfully Coq provides a standard library of natural numbers.
  - But keep in mind that the standard library is built from the ground up
    as we just did above.
 *)

Print nat.
Check 40.
Compute 2 - S O.

Theorem plus_1_l :
  forall n: nat, 1 + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


(** 
  - Defining more operations on natural numbers.
 *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

Compute minus 2 0.
Compute minus 2 1.


Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 2 3) = 6.
Proof.
  reflexivity.
Qed.


(** 
  - Defining more notation on natural numbers.
 *)

Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "x - y" := (minus x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).

Theorem minus_n_0 :
  forall n: nat, n - 0 = n.
Proof.
  induction n.
  reflexivity.
  reflexivity.
Qed.

Theorem mult_0_l :
  forall n:nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.


Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.


(** ** Comparing Natural Numbers *)

(** 
  - Definining whether a natural number is equal to another natural number
    by structural recursion on it's arguments.
 *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Compute eqb 3 3.
Compute eqb 1 2.


(** 
  - Definining whether a natural number is less than another natural
    number by structural recursion on it's arguments.
 *)
Fixpoint leb (x y: nat) : bool :=
match x with
| O => true
| S x' =>
    match y with
    | O => false
    | S y' => leb x' y'
    end
end.

Fixpoint leb' (x y: nat) : bool :=
match x, y with
| O, _ => true
| S x', O => false
| S x', S y' => leb x' y'
end.


Example test_leb1:
  leb 2 2 = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_leb2:
  leb 2 4 = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_leb3:
  leb 4 2 = false.
Proof.
  simpl.
  reflexivity.
Qed.


(** ** More Complex Proofs 

   - We can begin to write more complex proofs. 
*)

Theorem plus_id_example :
  forall n m:nat,
    n = m ->
    n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.
