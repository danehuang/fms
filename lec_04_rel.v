(** * Inductive Propositions, Relations, and Curry-Howard *)

(** ** References

   - https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
   - https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html

 *)

(** ** Recap

  - Last time we introduced the language of propositions in Coq.
    Propositions enable us to express logical claims.
    These claims could either by [True] or [False]
  - We then saw how we could use the proof system in Coq to prove if a
    proposition was [True] or [False].
  - Finally, we saw that what distinguished a proposition from booleans
    was the notion of *decidability*. A general proposition does not 
    satisfy law of excluded middle whereas a decidable proposition does.
    This naturally led us to consider the constructive nature of Coq.
  - Today will be the final part of our crash course into Coq before turning
    our attention to survey various computational models (machine + language).
*)


(** ** Goal for today

   - Introduction to inductively defined propositions
   - Induction and proof trees
   - Arithmetic expression language + operational semantics.
   - _Operational semantics_ for arithmetic expression language.
   - Introduce the _Curry-Howard isomorphism_.
   - Equality as an inductive type.

 *)
                         


(* ================================================================= *)
(** ** Even as an Inductively Defined Propositions *)


(**
   - We already saw that we could define inductive data-types
<<
Inductive nat : Set :=
| O: nat
| S: nat -> nat
>>
 *)


(**
   - We also saw two ways to define evenness on natural numbers.

<<
Fixpoint is_evenb (n: nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => is_evenb n'
  end.
>>

<<
Fixpoint is_even (n: nat): Prop :=
  match n with
  | O => True
  | S O => False
  | S (S n') => is_even n'
  end.
>>

<<
Definition is_even_ex (n: nat): Prop :=
  exists m: nat, double m = n.
>>
 *)


(**
   - Now we'll see how we can use inductive definitions to define evenness.
   - This will be our first example of an _inductively defined proposition_.
   - SEAR THIS EXAMPLE INTO YOUR MEMORY. We will use this over and over
     (and over) again.
 *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_SS : forall (n: nat) (H: ev' n), ev' (S (S n)).

(**
   - [ev'] is an inductive type that takes a nat and returns a prop.
   - [ev'_0] is a constructor that returns the proposition [ev' 0].
     We can read this as "I assert that 0 is even".
   - [ev'_SS] is a constructor that returns the proposition
     [forall (n : nat) (H : ev' n), ev' (S (S n))].
     We can read this as "Give me a natural number n and a proof that
     [ev' n] holds and I'll assert that ev' (S (S n)) holds."
   - Here's another way to write it.
 *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
(* different syntax for same concept *)
| ev_SS (n : nat) (H : ev n) : ev (S (S n)). 
                         


(** 
  - Question: why can't we write the following similar to list? 
*)
Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).

(**
  - Writing [(n: nat)] makes it a *global parameter* which means
    that the argument to [wrong_ev] has to be the same in all cases.
  - Writing [nat -> prop] makes it an *index* which means that the argument to
    [wrong_ev] can vary in each case. This notion of an index will be important
    for talking about dependent types.
 *)


(** 
   - Question: why did we not write [ev_SS: nat -> ev n -> ev (S (S n))]? 
 *)

Fail Inductive wrong_ev' : nat -> Prop :=
| wrong_ev'_0: wrong_ev' 0
| wrong_ev'_SS : nat -> wrong_ev' n -> wrong_ev' (S (S n)).

(**
  - Recall that "A -> B" is shorthand for [forall _: A, B].
  - In this case, we need the number "n".
  - This is an example of a _dependent type_, and we will discuss this
    more when we talk about the Curry-Howard isomorphism.   
 *)


Theorem ev_4:
  ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.    (* Question: forwards or backwards reasoning? *)
Qed.

Theorem ev_plus4 :
  forall (n: nat), ev n -> ev (4 + n).
Proof.
  intros n.
  simpl.
  intros Hn.
  apply ev_SS.
  apply ev_SS.
  apply Hn.
Qed.


(** ** Paper-Pencil Inference Rules *)

(**
   - What's the mental model for the proofs above?
   - Let's take a detour to paper-pencil *inference rules*, i.e., how we would do
     this without a proof assistant.
 *)


(** *** Inductively defined sets *)

(*
  We can define _inductively defined sets_ as follows:


    (Axiom)

                         (empty premise)
      ---------------    (name of rule)
          a \in S        (conclusion)

    This axiom asserts that the element a is always in the set S.


    (Inference Rule)


      a_1 \in S .... a_n \in S   (premise)
     --------------------------  (name of rule)
              a \in S            (conclusion)

    This inference rule asserts that if we can show that a_1 \in S, a_n \in S,
    then we can show that a \in S.

 *)


(** *** Example 1: Natural Numbers *)

(*
    Suppose we are trying to define the set of natural numbers nat.

    (Axiom)

                  
      --------------- O
        O \in nat    


    (Inference rule)

         n \in nat      
    ------------------ S
        S n \in nat       

 *)

Print nat.


(** *** Example 2: Lists *)

(*

    Suppose we are trying to define the set of lists of type X.

    (Axiom)

                      
      --------------- nil
       {} \in list(X)


    (Inference rule)

     x \in X   ls \in list(X) 
    ------------------------- cons
        {x, ls} \in list(X)
 *)

Print list.


(** *** Example 3: Even *)

(*
    (Axiom)

                 
      --------------- ev_O
          O \in ev


    (Inference rule)
  
          n \in ev      
    ------------------ ev_SS
      S (S (n)) \in ev  

 *)

Print ev.
(* notice we have Prop now! *)


Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.


(** *** Proof trees *)

(*

            ------ ev_0
             ev O
       ----------------- ev_SS
         ev (S (S (O)))
    ------------------------ ev_SS
      ev (S (S (S (S O))))

*)

(**
   - Question: why is this a tree?
   - Answer: eventually we may have rules that require multiple premises
     to be satisfied, in which case we will eventually get a tree out.
   - We will see an example of this later on.
 *)


(** ** Working with Inductive Propositions *)


(** *** Inversion on evidence *)

Theorem ev_inversion :
  forall (n: nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.

  (* Just like destruct on natural numbers or lists. *)
  destruct E.

  - (* E = ev_0 *)
    left.
    reflexivity.
  - (* E = ev_SS n *)
    right.
    exists n.
    split.
    reflexivity.
    apply E.
Qed.

(**
   - Theorems of this form are called _inversion_ lemmas.
   - Intuitively, it is saying that if we build a proof of [ev n],
     it must be constructed with informat either either from the
     premises of [ev_O] or [ev_SS].
   - What properties of inductive types does this remind you of?
 *)

Theorem evSS_ev :
  forall (n: nat),
    ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E. (* tactic [inversion] applies the inversion lemma and
                  removes trivial cases. For example, we know we cannot
                  be in the [ev_O] case. Why? *)
  apply H0.
Qed.


(** *** Induction on evidence *)

(**
   - Recall that all inductive types have an induction principle.
   - The same is true of inductive propositions.
 *)

Print ev_ind.


(**
   - We'll need some definitions from our previous lecture.
   - You can run [coqc lec_03_proof.v] to compile the previous lecture.
   - Now we can use it.
 *)
Require Import lec_03_proof.
Print lec_03_proof.


Lemma ev_even_ex :
  forall (n: nat),
    ev n -> is_even_ex n.
Proof.
  intros n E.
  
  (* We are performing induction on the evidence! *)
  induction E as [|n' E' IH].
  
  - (* E = ev_0 *)
    unfold is_even_ex.
    exists 0.
    reflexivity.
  - (* E = ev_SS n' E' with IH : Even E' *)
    unfold is_even_ex in IH.
    destruct IH as [k Hk].    
    unfold is_even_ex.    
    exists (S k). simpl.
    rewrite Hk.
    reflexivity.
Qed.


(** *** Picture of Proof

   - Let's go back to the proof tree view.
   - What happens after we do induction on ev?
 *)

(*
          -------------- ev_O or ev_SS
               ev n
    ----------------------------
       exists k, double k = n


    Case ev_O:

          -------------- ev_O
               ev O
    ---------------------------
       exists k, double k = O


    Case ev_SS:
           
     ------    -----------------------
      ev n'    exists m, double m = n'
    ----------------------------------- IH
       exists k, double k = S (S n')

 *)


(** ** Inductive Relations *)

(**
   - In the same way that we could define
 *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).


Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

(** *** Proof tree view *)
(*

    ----------- le_n
       3 <= 3
 *)


Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

(** *** Proof tree view *)
(*

    ----------- le_n
      3 <= 3
    ----------- le_S
      3 <= 4
    ----------- le_S
      3 <= 5
    ----------- le_S
      3 <= 6
 *)


Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H.
  inversion H.
  inversion H2.
Qed.
(** *** Proof tree view *)
(*

          ----------- (contradiction, neither le_n nor le_S apply, so we can't build this)
            2 <= 0
          ----------- le_S
            2 <= 1
    ----------------------- intros
      2 <= 1 -> 2 + 2 = 5

 *)



(** ** Arithmetic Expression Language *)

(**
   - Let's define a grammar for a small arithmetic language.
   - You may think of this as a simple calculator language.
 *)

Inductive exp : Set :=
| nat_exp: nat -> exp
| plus_exp: exp -> exp -> exp
| times_exp: exp -> exp -> exp.

Print exp_ind.


(** *** Inference rule view *)
(*

    ----------- nat_exp
     n \in exp


     e1 \in exp  e2 \in exp
    ------------------------ plus_exp
         e1 + e2 \in exp


     e1 \in \exp e2 \in exp
    ------------------------ times_exp
        e1 * e2 \in exp

 *)

(**
   - Right now it's just a bunch of syntax.
   - What about its semantics?
   - Let's define it as an inductive relation!
 *)
                  
Inductive exp_step : exp -> exp -> Prop :=
| plus_reduce :
  forall (n1 n2: nat),
    exp_step (plus_exp (nat_exp n1) (nat_exp n2)) (nat_exp (n1 + n2))
| plus_reduce_left :
  forall (e1 e2: exp),
    forall (e1': exp), exp_step e1 e1' ->
                       exp_step (plus_exp e1 e2) (plus_exp e1' e2)
| plus_reduce_right :
  forall (n: nat) (e2: exp),
    forall (e2': exp), exp_step e2 e2' ->
                       exp_step (plus_exp (nat_exp n) e2) (plus_exp (nat_exp n) e2')
| times_reduce :
  forall (n1 n2: nat),
    exp_step (times_exp (nat_exp n1) (nat_exp n2)) (nat_exp (n1 * n2))
| times_reduce_left :
  forall (e1 e2: exp),
    forall (e1': exp), exp_step e1 e1' ->
                       exp_step (times_exp e1 e2) (times_exp e1' e2)
| times_reduce_right :
  forall (n: nat) (e2: exp),
    forall (e2': exp), exp_step e2 e2' ->
                       exp_step (times_exp (nat_exp n) e2) (times_exp (nat_exp n) e2').

Print exp_step_ind.


(** *** Inference rule view *)
(*

    ---------------------- plus_reduce
     "n1 + n2" -> n1 + n2


            e1 -> e1'
    ------------------------ plus_reduce_left
     "e1 + e2" -> "e1' + e2"


            e2 -> e2'
    ------------------------ plus_reduce_right
      "n + e2" -> "n + e2'"


    ---------------------- times_reduce
      "n1 * n2" -> n1 * n2


            e1 -> e1'
    ------------------------ times_reduce_left
     "e1 * e2" -> "e1' * e2"


            e2 -> e2'
    ------------------------ times_reduce_right
       "n * e2" -> "n * e2'"

 *)


(**
   - Our first property of the step relation is progress: either we reduce to a
     natural number or there is a step that we can take.
   - We will prove this by induction on the structure of the expression [exp].
 *)

Theorem exp_progress:
  forall (e: exp),
  (exists (n: nat), e = nat_exp n) \/ exists e', exp_step e e'.
Proof.
  induction e.
  { (* nat_exp *)
    left.
    exists n.
    reflexivity.
  }
  { (* plus_exp *)
    destruct IHe1.
    destruct IHe2.
    - right.
      destruct H.
      destruct H0.
      rewrite H.
      rewrite H0.
      exists (nat_exp (x + x0)).
      apply plus_reduce.
    - right.
      destruct H.
      destruct H0.
      rewrite H.
      exists (plus_exp (nat_exp x) x0).
      apply plus_reduce_right.
      apply H0.
    - destruct H.
      destruct IHe2.
      right.
      destruct H0.
      exists (plus_exp x e2).
      apply plus_reduce_left.
      apply H.
      right.
      destruct H0.
      exists (plus_exp x e2).
      apply plus_reduce_left.
      apply H.
  }
  {
    destruct IHe1.
    destruct IHe2.
    - right.
      destruct H.
      destruct H0.
      rewrite H.
      rewrite H0.
      exists (nat_exp (x * x0)).
      apply times_reduce.
    - right.
      destruct H.
      destruct H0.
      rewrite H.
      exists (times_exp (nat_exp x) x0).
      apply times_reduce_right.
      apply H0.
    - destruct H.
      destruct IHe2.
      right.
      destruct H0.
      exists (times_exp x e2).
      apply times_reduce_left.
      apply H.
      right.
      destruct H0.
      exists (times_exp x e2).
      apply times_reduce_left.
      apply H.
  }
Qed.


(**
   - You might have noticed that we could have given alternative semantics.
   - In particular, why bother with an inductive proposition at all?
   - Here's a sneak peak.
 *)

Fixpoint eval_exp (e: exp) : option exp :=
  match e with
  | nat_exp n => Some (nat_exp n)
  | plus_exp e1 e2 =>
      match eval_exp e1, eval_exp e2 with
      | Some (nat_exp n1), Some (nat_exp n2) => Some (nat_exp (n1 + n2))
      | _, _ => None
      end
  | times_exp e1 e2 =>
      match eval_exp e1, eval_exp e2 with
      | Some (nat_exp n1), Some (nat_exp n2) => Some (nat_exp (n1 * n2))
      | _, _ => None
      end
  end.

(**
   - We might be interested in proving that such semantics are equivalent.
   - We'll save this for some other time.
 *)



(** ** The Curry Howard Correspondence *)


(** *** The analogy:

   propositions ~ types
   proofs       ~ data values

   In other words, "proving a theorem is the same as constructing a term
   of the appropriate type".
  
 *)


Print ev_4.

(**
   - A proof script is a more high-level way to build up a term of that type.
 *)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.


(** *** Forall/-> and functions *)


Theorem ev_plus4' :
  forall n,
    ev n -> ev (4 + n).
Proof.
  intros n H.
  simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4'': forall (n: nat), ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).


(** *** Conjunction and products *)

Print prod.

Theorem proj1' :
  forall P Q,
    P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP HQ].
  apply HP.
  Show Proof.
Qed.

Print conj.

Definition proj1'': forall P Q, P /\ Q -> P :=
  fun (P Q: Prop) =>fun (HPQ: P /\ Q) =>
    match HPQ with
    | conj HP _ => HP
    end.


(** *** Disjunction and sums *)

      
Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
  Show Proof.
Qed.

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.


(** *** Existentials  *)

Print ex_intro.

Check ex (fun n => ev n) : Prop.

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).


(** *** True/False *)

Print True.

Fact p_implies_true : forall P, P -> True.
Proof.
  intros.
  apply I.
  Show Proof.
Qed.

Definition p_implies_true': forall P, P -> True :=
  fun (P: Type) => fun (_ : P) => I.

Print False.

Fail Definition contra : False :=
  0 = 1.

Definition false_implies_zero_eq_one: False -> 0 = 1 :=
  fun contra => match contra with end.


(** *** Equality *)

Locate "=".

Print eq.

Lemma four: 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
  Show Proof.
Qed.

Print four.


(**
   - We might wonder if Coq's definition of equality is too restrictive.
   - It turns out that it is (logically) equvialent to Leibniz equality.
 *)


Lemma equality_implies_leibniz_equality : forall (X : Type) (x y: X),
  x = y -> forall P: X -> Prop, P x -> P y.
Proof.
  intros.
  rewrite <- H.
  assumption.
Qed.

Lemma leibniz_equality_implies_equality : forall (X : Type) (x y: X),
  (forall P: X -> Prop, P x -> P y) -> x = y.
Proof.
  intros.
  
  (* This part is the interesting bit of the proof *)
  specialize (H (fun z => x = z)).

  simpl in H.
  apply H.
  reflexivity.
Qed.


(** ** Summary

   - We saw inductively defined propositions, induction, and proof trees.
   - We introduced an arithmetic expression language and operational semantics.
   - We saw the  Curry-Howard isomorphism and equality as an inductive type.
 *)
