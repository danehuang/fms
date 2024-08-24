(** * Proofs *)

(** ** References

   - https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html
   - https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html
 *)

(** ** Recap

  - Last time, we got a crash course in functional programming in Coq.
  - This enables us to define data-structures and write computations on them.
  - Today, we'll look more into the language of propositions [Prop] in Coq
    and how to prove theorems via _forward_ and/or _backward_ reasoning.
  - We'll take a closer look at _constructive logic_ vs. _classical logic_.
 *)

(** ** Goal for today

  - Look at _forward_ and/or _backward_ reasoning.
  - Introduce the language of [Prop].
  - Introduce _constructive logic_ vs. _classical logic_.
*)



(** ** Propositions in Coq *)


(**
   - The type of logical claims in Coq is [Prop].
 *)
    
Check (0 = 0).

Check (forall n m: nat, n + m = m + n).


(**
   - Any term with the type [Prop] is a syntactically well-formed proposition.
   - But note that the proposition may not be provable.
 *)

Check (1 = 2).

Check (forall n: nat, n + n = 0).


(**
   - We use the proof environment to try to prove that propositions are true.
 *)

Check (2 + 2 = 4).

Theorem thm_2_plus_2_eq_4 :
  2 + 2 = 4.
Proof.
  simpl.
  reflexivity.
Qed.


(**
   - Here's a hint ahead to the Curry-Howard isomorphism.
   - Recall that every term in Coq has a type.
   - What's the type of [thm_2_plus_2_eq_4]?
 *)

Check thm_2_plus_2_eq_4.
Print thm_2_plus_2_eq_4.



Check (2 + 2 = 4).

Definition prop_2_plus_2_eq_4: Prop := 2 + 2 = 4.

Check prop_2_plus_2_eq_4.

Theorem thm_2_plus_2_eq_4': prop_2_plus_2_eq_4.
Proof.
  reflexivity.
Qed.


Check thm_2_plus_2_eq_4.


(**
   - We can define functions in Coq that return propositions.
 *)

Definition is_two (n: nat): Prop :=
  n = 2.

Check is_two.


(**
   - We can even define recursive functions in Coq that return propositions.
   - We'll talk more about this later.
 *)

Fixpoint is_even (n: nat): Prop :=
  match n with
  | O => True
  | S O => False
  | S (S n') => is_even n'
  end.

(**
   - You might be wondering what the difference between [Prop] and [boolean] is.
   - We'll get to this later.
 *)

Fixpoint is_evenb (n: nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => is_evenb n'
  end.



(** ** Forwards and Backwards Reasoning *)


(*

    - HA   -------- H1
    A       A -> B
    ---------------- apply H1    -------- H2
           B                      B -> C
    ---------------------------------------- apply H2
                      C

 *)

Theorem backwards_ex:
  forall (A B C: Prop),
    (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C.
  intros H1.
  intros H2.
  intros HA.  (* question: is the type of HA [Prop] or [A]? *)
  apply H2.   (* notice how we apply matches the goal and replaces
                 it with the hypothesis *)
  apply H1.   (* same *)
  apply HA.   (* same, but not hypothesis so we're done *)
Qed.

(** *** Prose

   - Show that C holds whenever A, A -> B, and B -> C hold (for any A, B, C).
   - Because B -> C, it suffices to show that B holds. (apply H2)
   - Because A -> B, it suffices to show that A holds. (apply H1)
   - We have that A holds by assumption and so we are done. (apply HA)
 *)


(*

    --- HA   -------- H1
     A        A -> B
   -------------------- apply H1 in HA in HB    --------- H2
             B                                    B -> C
   ---------------------------------------------------------- apply H2 in HB as HC
                                C
 *)

Theorem forwards_ex:
  forall (A B C: Prop),
    (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C H1 H2.
  intros HA.
  apply H1 in HA as HB.  (* supply HA to H1 *)
  apply H2 in HB as HC.  (* supply HB with H2 *)
  apply HC.              (* supply HC to the goal *)
Qed.

Print forwards_ex.

(** *** Prose

   - Show that [C] holds whenever [A], [A -> B], and [B -> C] hold
     (for any A, B, C).
   - Because we have [A] and [A -> B] by assumption, we can derive
     that [B] holds.
   - Combining this with [B -> C], we can derive that [C] holds, which
     is what we wanted to show.
 *)


(**
   - Backwards reasoning is more common in Coq.
   - But it's important to keep in mind that both are valid forms of
     reasoning.
   - Discussion point for class: which style of reasoning do you find
     more natural, forwards or backwards? 
 *)


(**
   - Key takeaway: [apply] is the tactic that lets you go forwards/backwards.
 *)


Theorem forwards_and_backwards:
  forall (A B C: Prop),
    (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C H1 H2.
  intros HA.  
  apply H2.               (* backwards *)
  apply H1 in HA as HB.   (* forwards *)
  assumption.             (* another tactic [assumption], which proves the
                             goal if an assumption matches the goal. *)
Qed.


(** ** Reasoning about data constructors *)

(** 
  - We've seen several examples of inductive data-types: bools, natural numbers,
    pairs, and lists.
  - We also saw that every inductive data-type had an induction principle.
  - This induction principle enables us to prove properties 
*)

Print bool_ind.
Check nat_ind.
Print prod_ind.
Check list_ind.


(** 
  - The next step is to learn about *disjointness* and *injectivity* of inductive
    datatypes.
  - Disjointness means that distinct cases of an inductive datatype can never be equal.
    If we ever find ourselves in a situation where this is the case, then we have
    a contradiction.
  - Injectivity, or one-to-one, means f x = f y -> x = y.
  - Let's start with disjointness.
 *)

Theorem discriminate_ex1 :
  false = true ->
  2 + 2 = 5.
Proof.
  intros Hcontra.
  
  (* This tactic "enforces" the disjointness of inductive datatypes *)
  discriminate Hcontra.
Qed.

Theorem discriminate_ex2 :
  forall n: nat,
    S n = O ->
    2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.


Require Import Coq.Lists.List.

Theorem discriminate_ex3 :
  forall (X: Type) (x: X) (xs: list X),
    x :: xs = nil ->
    2 + 2 = 5.
Proof.
  intros X x xs contra.
  discriminate contra.
Qed.


(** 
  - You may be wondering how Coq deals with False and contradictions.
  - More on this later when we introduce classical vs. constructive logic.
  - For now, back to injectivity.
 *)


Theorem S_injective:
  forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H1.

  (**
     - What proof strategy would you use to try to prove this?
     

















   *)

  (* Assert enables us to prove a lemma within a lemma. *)
  assert (H2: n = pred (S n)). 
  {
    reflexivity.
  }
  rewrite H2.
  rewrite H1.
  simpl.
  reflexivity.
Qed.


(**
   - Can we repeat a similar argument for lists?
 *)

Theorem cons_injective:
  forall (X: Type) (xs ys: list X) (x y: X),
    x :: xs = y :: ys ->
    xs = ys.
Proof.
  intros X xs ys x y H1.
  assert (H2: xs = tail (x :: xs)).
  {
    reflexivity.
  }
  rewrite H1 in H2.
  rewrite H2.
  simpl.
  reflexivity.
Qed.

(**
   - We've proven disjointness and injectivity in Coq.
   - But one thing you may be wondering about, and bothered by, is why
     is injectivity true?
   - For example, there are many different representations of natural
     numbers, real numbers, etc, as inductive datatypes.
   - Couldn't it be the case that some representations are redundant and
     injectivity might fail?
   - The key thing to remember, what we're dealing with here is _syntax_,
     i.e., the syntax is unique. The semantics may not be.
 *)


(** ** Strengthening Inductive Hypothesis *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_fail:
  forall (n m: nat),
    double n = double m -> n = m.
Proof.
  intros.
  induction n.
  {
    simpl in H.
    destruct m.
    - reflexivity.
    - discriminate H.
  }
  {
    (* stuck, we need forall m! *)
Abort.






















Theorem double_injective:
  forall (n m: nat),
    double n = double m -> n = m.
Proof.
  (* removed intros  *)
  intros n.
  induction n.
  {
    intros m H.
    simpl in H.
    destruct m.
    + simpl.
      reflexivity.
    + simpl in H.
      discriminate H.
  }
  {
    intros m H.
    destruct m.
    + simpl in H.
      discriminate H.
    + apply f_equal.  (* strip away S *)
      apply IHn.
      simpl in H.
      injection H as H2.  (* use injectivity *)
      trivial.            
  }
Qed.


(**
   - Question: would this proof change if we defined double to be 2 * n?
   - Why or why not?
 *)


(** ** Logical connectives in Coq *)

(**
   - We've seen how to use the keyword [Inductive] to build up
     complex data-types.
   - We then defined functions on those data-types and proved
     properties about them.
   - Now we'll look into how to build up complex propositions
     with logical connectives.
   - We've already seen an example of a logical connective [->].
 *)


(** *** Implication *)

Locate "->".

(**
   - So anytime we have seen A -> B we could have replaced it with forall _: A, B.
   - In other words, implication is *syntactic sugar*.
   - Mathematical language: A if B translates to B -> A 
   - We'll talk more about -> after we talk about negation.
 *)


(** *** Conjunction *)

(**
   - A and B is True if both A is True and B is True.
   - "A and B" is called a *conjunction*.
 *)

Print and.

Example and_ex1:
  True /\ True.
Proof.
  split.  (* [split] takes a conjunction and "breaks" it into the components *)
  - trivial.
  - trivial.
Qed.

Example and_ex2:
  2 + 2 = 4 /\ 2 * 2 = 4.
Proof.
  split.  (* tactic [split] takes a conjunction and breaks it into 2 subgoals *)
  - (* 2 + 2 = 4 *)
    reflexivity.
  - (* 2 * 2 = 4 *)
    reflexivity.
Qed.

Lemma and_intro:
  forall A B: Prop,
    A ->
    B ->
    A /\ B.
Proof.
  intros A B HA HB. (* note that HA: A and not HA: Prop.
                       We'll get to this later. *)
                    (* Similar for HB: B. *)
  split.
  - (* A *)
    apply HA.
  - (* B *)
    apply HB.
Qed.


(** 
    - If we think of currying, we might think that [and_intro'] is also true.
    - Indeed it is, and so maybe [and_intro] isn't that exciting.
 *)

Lemma and_intro':
  forall A B: Prop,
    A /\ B ->
    A /\ B.
Proof.
  intros A B HAB.
  split.
  - (* A *)
    destruct HAB as [HA HB].
    apply HA.
  - (* B *)
    destruct HAB as [HA HB].
    apply HB.
Qed.

Theorem and_assoc:
  forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros.
  destruct H.
  destruct H0.
  split.
  - split; assumption.
  - assumption.
Qed.
    

(**
   - With conjunction and implication, we can define *logical equivalence* *iff*.
 *)

Locate "<->".
Print iff.


(** *** Disjunction *)

Print or.

Example or_ex1:
  True \/ False.
Proof.
  left.  (* [left] is a tactic that selects the left branch of or *)
  trivial.
Qed.

Example or_ex2:
  False \/ True.
Proof.
  right.  (* [right] is similar to left *)
  trivial.
Qed.

Example or_ex3:
  2 + 2 = 4 \/ 2 * 2 = 5.
Proof.
  left.
  simpl.
  reflexivity.
Qed.


(**
   - Let's explore the language of propositions in Coq a bit more.
   - We'll start with the two simplest: [True] and [False].
 *)


(** *** True *)


Lemma True_is_true1:
  True.
Proof.
  trivial.   (* For once, trivial is acceptable as a proof step. *)
Qed.

Print True.

(** 
  - Yes, even [True] is an inductive type in Coq.
  - It has one construct [I].
  - By disjointness and injectivity, [I] is the unique *inhabitant* of the type [Prop].
 *)

Lemma True_is_true2:
  True.
Proof.
  apply I.
Qed.


(** *** False *)

Print False.

(** 
  - [False] is an inductive type in Coq as well.
  - And it has no constructors!
  - This is a good thing: we better not be able to construct
    [False] propositions.
 *)

Lemma False_implies_anything:
  forall (P: Prop),
    False -> P.
Proof.
  intros P HFalse.
  destruct HFalse.
Qed.

(**
   - In Latin, the phrase "ex falso quodlibet" means
     "from falsehood follows whatever you like".
   - We can now define logical negation in Coq.
 *)


(** *** Negation *)


Print not.
Locate "~".

Lemma contradiction_implies_anything:
  forall (P: Prop),
    P /\ ~ P -> P.
Proof.
  unfold not.
  intros P Hcontra.
  destruct Hcontra.

  (* [exfalso] tactic for changing the goal to False *)
  exfalso.
  
  apply H0.
  assumption.
Qed.



Theorem double_negation1:
  forall (P: Prop),
    P -> ~ ~ P.
Proof.
  unfold not.
  intros.
  apply H0.

  (* apply H works equally well here *)
  assumption.  
Qed.

Theorem double_negation2:
  forall (P: Prop),
    ~ ~ P -> P.
Proof.
  unfold not.
  intros.
  exfalso.
  apply H.
  intros.
  apply H.
  intros.
  
  (* Hmmm ... *)
Abort.

Theorem contrapositive:
  forall (P Q: Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

(**
   - Quick check: did we do forwards or backwards reasoning?
   - Can you do the proof using the other direction?
 *)


(** *** Existential Quantification *)

Print is_even.

(** 
   - Another way to formalize [is_even] with existential quantification.
   - We'll use it to make a point later on Propositions vs. booleans.
 *)

Print double.

Definition is_even_ex (n: nat): Prop := exists m: nat, double m = n.

Theorem ten_is_even_ex:
  is_even_ex 10.
Proof.
  unfold is_even_ex.
  exists 5.  (* tactic [exists] requires us to supply a *witness* 5 *)
  simpl.
  reflexivity.
Qed.

(** 
  - Unlike [forall] where we could assume an arbitrary x, [exists]
    requires us to supply a specific witness.  
  - At this point, for those of us who have studied first-order logic or
    propositional logic, we may wonder if some of the logical connectives are
    extraneous.
  - For example, do we really need conjunction if we have disjunction
    and negation? Do we need existential quantification if we have forall
    and negation?
 *)


(**
  - not (A + B) = not A * not B
 *)

Theorem demorgan_works:
  forall (A B: Prop),
    ~ (A \/ B) <-> ~A /\ ~B.
Proof.
  unfold not.
  split.
  {
    intros.
    split.
    - intros.
      apply H.
      left.
      assumption.
    - intros.
      apply H.
      right.
      assumption.
  }
  {
    intros.
    destruct H.
    destruct H0.
    - apply H.
      assumption.
    - apply H1.
      assumption.
  }   
Qed.

(**
  - not (A * B) = not A + not B
 *)
Theorem demorgan_stuck:
  forall (A B: Prop),
    ~ (A /\ B) <-> ~A \/ ~B.
Proof.
  split.
  {
    unfold not.
    intros.
  (* Stuck, can't get A and B at the same time *)
Abort.

(**
   - What about [forall] and [exists]?
   - Classically, we might expect that 
     [~ forall x, P x <-> exists x, ~ P x].
   - This is not provable in Coq either. Coq is an example of a _constructive logic_.
   - Before we can talk about the difference between constructive and classical logic,
     we need to dive more into the difference between booleans and propositions.
 *)


(** ** Propositions vs. Booleans *)

Print True.
Print False.
Print bool.

(** 
  - At this point, you may be wondering what the difference between
    [Prop] and [bool] is.
  - This is a good thing to be wondering about!
  - If they are indeed the same thing, then we've just duplicated all our work.
  - If they are indeed different, then what exactly is the difference?
  - This is something good to wonder about, and we will need a formalization
    of an idea called a _Turing machine_ to be able talk about a concept called
    _decidability_.
  - For now, we will only be able to talk about _decidability_ informally.
    In essence, a proposition is decidable if there is an "algorithm" that
    can determine if the proposition holds or not. Booleans, by contrast,
    are always produced by computations, and consequently, decidable by
    construction.
 *)

(** 
   - It's best to see this difference via an example.
 *)

Print is_even.

Print is_even_ex.

Print is_evenb.

Theorem ten_thousand_is_even:
  is_even 10000.
Proof.
  reflexivity.
Qed.

Theorem ten_thousand_is_even_ex':
  is_even_ex 10000.
Proof.
  unfold is_even_ex.
  exists 5000.
  simpl.
  reflexivity.
Qed.

Theorem ten_thousand_is_evenb:
  is_evenb 10000 = true.
Proof.
  reflexivity.
Qed.

(**
   - Did you see the difference?
   - The reflexivity in [ten_thousand_is_even] needed to execute
     the fixpoint to produce [Prop].
   - The reflexivity in [ten_thousand_is_even_ex'] needed to check
     eq_refl on [5000].
   - The refelxivity in [ten_thousan_is_evenb] needed to check
     [eq_refl] on [true]. The fixpiont was run on natural numbers to
     produce bool.
   - In many practical developments, we may need to pay attention to
     how we formalize our statements to make sure that our proof checker
     can check our proofs!
   - There are at least two interesting extensions of this idea.
   - We'll go over one now called proof by _computational reflection_.
     (The other one is related and is called _translation validation_,
      and we'll go over it if we have time.)
 *)

(* helper lemma 1 *)
Theorem even_S :
  forall n : nat,
    is_evenb (S n) = negb (is_evenb n).
Proof.
  induction n.
  - simpl.
    reflexivity.
  - rewrite IHn.
    Search negb.
    rewrite Bool.negb_involutive.
    simpl.
    reflexivity.
Qed.

(* helper lemma 2 *)
Lemma even_double_conv:
  forall n, exists k,
    n = if is_evenb n then double k else S (double k).
Proof.
  induction n.
  {
    exists 0.
    simpl.
    reflexivity.
  }
  {
    rewrite even_S.
    destruct (is_evenb n).
    simpl.
    destruct IHn.
    + exists x.
      rewrite H.
      reflexivity.
    + simpl.
      destruct IHn.
      {
        exists (S x).
        rewrite H.
        destruct x.
        - simpl.
          reflexivity.
        - simpl.
          reflexivity.
      }
  }
Qed.

(* helper lemma 3 *)
Lemma even_double :
  forall k: nat, is_evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(* The theorem we actually care about. *)
Theorem even_computational_reflection:
  forall n: nat,
    is_evenb n = true <-> is_even_ex n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - unfold is_even_ex. 
    intros [k Hk]. rewrite <- Hk. apply even_double.
Qed.


(** ** Constructive Logic vs. Classical Logic *)

(**
   - Certainly, this must be true ....
 *)

Definition excluded_middle :=
  forall (P : Prop),
    P \/ ~ P.

(**
   - This holds in classical logic.
   - Not so in constructive logic.
   - The following restricted form does hold on decidable propositions.
 *)

Theorem restricted_excluded_middle :
  forall (P: Prop) (b: bool),
    (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.


(**
   - Logic's that do not assume excluded middle are called _constructive logics_.
   - The idea is that we actually need to construct a proof or a counterexample.
   - This has implications for proof by contradiction. In particular, we can
     really only use it when the proposition we're proving is decidable.
   - _Law of excluded middle_ is consistent with Coq's logic so we can add it
     when necessary.
   - Law of excluded middle is interprovable with _double negation elimination_.
   - There's obviously a whole lot more that can be said about constructive vs.
     classical logic, but I hope you're starting to see some of the
     interconnections between constructive logic and computation!
 *)


(** *** Functional Extensionality *)

(**

   f(x) = x + 1
   g(x) = -1 + x + 1

   for any input i give both f and g, it gives me the same outputs
*)


(** 
    - Question: how do we define equivialence of functions?
 *)













(**
   - It's common to say that f = g if forall x, f x = g x.
   - This principle is called *functional extensionality*.
   - We might wonder if this is true in Coq.
   - The converse is true.
 *)

Theorem functional_extensionality_converse:
  forall (X Y: Type) (f g: X -> Y),
    f = g -> (forall (x: X), f x = g x).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.


Theorem functional_extensionality:
  forall (X Y: Type) (f g: X -> Y),
    (forall (x: X), f x = g x) -> f = g.
Proof.
  intros.
  (* stuck *)
Abort.

(**
   - Functional extensionality is not provable in Coq.
   - We can always add it as an axiom, however, because it is known to be consistent with Coq's logic.
 *)

Axiom functional_extensionality:
  forall (X Y: Type) (f g: X -> Y),
    (forall (x: X), f x = g x) -> f = g.

Theorem why_isnt_this_provable:
  forall (n: nat),
    (fun m: nat => m + n) = (fun m: nat => n + m).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  Search "_ + _".
  apply PeanoNat.Nat.add_comm.
Qed.

Print Assumptions why_isnt_this_provable.


(** ** Summary

  - We saw the language of propositions [Prop] in Coq.
  - We introduced some differences between constructive logic
    and classical logic.
 *)
