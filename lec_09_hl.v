(** * Hoare Logic and Axiomatic Semantics *)

From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.PeanoNat. Import Nat.

Require Import lec_08_imp.

(** ** References

  - https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html
  - https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html

 *)


(** ** Recap 

  - Last time we looked at the IMP programming language which introduced the
    concept of programming with state.
  - Thus we got a "language" for programming TMs.
  - We then introduced it's small-step (machine-like) and
    big-step (evaluation) semantics. These different styles of giving semantics:
    small-step and big-step semantics.
  - We did a formal proof that big-step evaluation was deterministic.
  - Today we will introduce _Hoare Logic_.
  - Along the way we will see a 3rd style of semantics: _axiomatic semantics_.
  - Finally we'll show how to verify programs.
 
 *)

(**
 *)


(** ** Goal for today

   - Introduce Hoare logic, including assertions and compositional rules
     (assignment, pre/post, skip, seq, if, while).
   - Introduce axiomatic semantics.
   - Show example program verifications with _decorated commands_.
   - Show how to extract verification conditions in an effort to automate
     verification.

 *)


(** ** Hoare Logic *)

(**
   - Up until now, we've proven properties of entire languages / machines.
   - What if we wanted to prove a property of a single program in a language?
   - This is where *Hoare Logic* comes in. Hoare Logic is a logic that is designed
     to prove properties of programs.
   - Hoare Logic (and separation logic) is an active area of research.
 *)



(** *** The Basic Idea 1: Make assertions *)
(*

   {{P}} c {{Q}}
*)

(** 
   - P is a *precondition*, i.e., true before we run c
   - c is a command in IMP or a program/algorithm
   - Q is a *postcondition*, i.e., true after we run c
 *)


(** *** The Basic Idea 2: Compositional *)
(*

    {{P}} c1 {{Q}}  {{Q}} c2 {{R}}
   -------------------------------- HoareSeq
          {{P}} c1; c2 {{R}}
*)

(**
   - For every construct in our language, we will have a corresponding set of 
     assertions that we can make about it.
   - In this manner, we can prove properties of programs by following the structure
     of the program.
   - 
 *)


(** *** So we need to define two things

   - an assertion language
   - structural proof rules
 *)


(** ** Assertions 

   - First we need to be able to make *assertions* about programs.
   - What could we possibly say about an IMP program?
   - Well IMP programs take states and transform them into states.
   - So perhaps we can make assertions about states.
 *)

Definition Assertion := state -> Prop.


(** *** Example 1
   
   [st X <= st Y]

   The valued stored at identifer X is less than the value stored at identifier Y.
 *)
Definition assn1 : Assertion :=
  fun st => st X <= st Y.


(** *** Example 2
   
   [st X = 3 \/ st X <= st Y]

   The valued stored at identifer X is either 3 or
   the value stored at identifier X is less than the value stored at identifier Y.
 *)
Definition assn2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.


(**
   - Thus we have a shallow embedding!
   - We could have a deep embedding if we reified the language of propositions
     for Hoare logic as an AST. But this would be a lot of work.
   - In this case it is simpler to do a shallow embedding.
   - The downside of a shallow embedding is that now we have the power of [Prop].
 *)


(** *** Example 3
   
   [st X = 3 -> st Y = 4]

   If the value stored at X is 3 then the value stored at Y is 4.
 *)
Definition assn3 : Assertion :=
  fun st => (fun st => st X = 3) st -> (fun st => st Y = 4) st.


(** ** Example 4
   
   [st X = 3 <-> st Y = 4]

   If the value stored at X is 3 iff the value stored at Y is 4.
 *)
Definition assn4 : Assertion :=
  fun st => (fun st => st X = 3) st <-> (fun st => st Y = 4) st.


(** *** Ignore me, notation for pretty assertions *)

(** *** Side Comment:
   - When working with shallow embeddings, it is useful to have powerful
     notation mechanisms.
   - In this case, we are going to use notation to make the shallowly-embedded
     assertion language as close to Coq's original syntax as possible.
 *)

Definition Aexp : Type := state -> nat.
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.
Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.
Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.
Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st -> assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <-> assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.


(** Lift predicate into assertion language. *)
Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

(** Lift 2-arity relation into assertion language. *)
Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).


(** *** Assertions *)

(**
   - Here are the previous examples with prettier notation.
   - Note that the quantification over state is implicit now.
 *)

Definition assn1' : Assertion :=
  X <= Y.

Definition assn2' : Assertion :=
  X = 3 \/ X <= Y.

Definition assn3' : Assertion :=
  X = 3 -> Y = 4.

Definition assn4' : Assertion :=
  X = 3 <-> Y = 4.


(** ** Hoare Triples *)


(** *** Hoare Triples

   [{{P}} c {{Q}}]

   - P is a _precondition_ and is written in our assertion language.
   - c is a command in IMP.
   - Q is a _postcondition_ and is written in our assertion language.

 *)

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
    st =[ c ]=> st' ->   (* as a reminder, this is big-step evaluation *)
    P st ->
    Q st'.

(**
   - Some notational support for writing Hoare Triples.
 *)
Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.


(** *** Example 1

   [{{X = 0}} X := X + 1 {{X = 1}}]

  - The command X := X + 1 transforms 
  - a state in which X = 0
  - to a state in which X = 1
 *)

Definition hex1 : Prop :=
  {{X = 0}} X := X + 1 {{X = 1}}.


(** *** Example 2

   [forall m, {{X = m}} X := X + 1 {{X = m + 1}}]

   - The command X := X + 1 transforms
   - a state in which X = m
   - to a state in which X = m + 1

   - Note that m is a Coq variable m and not an IMP variable.
   - This is possible because we have done a shallow embedding!
*)

Definition hex2 : Prop :=
  forall m, {{X = m}} X := X + 1 {{X = m + 1 }}.


(**
   - If Q holds, then it doesn't matter what P is.
 *)
Theorem hoare_post_true : forall (P Q : Assertion) (c: com),
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  apply H.
Qed.


(**
   - If P never holds, then it doesn't matter what Q is.
 *)
Theorem hoare_pre_false : forall (P Q : Assertion) (c: com),
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  specialize (H st).  
  contradiction.
Qed.


(** ** Compositional Proof Rules *)


(** *** The Basic Idea 2: Compositional *)
(*

    {{P}} c1 {{Q}}  {{Q}} c2 {{R}}
   -------------------------------- HoareSeq
          {{P}} c1; c2 {{R}}

   ... more rules mirror language constructs

 *)


(*** ** Assignment Proof Rules *)
 


(** *** Question: is this rule correct? *)
(*

   
   ---------------------------- HoareAsgnWrong
    {{ True }} X := a {{ X = a }}

 *)













(** *** Counter-example *)
(*

   ---------------------------- hoare_asgn_wrong
    {{True}} X := -X {{ X = -X }}
   
 *)

(** *** Actual rule *)
(*
   
   --------------------------------- hoare_asgn
    {{ Q[X |-> a] }} X := a {{ Q }}
 *)


(** *** Wait! That's backwards?
   
   - Upon first glance, this rule looks backwards.
   - If Q holds and I assign a to X, shouldn't the postcondition be
     Q with [X |-> a]?
   - As we saw with HoareAsgnWrong, this can't possibly hold because
     it doesn't hold when Q = True.
   - So let's reason backwards with what the rule is saying.
 *)


(** *** Wait! That's backwards? *)
(*   

  --------------------------------- HoareAsgnCorrect
    {{ Q[X |-> a] }} X := a {{ Q }}
*)

(**
   - Q holds after I run [X := a]
   - And so Q[X |-> a] should hold before I run [X := a]
   - Let's formalize this in Coq.
 *)

                                 
Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
Notation "P [ X ⊢> a ]" := (assn_sub X a P)
                             (at level 10, X at next level, a custom com).


Theorem hoare_asgn : forall Q X a,
  {{Q [X ⊢> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE; subst.
  unfold assn_sub in HQ.
  assumption.
Qed.


Example assn_sub_example :
  {{(X < 5) [X  ⊢> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.
Qed.
  


(** *** If you insist on a forward rule ... *)
(*

              st' = (X !-> m ; st)
  --------------------------------------------- HoareAsgnFwd
       {{fun st => P st /\ st X = m}} 
                   X := a
   {{fun st => P st' /\ st X = aeval st' a }}
 *)

Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X := a
  {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}.
Proof.
  unfold hoare_triple.
  intros.
  destruct H0; subst.
  split.
  {
    inversion H; subst.
    rewrite t_update_shadow.

    assert (forall (A: Type) (st: total_map A) X, (X !-> st X; st) = st).
    {
      From Coq Require Import Logic.FunctionalExtensionality.
      unfold t_update.
      intros.
      apply functional_extensionality.
      intros.
      unfold eqb_string.  
      remember (string_dec X x) as Eqb.
      destruct Eqb; subst; auto.
    }    
    rewrite H1.
    assumption.
  }
  {
    inversion H; subst.
    rewrite t_update_shadow.
    rewrite t_update_same.
    rewrite t_update_eq.
    reflexivity.
  }
Qed.


(** *** Consequence 
    
  - Sometimes, our pre-condition and post-conditions are not in the shape
    we want them to be.
  - There is a sound way to accomplish this with strengthening pre-conditions
    and weakening post-conditions.
  - First we need some notation for implication.
*)

Definition assert_implies (P Q : Assertion): Prop :=
  forall st, P st -> Q st.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.


(** *** Strengthening pre-conditions

      {{P'}} c {{Q}}  P ->> P'
   ----------------------------
          {{P}} c {{Q}}	
*)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) (c: com),
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp.
    assumption.
Qed.


(** *** Weakening post-conditions


     {{P}} c {{Q'}}    Q' ->> Q
   ------------------------------
         {{P}} c {{Q}}
*)


Theorem hoare_consequence_post : forall (P Q Q' : Assertion) (c: com),
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.



Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.


(** *** Skip *)
(*

     -------------------- hoare_skip
      {{ P }} skip {{ P }}
 *)

Theorem hoare_skip : forall P,
  {{P}} skip {{P}}.
Proof.
  intros P st st' H HP.
  inversion H; subst.
  assumption.
Qed.


(** *** Sequencing *)
(*

       {{ P }} c1 {{ Q }}   {{ Q }} c2 {{ R }}
    -------------------------------------------- hoare_seq
               {{ P }} c1; c2 {{ R }}
 *)

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.


Example hoare_asgn_ex2 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros a n.
  eapply hoare_seq.
  {
    (* right part of seq *)
    apply hoare_skip.
  }
  {
    (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assn_sub.
      unfold "->>".
      unfold t_update.
      intros.
      simpl in *.
      assumption.
  }
Qed.


(** *** If *)
(*

       {{ P /\ b }} c1 {{ Q }}   {{ P /\ ~b }} c2 {{ Q }}
    ------------------------------------------------------- hoare_if
               {{ P }} if b { c1 } { c2 } {{ Q }}
 *)


Definition bassn b : Assertion :=
  fun st => (beval st b = true).
Coercion bassn : bexp >-> Assertion.
Arguments bassn /.


Lemma bexp_eval_false : forall b st,
  beval st b = false ->
  ~ ((bassn b) st).
Proof.
  congruence.
Qed.
Hint Resolve bexp_eval_false : core.


Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.


(** *** While *)
(*

              {{P /\ b}} c {{P}}
      --------------------------------- hoare_while
      {{P} while b do c end {{P /\ ~b}}

 *)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* while b do c appears in the evaluation above the line and so needs to be remembered *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval; inversion Horig; subst.
  {
    (* while false *)
    eauto.
  }
  {
    (* while true *)
    eauto.
  }
Qed.


(** ** Axiomatic Semantics! *)


(** *** What if we gathered all the rules together?

  - We would get another method to give semantics to programs,
    i.e., *axiomatic semantics*.
  - This follows from the compositional design of Hoare Logic!
*)

(*

     ---------------------- hoare_skip
      {{ P }} skip {{ P }}


   --------------------------------- hoare_asgn
    {{ Q[X |-> a] }} X := a {{ Q }}


       {{ P }} c1 {{ Q }}   {{ Q }} c2 {{ R }}
    -------------------------------------------- hoare_seq
               {{ P }} c1;c2 {{ R }}


      {{ P /\ b }} c1 {{ Q }}   {{ P /\ ~b }} c2 {{ Q }}
   ------------------------------------------------------- hoare_if
            {{ P }} if b { c1 } { c2 } {{ Q }}


            {{P ∧ b}} c {{P}}
   ---------------------------------- hoare_while
    {{P} while b do c end {{P ∧ ~b}}


      {{P'}} c {{Q}}  P ->> P'
   ----------------------------- pre_strengthen
          {{P}} c {{Q}}


     {{P}} c {{Q'}}    Q' ->> Q
   ------------------------------ post_weaken
         {{P}} c {{Q}}
 *)


(** *** Example Verifications *)

Definition swap: com :=
  <{ Z := X;
     X := Y;
     Y := Z }>.

(** **** Goal: Swap is correct *)
(*
   {{X <= Y}}
      Z := X;
      X := Y;
      Y := Z 
   {{Y <= X}}
 *)

(** **** Step 1 *)
(*
      Z := X;
      X := Y;
      Y := Z 
   {{Y <= X}}
 *)

(** **** Step 2 *)
(*
      Z := X;   
      X := Y;
   {{Y <= X /\ Y = Z}}
      Y := Z 
   {{Y <= X}}
 *)

(** **** Step 3 *)
(*
      Z := X;   
   {{Y <= X /\ Y = Z /\ X = Y}}
      X := Y;
   {{Y <= X /\ Y = Z}}
      Y := Z 
   {{Y <= X}}
 *)

(** **** Step 4 *)
(*
   {{Y <= X /\ Y = Z /\ X = Y /\ Z = X}}
      Z := X;   
   {{Y <= X /\ Y = Z /\ X = Y}}
      X := Y;
   {{Y <= X /\ Y = Z}}
      Y := Z 
   {{Y <= X}}
 *)

(** **** Step 5 *)
(*
   {{X <= Y}}
      Z := X;   
   {{Y <= X /\ Y = Z /\ X = Y}}
      X := Y;
   {{Y <= X /\ Y = Z}}
      Y := Z 
   {{Y <= X}}
 *)

Theorem swap_is_correct :
  {{X <= Y}}
    swap
  {{Y <= X}}.
Proof.
  unfold swap.    
  eapply hoare_seq.
  {
    eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_asgn.
  }
  {
    unfold assn_sub.
    simpl. 
    unfold hoare_triple.
    intros.
    inversion H; subst; auto.
  }    
Qed.


(** *** Swapping is correct 2 *)


(** **** Program *)
(*
       X := X + Y;
       Y := X - Y;
       X := X - Y
 *)


(** **** Step 1 *)
(*
       X := X + Y;
       Y := X - Y;
       X := X - Y
     {{ X = n /\ Y = m }}
 *)


(** **** Step 2 *)
(*
       X := X + Y;
       Y := X - Y;
     {{ X - Y = n /\ Y = m }}       (assn_sub)
       X := X - Y
     {{ X = n /\ Y = m }}
 *)


(** **** Step 3 *)
(*
       X := X + Y;
     {{ X - (X - Y) = n /\ X - Y = m }}   (assn_sub)
       Y := X - Y;
     {{ X - Y = n /\ Y = m }}
       X := X - Y
     {{ X = n /\ Y = m }}
 *)


(** **** Step 4 *)
(*
     {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}  (assn_sub)
       X := X + Y;
     {{ X - (X - Y) = n /\ X - Y = m }}
       Y := X - Y;
     {{ X - Y = n /\ Y = m }}
       X := X - Y
     {{ X = n /\ Y = m }}
 *)


(** **** Step 5 *)
(*
     {{ X = m /\ Y = n }} ->>                                (weaken)
     {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
       X := X + Y;
     {{ X - (X - Y) = n /\ X - Y = m }}
       Y := X - Y;
     {{ X - Y = n /\ Y = m }}
       X := X - Y
     {{ X = n /\ Y = m }}
 *)

Definition swap': com :=
  <{ X := X + Y;
     Y := X - Y;
     X := X - Y }>.


Theorem swap_is_correct' :
  {{X <= Y}}
    swap
  {{Y <= X}}.
Proof.
  (** Exercise *)
Admitted.


(** *** Reduce to zero is correct *)

(**
   - We now try to verify programs with a while loop, which requires us to
     identify a **loop invariant**.
   - This is pretty tricky to do in general.
   - This mirrors the trickiness of figuring out what to perform induction on.
   - Luckily for us, this first example is quite easy to do.
 *)

(** **** Program *)
(*
       while ~(X = 0) do
         X := X - 1
       end
 *)


(** **** Step 1 *)
(*
       while ~(X = 0) do
         X := X - 1
       end
     {{ X = 0 }}
 *)


(** **** Step 2 *)
(*
       while ~(X = 0) do
         X := X - 1
       end
     {{ True ∧ ~(X <> 0) }} ->>   (weaken)
     {{ X = 0 }}
 *)


(** **** Step 3 *)
(*
       while ~(X = 0) do
         X := X - 1
       {{ True }}
       end
     {{ True ∧ ~(X <> 0) }} ->>   (weaken)
     {{ X = 0 }}
 *)


(** **** Step 4 *)
(*
       while ~(X = 0) do
       {{ True /\ X <> 0 }} ->>
       {{ True }}
         X := X - 1
       {{ True }}
       end
     {{ True ∧ ~(X <> 0) }} ->>   (weaken)
     {{ X = 0 }}

*)

Definition reduce_to_zero' : com :=
  <{ while ~(X = 0) do
       X := X - 1
       end }>.


Theorem reduce_to_zero_correct' :
  {{True}}
    reduce_to_zero'
  {{X = 0}}.
Proof.
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  - apply hoare_while.
    + (* Loop body preserves invariant *)
      (* Need to massage precondition before hoare_asgn applies *)
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * (* Proving trivial implication (2) ->> (3) *)
        unfold assn_sub.
        unfold "->>".
        simpl.
        intros.
        exact I.
  - (* Invariant and negated guard imply postcondition *)
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse.
    simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    Check eqb_eq.
    apply eqb_eq in GuardFalse.
    apply GuardFalse.
Qed.


(** *** More complex loop invariants *)


(** **** Program *)
(*
    {{ X = m /\ Y = n }}
      while ~(X = 0) do
        Y := Y - 1;
        X := X - 1
      end
    {{ Y = n - m }}

 *)


(** **** Step 1 *)
(*
      while ~(X = 0) do
        Y := Y - 1;
        X := X - 1
      end
    {{ INV /\ ~ (X ~= 0) }} ->>     (weaken)
    {{ Y = n - m }}

 *)

(** **** Step 2 *)
(*
      while ~(X = 0) do
        Y := Y - 1;
        X := X - 1
        {{ INV }}                        (while)
      end
    {{ INV /\ ~ (X ~= 0) }} ->>          (weaken)
    {{ Y = n - m }}

 *)

(** **** Step 3 *)
(*
      while ~(X = 0) do
        Y := Y - 1;
        {{ INV [X ⊢> X-1] }}             (assn)
        X := X - 1
        {{ INV }}                        (while)
      end
    {{ INV /\ ~ (X ~= 0) }} ->>          (weaken)
    {{ Y = n - m }}

 *)

(** **** Step 4 *)
(*
      while ~(X = 0) do
        {{ INV [X ⊢> X-1] [Y ⊢> Y-1] }}  (assn)
        Y := Y - 1;
        {{ INV [X ⊢> X-1] }}             (assn)
        X := X - 1
        {{ INV }}                        (while)
      end
    {{ INV /\ ~ (X ~= 0) }} ->>          (weaken)
    {{ Y = n - m }}

 *)

(** **** Step 5 *)
(*
      {{ INV }}                          (while)
      while ~(X = 0) do
        {{ INV /\ X ~= 0 }} ->>          (while + weaken)
        {{ INV [X ⊢> X-1] [Y ⊢> Y-1] }}  (assn)
        Y := Y - 1;
        {{ INV [X ⊢> X-1] }}             (assn)
        X := X - 1
        {{ INV }}                        (while)
      end
    {{ INV /\ ~ (X ~= 0) }} ->>          (weaken)
    {{ Y = n - m }}

 *)

(** **** Step 6 *)
(*
    {{ X = m /\ Y = n }} ->>             (pre)
    {{ INV }}                            (while)
      while ~(X = 0) do
        {{ INV /\ X ~= 0 }} ->>          (while + weaken)
        {{ INV [X ⊢> X-1] [Y ⊢> Y-1] }}  (assn)
        Y := Y - 1;
        {{ INV [X ⊢> X-1] }}             (assn)
        X := X - 1
        {{ INV }}                        (while)
      end
    {{ INV /\ ~ (X ~= 0) }} ->>          (weaken)
    {{ Y = n - m }}

 *)


(** **** Guess 1 *)
(*
    INV = True

    {{ X = m /\ Y = n }} ->>             
    {{ True }}                           
      while ~(X = 0) do
        {{ True /\ X ~= 0 }} ->>          
        {{ True [X ⊢> X-1] [Y ⊢> Y-1] }}  
        Y := Y - 1;
        {{ True [X ⊢> X-1] }}             
        X := X - 1
        {{ True }}                        
      end
    {{ True /\ ~ (X ~= 0) }} ->>          (broken)
    {{ Y = n - m }}

 *)

(** **** Guess 2 *)
(*
    INV = Y = n - m

    {{ X = m /\ Y = n }} ->>                   (broken)
    {{ Y = n - m }}                            
      while ~(X = 0) do
        {{ Y = n - m /\ X ~= 0 }} ->>          (broken)
        {{ Y = n - m [X ⊢> X-1] [Y ⊢> Y-1] }}
        Y := Y - 1;
        {{ Y = n - m [X ⊢> X-1] }}             
        X := X - 1
        {{ Y = n - m }}                        
      end
    {{ Y = n - m /\ ~ (X ~= 0) }} ->>          
    {{ Y = n - m }}

 *)


(** **** Guess 3 *)
(*
    INV = Y - X = n - m

    {{ X = m /\ Y = n }} ->>             
    {{  Y - X = n - m }}                           
      while ~(X = 0) do
        {{ Y - X = n - m /\ X ~= 0 }} ->>          
        {{ Y - X = n - m [X ⊢> X-1] [Y ⊢> Y-1] }}  
        Y := Y - 1;
        {{ Y - X = n - m [X ⊢> X-1] }}             
        X := X - 1
        {{ Y - X = n - m }}                        
      end
    {{ Y - X = n - m /\ ~ (X ~= 0) }} ->>          
    {{ Y = n - m }}

 *)


Definition slow_subtract : com :=
  <{ while ~(X = 0) do
      X := X - 1;
      Y := Y - 1
     end }>.

Theorem slow_subtract_correct:
  forall m n,
  {{ X = m /\ Y = n }}
    slow_subtract
  {{ Y = n - m }}.
Proof.
  (* Exercise! *)
Admitted.
    

(** ** Decorated Commands *)

(**
   - In working out the verification of individual programs, we found it
     useful to decorate every intermediate command with an assertion.
   - If we want to make this explict in Coq, we can define in inductive
     type that formalizes this idea: a **decorated command**.
 *)

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom) (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion).
         (* d ->> {{ Q }} *)
         

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.


(** *** Ignore me, notation *)

Declare Scope dcom_scope.
Notation "'skip' {{ P }}"
      := (DCSkip P)
      (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}"
      := (DCAsgn l a P)
      (in custom com at level 0, l constr at level 0,
          a custom com at level 85, P constr, no associativity) : dcom_scope.
Notation "'while' b 'do' {{ Pbody }} d 'end' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
           (in custom com at level 89, b custom com at level 99,
           Pbody constr, Ppost constr) : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}"
      := (DCIf b P d P' d' Q)
           (in custom com at level 89, b custom com at level 99,
               P constr, P' constr, Q constr) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (in custom com at level 12, right associativity, P constr) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (in custom com at level 10, right associativity, P constr) : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
      (in custom com at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (in custom com at level 91, P constr) : dcom_scope.
Open Scope dcom_scope.


(** *** Extracting Verification Conditions *)

(**
   - Intuitively, we should just be able to erase the decorations
     without changing the meaning of the program.
   - We can write a function that gets rid of all the decorations.
 *)

Fixpoint erase (d : dcom) : com :=
  match d with
  | DCSkip _ => CSkip
  | DCSeq d1 d2 => CSeq (erase d1) (erase d2)
  | DCAsgn X a _ => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (erase d1) (erase d2)
  | DCWhile b _ d _ => CWhile b (erase d)
  | DCPre _ d => erase d
  | DCPost d _ => erase d
  end.

Definition erase_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => erase d
  end.


(**
   - Here is the previous reduce to 0 example.
   - We have decorated it with all the intermediate propositions and shown
     that erasing the decorations gets us back the original program.
 *)

Example dec_while : decorated :=
  <{
  {{ True }}
  while ~(X = 0)
  do
    {{ True /\ (~ X = 0) }}
    X := X - 1
    {{ True }}
  end
  {{ True /\ X = 0}} ->>
  {{ X = 0 }} }>.

Example extract_while_ex :
  erase_dec dec_while = <{while ~ X = 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  reflexivity.
Qed.


(**
   - We also be able to obtain the post-condition and pre-condition of the
     entire program.
 *)

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq _ d2 => post d2
  | DCAsgn _ _ Q => Q
  | DCIf _ _ _ _ _ Q => Q
  | DCWhile _ _ _ Q => Q
  | DCPre _ d => post d
  | DCPost _ Q => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Example pre_dec_while : pre_dec dec_while = True.
Proof.
  reflexivity.
Qed.


Example post_dec_while : post_dec dec_while = (X = 0)%assertion.
Proof.
  reflexivity.
Qed.


Definition dec_correct (dec : decorated) :=
  {{pre_dec dec}} erase_dec dec {{post_dec dec}}.

Example dec_while_triple_correct :
  dec_correct dec_while
 = {{ True }}
   while ~(X = 0) do X := X - 1 end
   {{ X = 0 }}.
Proof.
  reflexivity.
Qed.


(** *** Verification Conditions *)

(**
   - Now for the real reason why we want decorated programs.
   - We can use our compositional proof-rules to construct an entire predicate
     that must be true of our entire program, the **verification conditions**.
   - This will enable us to automate proving properties of our programs.
 *)


Open Scope assertion_scope.
Open Scope hoare_spec_scope.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X ⊢> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d /\ b) ->> Pbody)%assertion
      /\ ((post d /\ ~ b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d /\ (post d ->> Q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d ->
  {{P}} erase d {{post d}}.
Proof.
  (* Why can we do induction on d? Compositional proof rules! *)
  induction d; intros; simpl in *.
  { (* Skip *)
    eapply hoare_consequence_pre.
      + apply hoare_skip.
      + assumption.
  }
  {
    (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      + apply IHd2. apply H2.
      + apply IHd1. apply H1.
  }
  { (* Asgn *)
    eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + assumption.
  }
  { (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse] ] ] ] ].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence; eauto.
      + eapply hoare_consequence; eauto.
  }
  { (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1 Hd] ] ].
    eapply hoare_consequence; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  }
  { (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre; eauto.
  }
  { (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post; eauto.
  }
Qed.


(** ** Summary 

   - We saw Hoare logic, including assertions and compositional rules
     (assignment, pre/post, skip, seq, if, while).
   - This gave us a third style of semantics: axiomatic semantics.
   - We saw example verifications of single programs.
   - Finally we saw how to extract verification conditions.

 *)
