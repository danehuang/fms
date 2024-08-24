(* ################################################################# *)
(** * CSC825: Logic and Computability *)

From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Require Import Maps.
Require Import Multi.
  

(** ** References

   - https://softwarefoundations.cis.upenn.edu/plf-current/Norm.html

 *)


(** ** Recap
   
   - Last time we finished off our section on types.
   - Today, we'll look into a powerful proof technique called _logical relations_.

 *)


(** ** Goal for today

  - Introduce the idea of _logical relations_, a powerful proof technique
     that can be used to obtain a stronger induction hypothesis.
   - This technique can be used to show that STLC is strongly normalizing,
     i.e., that every well-typed STLC term terminates.
   - We will also show how to use this technique to give another proof of
     type-soundness for STLC.
   - Along the way, we'll encounter many concepts we've seen throughout this
     class.

 *)


(** ** STLC Recap *)

(** *** Types *)

Inductive ty : Type :=
| Ty_Bool : ty                 (* Bool      *)
| Ty_Arrow : ty -> ty -> ty    (* T1 -> T2  *)
.

(** *** Terms *)

Inductive tm : Type :=
(* pure STLC *)
| tm_var : string -> tm               (* x             *)
| tm_app : tm -> tm -> tm             (* t1 t2         *)
| tm_abs : string -> ty -> tm -> tm   (* \x:T1, t      *)
(* booleans *)  
| tm_true : tm                        (* true          *)
| tm_false : tm                       (* false         *)
| tm_if : tm -> tm -> tm -> tm        (* if t1 t2 t3   *)
.

(** *** Notation *)

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
Notation "{ x }" := x (in custom stlc at level 1, x constr).
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom stlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom stlc at level 0).


(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{ \ y : T, t1 }> =>
      if eqb_string x y then t else <{ \y:T, [x:=s] t1 }>
  | <{t1 t2}> =>
      <{ ([x:=s]t1) ([x:=s]t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).


(** *** Values *)

Inductive value : tm -> Prop :=
| v_abs : forall x T2 t1,
    value <{\x:T2, t1}>                (* \x:T2, t1  *)
| v_true :
  value <{true}>                       (* true       *)
| v_false :
  value <{false}>                      (* false      *)
.
Hint Constructors value : core.


(** *** Small-Step Call-By-Value Semantics *)

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T2 t1 v2,
    value v2 ->
    <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
| ST_App1 : forall t1 t1' t2,
    t1 --> t1' ->
    <{t1 t2}> --> <{t1' t2}>
| ST_App2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    <{v1 t2}> --> <{v1 t2'}>
| ST_IfTrue : forall t1 t2,
    <{if true then t1 else t2}> --> t1
| ST_IfFalse : forall t1 t2,
    <{if false then t1 else t2}> --> t2
| ST_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').
Hint Constructors step : core.


(** *** Multi-Step Reduction *)

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


(** *** Normal Forms *)

Print normal_form.
Notation step_normal_form := (normal_form step).

(**
   - values cannot be reduced.
 *)
Lemma value__normal : forall t,
  value t ->
  step_normal_form t.
Proof.
  intros t H; induction H; intros [t' ST]; inversion ST; eauto.
Qed.

Hint Resolve value__normal : core.



(** *** Small-step reductoin is deterministic *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X,
    R x y1 ->
    R x y2 ->
    y1 = y2.

Lemma step_deterministic :
   deterministic step.
Proof with eauto.
   unfold deterministic.
   intros t t' t'' E1 E2.
   generalize dependent t''.
   
   induction E1; intros t'' E2.
   { (* ST_AppAbs *)
     inversion E2; subst; clear E2; eauto.
     - inversion H3.
     - exfalso; apply value__normal in H; eauto.
   }
   { (* ST_App1 *)
     inversion E2; subst; clear E2; eauto.
     - inversion E1.
     - f_equal; eauto.
     - exfalso; apply value__normal in H1; eauto.
   }
   { (* ST_App2 *)
     inversion E2; subst; clear E2; eauto.
     - exfalso; apply value__normal in H3; eauto.
     - exfalso; apply value__normal in H; eauto.
     - f_equal; eauto.
   }
   { (* ST_IfTrue *)
     inversion E2; subst; clear E2; eauto.
     - inversion H3.
   }
   { (* ST_IfFalse *)
     inversion E2; subst; clear E2; eauto.
     - inversion H3.
   }
   { (* ST_If *)
     inversion E2; subst; clear E2; eauto.
     - inversion E1.
     - inversion E1.
     - f_equal; eauto.
   }
Qed.


(** *** Typing Contexts *)

Definition context := partial_map ty.
Reserved Notation "Gamma '⊢' t '\in' T" (at level 40,
                                        t custom stlc, T custom stlc at level 0).

(** *** Typing Relation *)

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Gamma x T1,
    Gamma x = Some T1 ->
    Gamma ⊢ x \in T1
| T_Abs : forall Gamma x T1 T2 t1,
    (x |-> T2 ; Gamma) ⊢ t1 \in T1 ->
    Gamma ⊢ \x:T2, t1 \in (T2 -> T1)
| T_App : forall T1 T2 Gamma t1 t2,
    Gamma ⊢ t1 \in (T2 -> T1) ->
    Gamma ⊢ t2 \in T2 ->
   Gamma ⊢ t1 t2 \in T1
| T_True : forall Gamma,
    Gamma ⊢ true \in Bool
| T_False : forall Gamma,
    Gamma ⊢ false \in Bool
| T_If : forall t1 t2 t3 T1 Gamma,
    Gamma ⊢ t1 \in Bool ->
    Gamma ⊢ t2 \in T1 ->
    Gamma ⊢ t3 \in T1 ->
    Gamma ⊢ if t1 then t2 else t3 \in T1
where "Gamma '⊢' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.
Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.


(** ** Proof of preservation recap 

   - As a reminder, we needed several lemmas before we could prove
     preservation: taking a step preserves the type of a term.
   - We needed a weakening lemma and a substitution lemma.
*)

(** *** Weakening

    - We can always make t well-typed in a larger Γ'.
 *)
Lemma weakening : forall Gamma Gamma' t T,
  inclusion Gamma Gamma' ->
  Gamma ⊢ t \in T ->
  Gamma' ⊢ t \in T.
Proof.
  (*
      Proof:
      
      By induction on the typing derivation of Γ ⊢ t : T.
   *)
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using inclusion_update.
Qed.

Corollary weakening_empty : forall Gamma t T,
  empty ⊢ t \in T ->
  Gamma ⊢ t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.


(** *** Substitution

    - Substitution of a closed term preserves typing.
 *)
Lemma substitution_preserves_typing :
  forall Gamma x U t v T,
  (x |-> U ; Gamma) ⊢ t \in T ->
  empty ⊢ v \in U ->
  Gamma ⊢ [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma.
  generalize dependent T.

  (*
      Proof:
      
      By induction on the structure of terms. (Why?)
      The only two cases that are not straightforward are variables and abstraction.
   *)
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  { (* var *)
    rename s into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty.
      assumption.
    + (* x<>y *)
      apply T_Var.
      rewrite update_neq in H2; auto.
  }
  { (* abs *)
    rename s into y, t into S.
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5.
      assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
  }
Qed.

Theorem preservation : forall t t' T,
   empty ⊢ t \in T ->
   t --> t' ->
   empty ⊢ t' \in T.
Proof.
  intros t t' T HT.
  generalize dependent t'.
  remember empty as Gamma.

  (*
     Proof:

     By induction on the derivation of empty ⊢ t : T.
     The only non-trivial case is the application case.
   *)
  induction HT; intros t' HE; subst; inversion HE; subst; eauto; try inversion HT; eauto.
  { (* T_App *)
    inversion HE; subst; eauto.
    + (* ST_AppAbs *)
      eapply substitution_preserves_typing with T2; eauto.
      inversion HT1; subst; eauto.
  }
Qed.


(** ** Strong Normalization of Simply-Typed Lambda Calculus 

   - Our goal is to prove strong normalization (SN) of STLC.
   - Informally, this means that every term reduces to a value.

 *)

(** *** Halts or Strong Normalization *)

Definition halts (t:tm) : Prop :=
  exists t', t -->* t' /\ value t'.

(**
   - Clearly all values should halt.
 *)
Lemma value_halts : forall v,
  value v ->
  halts v.
Proof.
  intros v H.
  unfold halts.
  exists v.
  split.
  - apply multi_refl.
  - assumption.
Qed.

(** *** Ordinary Induction Fails

   - SN is not true of many languages such as those with recursion.
   - Nevertheless, it is still useful to study the proof of SN of STLC
     because all the techniques we've seen so far:
     - induction on terms
     - induction on types
     - induction on operational semantics
     - induction on typing derivation
     will fail.
 *)

(** *** Why do we need logical relations? Normalization Attempt *)

Lemma normalization_attempt: forall t T,
  empty ⊢ t \in T ->
  halts t.
Proof.
  intros t T Htyp.
  unfold halts.
  remember empty as Gamma.
  induction Htyp; eauto; subst.
  {
    inversion H.
    (*
       Horray!
     *)
  }
  { (** case T = t1 t2 *)
    destruct IHHtyp2; eauto.
    destruct IHHtyp1; eauto.
    (*
       Oh no, our inductive hypothesis doesn't seem to be
       strong enough here.

       Can you think of an example?
       (\x. x x) (\x. x x) (call-by-name)
     *)
    admit.
  }
  {
    destruct IHHtyp3; eauto.
    destruct IHHtyp2; eauto.
    destruct IHHtyp1; eauto.
    destruct H.
    destruct H0.
    destruct H1.
    (*
       Can use type-soundness here and other similar cases.
     *)
Abort.



(** *** What's the fix?

   - To prove SN, we will need to introduce a proof technique called
      _logical relations_ (technically we'll only need _logical predicates_).
   - Logical relations are an extremely powerful proof technique.
   - Before we can do introduce them, we will need to take a closer look
     at free variables and closed terms. As you might have guessed from the proof
     of preservation, the entire difficulty deals with free variables and closed
     terms.

 *)


(** *** Free Variables and Closed Terms *)

(** **** Free Variables

    - We've shown free variables as fix-points before using sets.
    - Here we're using an inductive definition.
    - This is a formalization choice.
    - The advantage of using an inductive definition is that we do
      not need extra properties of sets.
    - The disadvantage is that we cannot take advantage of computation.

 *)

Inductive appears_free_in : string -> tm -> Prop :=
(* pure STLC *)
| afi_var : forall (x : string),
    appears_free_in x <{ x }>
| afi_app1 : forall x t1 t2,
    appears_free_in x t1 ->
    appears_free_in x <{ t1 t2 }>
| afi_app2 : forall x t1 t2,
    appears_free_in x t2 ->
    appears_free_in x <{ t1 t2 }>
| afi_abs : forall x y T11 t12,
    y <> x ->
    appears_free_in x t12 ->
    appears_free_in x <{ \y : T11, t12 }>
(* booleans *)
| afi_test0 : forall x t0 t1 t2,
    appears_free_in x t0 ->
    appears_free_in x <{ if t0 then t1 else t2 }>
| afi_test1 : forall x t0 t1 t2,
    appears_free_in x t1 ->
    appears_free_in x <{ if t0 then t1 else t2 }>
| afi_test2 : forall x t0 t1 t2,
    appears_free_in x t2 ->
    appears_free_in x <{ if t0 then t1 else t2 }>
.
Hint Constructors appears_free_in : core.


(** **** Closed Term

    - A closed term is one with no free variables.
 *)
Definition closed (t:tm) : Prop :=
  forall x, ~ appears_free_in x t.


(** **** Context Invariance
   
   - For those variables that are free, we require that the
     different contexts assign the same types.
 *)
Lemma context_invariance : forall Gamma Gamma' t S,
  Gamma ⊢ t \in S ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  Gamma' ⊢ t \in S.
Proof.
  intros Gamma Gamma' t S Htyp HE.
  generalize dependent Gamma'.

  (*
      Proof:

      By induction on the derivation of Γ ⊢ t : T.
      The only non-trivial case is the abstraction case.
   *)
  induction Htyp; intros; eauto 12.
  { (*
        case t = x (automation fails in this case):
        
        It suffices to show Γ'(x) = T by T_Var.
        This follows by our assumption HE.
     *)
    apply T_Var.
    rewrite <- HE; auto.
  }
  { (*
       case t = \x: T2, t1 :

       It suffices to show Γ', x: T2 ⊢ t1 : T1 by T_Abs.
       By our inductive hypothesis, we can show
       (Γ', x: T2)(x1) = (Γ, x: T2)(x1) whenever x1 is free in t1.
       We proceed by case analysis on whether x = x1.
       
       Case x = x1:       
         If x = x1, then we need to show that T2 = T2 (by context lookup),
         which reflexively follows.

       Case x != x1:
         If x != x1, then we need to show that Γ'(x1) = Γ(x1).
         By HE, we can equivalently show that x1 is free in \x: T2, t1.
         This follows by definition of free variables for abstraction.
     *)
    apply T_Abs.
    apply IHHtyp.
    intros x1 Hafi.
    destruct (eqb_stringP x x1); subst.
    + rewrite update_eq.
      rewrite update_eq.
      reflexivity.
    + rewrite update_neq; [| assumption].
      rewrite update_neq; [| assumption].
      apply HE.
      apply afi_abs; assumption.      
  }
Qed.


(** **** Free in Context
   
   - For those variables that are free, we need to say that
     context lookup is successful.
 *)
Lemma free_in_context : forall x t T Gamma,
  appears_free_in x t ->
  Gamma ⊢ t \in T ->
  exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma Hafi Htyp.
  (*
     Proof:
     
     By induction on the derivation of Γ ⊢ t : T.
     The only non-trivial case is the abstraction case.
   *)

  induction Htyp; inversion Hafi; subst; eauto.
  {
    (*
       case t = \x0: T2, t1 :

       By inversion on appears_free_in x t, the only non-trivial case is
       when x0 != x.
       In this case, it suffices to show that there exists some T' such that
       Γ(x) = T'.
       By our inductive hypothesis, we have that there exists some T'
       such that (Γ, x0: T2)(x) = T'.
       Since x0 != x, we have that Γ(x) = T', so we have found such a T'.
     *)
    apply IHHtyp in H4; destruct H4 as [T' Hctx].
    exists T'.
    unfold update, t_update in Hctx.
    rewrite false_eqb_string in Hctx; eauto.
  }
Qed.


(**
   - A term typeable-in an empty context is closed.
 *)
Corollary typable_empty__closed :
  forall t T,
    empty ⊢ t \in T ->
    closed t.
Proof.
  intros.
  unfold closed.
  intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  discriminate C.
Qed.


(** ** Logical Relations 

   - Now that we have defined close terms we can finally define
     logical relations.
   - We will define the relation R by structural induction on types.
 *)

(*
   R_{Bool}(t)     := empty ⊢ t: Bool ∧ ∃v. t -->* v

   R_{T1 -> T2}(t) := empty ⊢ t: T1 -> T2 ∧ ∃v. t ->* v ∧
                      ∀ s. R_{T1}(s) -> R_{T2}(t s)

*)
Fixpoint R (T:ty) (t:tm) : Prop :=
  empty ⊢ t \in T /\
  halts t /\
  (
    match T with
    | <{ Bool }> =>
        True
    | <{ T1 -> T2 }> =>
        (forall s, R T1 s -> R T2 <{t s}>)

    end
  ).

(** *** Strategy

   - Once we have defined the logical relation R, we will prove strong normalization
     of STLC in two steps.

   1. empty ⊢ t: T -> R_{T}(t)
   2. R_{T}(t) -> halts(t)

 *)

(** *** Step 2

   - It is trivial to show that being in the relation R implies that the
     term t halts.
   - Indeed, we baked in that t being in R means that it must halt.
   - We show step 2 now.
 *)
Lemma R_halts : forall {T} {t},
  R T t ->
  halts t.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [_ [H _]]; assumption.
Qed.


(** 
   - Another easy lemma.
 *)
Lemma R_typable_empty : forall {T} {t},
  R T t ->
  empty ⊢ t \in T.
Proof.
  intros.
  destruct T; unfold R in H; destruct H as [H _]; assumption.
Qed.


(** *** Step 1

    - We now turn our attention to proving Step 1.
    - We'll need a series of technical lemmas
      1. forwards/backwards reduction preserves R
      2. the *fundamental* lemma.
 *)


(** *** Forwards and Backwards Reduction

   - We first need a lemma that shows that taking a step
     preserves halting, in both directions.
 *)

Lemma step_preserves_halting :
  forall t t',
    (t --> t') ->
    (halts t <-> halts t').
Proof.
  intros t t' ST.
  unfold halts.
  split.
  {
    (* halts t => halts t' *)
    intros [t'' [STM V]].
    destruct STM.
    + (**
         case multi_refl:         
       *)
      exfalso. apply value__normal in V; eauto.
    + (**
         case multi_step:

         This uses step_deterministic!
       *)
      rewrite (step_deterministic _ _ _ ST H).
      exists z.
      split; assumption.
  }
  {
    (* halts t' => halts t *)
    intros [t'0 [STM V]].
    exists t'0.
    split; eauto.
  }
Qed.


(** *** Forward Reduction preserves R *)
Lemma step_preserves_R : forall T t t',
  (t --> t') ->
  R T t ->
  R T t'.
Proof.
  (* Question: what do we do induction on? *)







  
  
 induction T; intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt]].
 {
   (*
      Case T = Bool:
    *)
   split.
   eapply preservation; eauto.
   split.
   apply (step_preserves_halting _ _ E); eauto.
   auto.
 }
 {
   (*
      Case T = T1 -> T2:
    *)
   split.
   eapply preservation; eauto.
   split.
   apply (step_preserves_halting _ _ E); eauto.
   intros.
   eapply IHT2.
   apply ST_App1.
   apply E.
   apply RRt; auto.
 }
Qed.


Lemma multistep_preserves_R : forall T t t',
  (t -->* t') ->
  R T t ->
  R T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  {
    assumption.
  }
  {
    apply IHSTM.
    eapply step_preserves_R.
    apply H.
    assumption.
  }
Qed.


(** *** Backward Reduction preserves R 

  - This lemma is admittedly a bit weird!?
  - But we'll need it.

*)

Lemma step_preserves_R' : forall T t t',
  empty ⊢ t \in T ->
  (t --> t') ->
  R T t' ->
  R T t.
Proof.
  induction T; intros t t' HTyp E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
     destruct Rt as [typable_empty_t [halts_t RRt]].
  { (*
       Case T = bool:
     *)
    repeat split; auto.
    apply (step_preserves_halting _ _ E); eauto.
  }
  {
    (*
       Case T = T1 -> T2:
     *)
    repeat split; auto.
    + apply (step_preserves_halting _ _ E); eauto.
    + intros.
      eapply IHT2; eauto.
      eapply T_App; eauto. 
      eapply R_typable_empty; eauto.      
  }
Qed.


Lemma multistep_preserves_R' : forall T t t',
  empty ⊢ t \in T ->
  (t -->* t') ->
  R T t' ->
  R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
  {
    (*
       Case multi_refl:
     *)
    assumption.
  }
  {
    (*
       Case multi_step:
     *)
    eapply step_preserves_R'.
    assumption.
    apply H.
    apply IHSTM.
    eapply preservation; eauto.
    auto.
  }
Qed.


(** *** Step 1, First Attempt
 
   - We might be tempted now to prove step 1 directly.
   - But we'll see that we get stuck in the lambda abstraction case.
 *)
Lemma step_1_try : forall T t,
  empty ⊢ t \in T ->
  R T t.
Proof.
  intros T t H.
  remember empty as Gamma.
  induction H; subst.
  {
    inversion H.
  }
  {
    (* Oh no, stuck here! *)
    admit.
  }
  {
    apply IHhas_type1; auto.
  }
  {
    unfold R.
    repeat split; eauto.
    unfold halts.
    exists <{ true }>.
    split; eauto.
  }
Abort.


(** *** The Fundamental Lemma

   - Like our proof of preservation, we need a stronger lemma
     that talks about arbitrary contexts.
   - In particular, we need to show that
    
    Fundamental Lemma:
    Γ ⊢ t: T -> γ ⊧ Γ -> R_{T}(γ(t))

    where

    1. The environment γ maps variables to terms.
    2. γ ⊧ Γ means that the environment γ and the context Γ contain the same
       variables at the appropriate types.
    3. γ(t) is notation for substitute all of the free-variables in t with the
       terms in γ.
      
   - As you might have guessed, we need to show a lot of lemmas about
     multi-substitutions now.

*)


(** *** Multi-substitutions *)


(** *** Environments γ
   
   - We will model environment's γ as lists of pairs.
 *)
Definition env := list (string * tm).


(** *** γ(t)
   
   - We will now need to define multi-substitution.

 *)

Fixpoint msubst (ss:env) (t:tm) : tm :=
  match ss with
  | nil => t
  | ((x,s)::ss') => msubst ss' <{ [x:=s]t }>
  end.


(** *** Contexts Γ
   
   - We will model type contexts Γ as lists of pairs.
   - Previously we used the functional dictionary.
   - Here we use this so that we can match the structure of our environments.

 *)

Definition tass := list (string * ty).

Fixpoint mupdate (Gamma : context) (xts : tass) :=
  match xts with
  | nil => Gamma
  | ((x,v)::xts') => update (mupdate Gamma xts') x v
  end.


(** *** Some Generic Functions on List Environments *)

Fixpoint lookup {X:Set} (k : string) (l : list (string * X)) : option X :=
  match l with
    | nil => None
  | (j,x) :: l' =>
      if eqb_string j k then Some x else lookup k l'
  end.

Lemma mupdate_lookup : forall (c : tass) (x:string),
  lookup x c = (mupdate empty c) x.
Proof.
  induction c; intros.
  auto.
  destruct a.
  unfold lookup, mupdate, update, t_update.
  destruct (eqb_string s x); auto.
Qed.


Fixpoint drop {X:Set} (n:string) (nxs:list (string * X)) : list (string * X) :=
  match nxs with
  | nil => nil
  | ((n',x)::nxs') =>
      if eqb_string n' n
      then drop n nxs'
      else (n',x)::(drop n nxs')
  end.

Lemma mupdate_drop : forall (c: tass) Gamma x x',
  mupdate Gamma (drop x c) x'
    = if eqb_string x x' then Gamma x' else mupdate Gamma c x'.
Proof.
  induction c; intros.
  - destruct (eqb_stringP x x'); auto.
  - destruct a. simpl.
    destruct (eqb_stringP s x).
    + subst. rewrite IHc.
      unfold update, t_update. destruct (eqb_stringP x x'); auto.
    + simpl. unfold update, t_update. destruct (eqb_stringP s x'); auto.
      subst. rewrite false_eqb_string; congruence.
Qed.


(** *** A Series of Substitution Lemmas 

   - Substitution of variables might feel like an intuitive concept, but
     it is the heart of logic + programming.
   - All the properties of capture-avoid substitution need to be
     proved.
   - All the issues with proofs of meta-theoretic properties either
     work or break due to variables.
*)


(** 

   - Substitution of a variable that is not free is idempotent.
   
   [x := t']t = t whenever x ∉ fv(t)

 *)
Lemma vacuous_substitution : forall t x,
  ~ appears_free_in x t ->
 forall t', <{ [x:=t']t }> = t.
Proof.
  (*
     Proof: 

     Note that even though appears_free_in is inductively defined,
     it is negated so we cannot perform induction on it.
     By induction on the structure of terms!
   *)
  
  induction t; intros; simpl.
  { (* case t = x: *)
    destruct (eqb_stringP x s); subst; auto.
    unfold not in H.
    exfalso.
    apply H.
    auto.
  }
  { (* case t = t1 t2: *)
    assert (~ appears_free_in x <{ t1 }> ) by eauto.
    assert (~ appears_free_in x <{ t2 }> ) by eauto.
    eapply IHt1 in H0; eauto.
    eapply IHt2 in H1; eauto.
    rewrite H1.
    rewrite H0.
    reflexivity.
  }
  { (* case t = \x: T, t: *)
    destruct (eqb_stringP x s); subst; auto.
    simpl.
    rewrite IHt; eauto.
  }
  { (* case t = true: *)
    reflexivity.
  }
  { (* case t = false: *)
    reflexivity.
  }
  { (* case t = if t1 then t2 else t3 *)
    assert (~ appears_free_in x <{ t1 }> ) as H1 by eauto.
    assert (~ appears_free_in x <{ t2 }> ) as H2 by eauto.
    assert (~ appears_free_in x <{ t3 }> ) as H3 by eauto.
    eapply IHt1 in H1; eauto.
    eapply IHt2 in H2; eauto.
    eapply IHt3 in H3; eauto.
    rewrite H1.
    rewrite H2.
    rewrite H3.
    reflexivity.
  }
Qed.


(*
    - Substitution is always idempotent on a closed term.
 *)
Lemma subst_closed: forall t,
  closed t ->
  forall x t', <{ [x:=t']t }> = t.
Proof.
  intros.
  apply vacuous_substitution.
  apply H.
Qed.

(*
    - Substitution of a closed term for a variable eliminates
      all mentions of that variable.
 *)
Lemma subst_not_afi : forall t x v,
  closed v ->
  ~ appears_free_in x <{ [x:=v]t }>.
Proof.
  (*
     Proof:

     By induction on the structure of terms.
   *)
  unfold closed, not.
  induction t; intros x v P A; simpl in A.
  {
    (* case t = x: *)
     destruct (eqb_stringP x s); eauto.
     inversion A; subst. auto.
  }
  {
    (* case t = t1 t2: *)
    inversion A; subst; eauto.
  }
  {
    (* case t = \x: T, t *)
     destruct (eqb_stringP x s); eauto.
     + inversion A; subst; eauto.
     + inversion A; subst; eauto.
  }
  {
    (* case t = true: *)
    inversion A.
  }
  { (* case t = false: *)
    inversion A.
  }
  {
    (* case t = if t1 then t2 else t3 *)
    inversion A; subst; eauto.
  }
Qed.


(**
   - Once we substitute away a variable with a closed term,
     we substitution with that variable is idempotent.
 *)
Lemma duplicate_subst : forall t' x t v,
  closed v ->
  <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
Proof.
  intros.
  eapply vacuous_substitution.
  apply subst_not_afi.
  assumption.
Qed.


(**
   - We can commute the order of substitution if the variables we are
     substituting away are distinct.
 *)
Lemma swap_subst : forall t x x1 v v1,
  x <> x1 ->
  closed v ->
  closed v1 ->
  <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
Proof.
  (*
      Proof:

      By induction on the structure of terms.
   *)
 induction t; intros; simpl.
  { (* case t = x: *)
    destruct (eqb_stringP x s); destruct (eqb_stringP x1 s).
    + subst.
      exfalso; eauto.
    + subst.
      simpl.
      rewrite <- eqb_string_refl.
      apply subst_closed; eauto.
    + subst.
      simpl.
      rewrite <- eqb_string_refl.
      rewrite subst_closed; eauto.
    + simpl.
      rewrite false_eqb_string; eauto.
      rewrite false_eqb_string; eauto.
  }
  { (* case t = t1 t2: *)
    rewrite IHt1; eauto.
    rewrite IHt2; eauto.
  }
  { (* case t = \x: T, t *)
    destruct (eqb_stringP x s); destruct (eqb_stringP x1 s); subst.
    + contradiction.
    + simpl.
      rewrite <- eqb_string_refl.
      destruct (eqb_stringP x1 s); auto; try contradiction.
    + simpl.
      rewrite <- eqb_string_refl.
      destruct (eqb_stringP x s); auto; try contradiction.
    + simpl.
      destruct (eqb_stringP x s); auto; try contradiction.
      destruct (eqb_stringP x1 s); auto; try contradiction.
      assert (x1 <> x) by auto.
      rewrite IHt; eauto.
  }
  { (* case t = true *)
    reflexivity.
  }
  { (* case t = false *)
    reflexivity.
  }
  { (* case t = if t1 then t2 else t3 *)
    rewrite IHt1; eauto.
    rewrite IHt2; eauto.
    rewrite IHt3; eauto.
  }
Qed.


(** *** A Series of Multi-Substitution Lemmas 

    - Similar to the lecture on type inference, we'll need to extend
      lemmas on substitutions to multi-substitutions.
*)


(**
   - Multi-substitutions in a closed term are idempotent, i.e.,
     
     γ(t) = t whenever t is closed.
 *)
Lemma msubst_closed:
  forall t, closed t ->
  forall ss, msubst ss t = t.
Proof.
  induction ss.
  reflexivity.
  destruct a.
  simpl.
  rewrite subst_closed; assumption.
Qed.


(** *** Closed Environments *)
(*

    ---------------------
       closed_env empty

        closed t   closed_env ρ
    ------------------------------
       closed_env (ρ, x: t)
 *)

Fixpoint closed_env (env:env) :=
  match env with
  | nil => True
  | (x,t)::env' => closed t /\ closed_env env'
  end.


(** *** Substitution Commutes? *)
(*

     γ([x := v]t) = [x := v]((γ\x)(t)) whenever v and γ are closed.

     (γ\x) means remove x from γ.
 *)

Lemma subst_msubst: forall env x v t,
 closed v ->
 closed_env env ->
 msubst env <{ [x:=v]t }> = <{ [x:=v] { msubst (drop x env) t } }> .
Proof.
  induction env0; intros; auto.
  destruct a.
  simpl.
  inversion H0.
  destruct (eqb_stringP s x).
  - subst. rewrite duplicate_subst; auto.
  - simpl. rewrite swap_subst; eauto.
Qed.


(** *** Instantiations *)

(** **** Linking Concrete Environments with Contexts

   - Similar to how we needed a store typing to connect the types at
     locations with a concrete store, we'll need *instantiations* to
     connect concrete environments with typing contexts.

 *)


(** **** γ ⊧ Γ
   
   - We define instantiations inductively now.
*)
(*

   ------------------ V_nil
      empty ⊧ empty

      value v   γ ⊧ Γ   v ∈ R_{T}(v)
   ----------------------------------- V_cons
            γ, x: v ⊧ Γ, x: T

 *)

Inductive instantiation : tass -> env -> Prop :=
| V_nil :
  instantiation nil nil
| V_cons : forall x T v c e,
  value v ->
  R T v ->
  instantiation c e ->
  instantiation ((x,T)::c) ((x,v)::e).


(** **** "Subtyping" *)
(*

   (γ, x: v) ⊧ (Γ, x: T) ->
   γ ⊧ Γ
   
   We'll need this in lambda abstraction case.

 *)

Lemma instantiation_drop : forall c env,
  instantiation c env ->
  forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e V.
  induction V.
  {
    intros. simpl. constructor.
  }
  {
    intros. unfold drop.
    destruct (eqb_string x x0); auto.
    constructor; eauto.
  }
Qed.


(** **** Domains Match

   - If γ ⊧ Γ then every variable in Γ corresponds to a value in γ.
 *)
Lemma instantiation_domains_match: forall {c} {e},
  instantiation c e ->
  forall {x} {T},
    lookup x c = Some T ->
    exists t, lookup x e = Some t.
Proof.
  intros c e V. induction V; intros x0 T0 C.
  inversion C.
  simpl in *.
  destruct (eqb_string x x0); eauto.
Qed.


(**
   - If γ ⊧ Γ then γ is a closed environment.
   - This makes sense: every value bound in γ satisfies R_{T} at
     the appropriate type, so it should be closed.
 *)
Lemma instantiation_env_closed : forall c e,
  instantiation c e ->
  closed_env e.
Proof.
  intros c e V; induction V; intros.
  {
    econstructor.
  }
  {
    unfold closed_env.
    fold closed_env.
    split; [|assumption].
    eapply typable_empty__closed.
    eapply R_typable_empty; eauto.
  }
Qed.


(**
   - If γ ⊧ Γ then the domains of Γ and γ and every value in γ is
     in R_{T} at the appropriate type T.
   - This is a combination of [instantiation_domain_closed] and 
     [instantiation_env_closed].
 *)
Lemma instantiation_R : forall c e,
  instantiation c e ->
  forall x t T,
    lookup x c = Some T ->
    lookup x e = Some t ->
    R T t.
Proof.
  intros c e V. induction V; intros x' t' T' G E.
  {
    inversion G.
  }
  {
    unfold lookup in *.
    destruct (eqb_string x x').
    + inversion G; inversion E; subst; eauto.
    +  eauto.
  }
Qed.


(** *** Preservation of Types under Substitution

    - If γ ⊧ Γ and Γ ⊢ t: S then Γ ⊢ γ(t): S.
    - As we we might expect, it uses the lemma we used for preservation:
      that substitution preserves typing.
 *)
Lemma msubst_preserves_typing : forall c e,
  instantiation c e ->
  forall Gamma t S, (mupdate Gamma c) ⊢ t \in S ->
    Gamma ⊢ { (msubst e t) } \in S.
Proof.
  induction 1; intros.
  {
    simpl in H. simpl. auto.
  }
  {
    simpl in H2. simpl. 
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
  }
Qed.


(** ** Back to the Fundamental Lemma 

   Reminder of the proof strategy of strong-normalization of STLC.
   1.  empty ⊢ t: T -> R_{T}(t)
   2.  R_{T}(t) -> halts(t)
    
   - 2 was easy because we baked in the condition into R_{T}.
   - We got stuck on 1, which is we needed to prove a stronger
     statement called the *Fundamental Lemma*:
     
     Γ ⊢ t: T -> γ ⊧ Γ -> R_{T}(γ(t))

   - 1 is a consequence of the Fundamental Lemma.
   - To prove the Fundamental Lemma, we will need several congruence 
     lemmas that look very similar to the ones we used for showing
     normalization of a language without functions.
   - You don't get something for nothing! We are proving something
     stronger and so we should expect that we also need to prove
     something similar as well.

*)

(** *** Familiar congruence lemmas *)

Lemma multistep_App2 : forall v t t',
  value v ->
  (t -->* t') ->
  <{ v t }> -->* <{ v t' }>.
Proof.
  intros v t t' V STM.
  induction STM; eauto.
Qed.

Lemma multistep_IfTrue : forall t2 t2' t3,
  t2 -->* t2' ->
  <{ if true then t2 else t3 }> -->* <{ t2' }>.
Proof.
  intros t2 t2' t3 STM.
  induction STM; eauto.
Qed.

Lemma multistep_IfFalse : forall t2 t3 t3',
  t3 -->* t3' ->
  <{ if false then t2 else t3 }> -->* <{ t3' }>.
Proof.
  intros t2 t2' t3 STM.
  induction STM; eauto.
Qed.


(** *** A series of msubst lemmas per constructor 

   - When proving normalization of the arithmetic language, we did
     not have functions and variables.
   - Hence, we did not need these substitution lemmas below.
   - We now get to use all the work that we did on substitutions
     and instantiations.
*)


(**  
     γ(x) = γ[x]  when x is in γ
          = x     otherwise  
*)
Lemma msubst_var: forall ss x,
 closed_env ss ->
   msubst ss (tm_var x) =
   match lookup x ss with
   | Some t => t
   | None => tm_var x
  end.
Proof.
  induction ss; intros; auto.
  destruct a.
  simpl.
  destruct (eqb_string s x).
  apply msubst_closed.
  inversion H; auto.
  apply IHss.
  inversion H; auto.
Qed.


(* γ(\x: T, t) = \x: T, (γ\x)(t) *)
Lemma msubst_abs: forall ss x T t,
  msubst ss <{ \ x : T, t }> = <{ \x : T, {msubst (drop x ss) t} }>.
Proof.
  induction ss; intros; auto.
  destruct a.
  simpl.
  destruct (eqb_string s x); simpl; auto.
Qed.


(* γ(t1 t2) = γ(t1) γ(t2) *)
Lemma msubst_app : forall ss t1 t2,
  msubst ss <{ t1 t2 }> = <{ {msubst ss t1} ({msubst ss t2}) }>.
Proof.
 induction ss; intros; auto.
 destruct a.
 simpl.
 rewrite <- IHss.
 auto.
Qed.

(* γ(true) = true *)
Lemma msubst_true: forall ss,
  msubst ss <{ true }> = <{ true }>.
Proof.
  induction ss; intros; auto.
  destruct a.
  simpl.
  assumption.
Qed.

(* γ(false) = false *)
Lemma msubst_false: forall ss,
  msubst ss <{ false }> = <{ false }>.
Proof.
  induction ss; intros; auto.
  destruct a.
  simpl.
  assumption.
Qed.

(* γ(if t1 then t2 else t3) = if γ(t1) then γ(t2) else γ(t3) *)
Lemma msubst_if: forall ss t1 t2 t3,
  msubst ss <{ if t1 then t2 else t3 }> = <{ if {msubst ss t1} then {msubst ss t2} else {msubst ss t3} }>.
Proof.
  induction ss; intros; auto.
  destruct a.
  simpl.
  rewrite IHss.
  reflexivity.
Qed.


(** *** The Fundamental Lemma *)
(*
    Γ ⊢ t: T -> γ ⊧ Γ -> R_{T}(γ(t))
*)

Lemma msubst_R : forall c env t T,
  (mupdate empty c) ⊢ t \in T ->
  instantiation c env ->
  R T (msubst env t).
Proof.
  intros c env0 t T HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember (mupdate empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c). {
    intros. rewrite HeqGamma. rewrite mupdate_lookup. auto.
  }
  clear HeqGamma.
  generalize dependent c.

  (* By induction on the Typing Derivation *)
  induction HT; intros.
  {    
    (*          Γ(x) = T
       case  --------------- T_Var
                Γ ⊢ x: T

       We need to show R_{T}(γ(x)).
       Equivalently, we need to show 
       1. empty ⊢ γ(x) : T
       2. halts γ(x).

       Since γ ⊧ Γ, we have that γ(x) satisfies R_{T}(x) by instantiation_R.
       Thus this proves 1 and 2.
     *)
    rewrite H0 in H.
    destruct (instantiation_domains_match V H) as [t P].
    eapply instantiation_R; eauto.
    rewrite msubst_var.
    + rewrite P. auto.
    + eapply instantiation_env_closed; eauto.
  }
  {
    (*           Γ, x: T2 ⊢ t1 : T1
       case  --------------------------- T_Abs
              Γ ⊢ \x: T2, t1: T2 -> T1

       We need to show R_{T2 -> T1}(γ(\x: T2, t1)).
       Equivalently we need to show R_{T2 -> T1}(\x: T2, (γ\x)(t1)).
     *)
    rewrite msubst_abs.
    
    (* 
        First we show an intermediate fact:

        empty ⊢ \x : T2, (γ\x)(t1) : T2 -> T1

        This follows by all the properties of γ we have established before.
     *)
    assert (WT : empty ⊢ \x : T2, {msubst (drop x env0) t1 } \in (T2 -> T1) ).
    { eapply T_Abs.
      eapply msubst_preserves_typing.
      {
        eapply instantiation_drop; eauto.
      }
      eapply context_invariance.
      {
        apply HT.
      }
      intros.
      unfold update, t_update. rewrite mupdate_drop. destruct (eqb_stringP x x0).
      + auto.
      + rewrite H.
        clear - c n. induction c.
        simpl. rewrite false_eqb_string; auto.
        simpl. destruct a. unfold update, t_update.
        destruct (eqb_string s x0); auto.
    }

     (*        
       We equivalently show 
       1. empty ⊢ \x: T2, (γ\x)(t1) : T2 -> T1
       2. halts (\x: T2, (γ\x)(t1))
       3. R_{T2}(s) -> R_{T1}((\x: T2, (γ\x)(t1)) s) for any s.
     *)
    unfold R. fold R. split.
    {
      (*
         This follows by the intermediate fact.
       *)
      auto.
    }
    split.
    {
      (*
         A lambda is a value and values halt.
       *)
      apply value_halts.
      apply v_abs.
    }
    {
      (*
         All the hard work we put into setting up the logical relation
         comes down to making the proof work in item 3.
       *)
      intros.

      (*          
          We have that R_{T2}(s) so we know that there is some value v that
          s -->* v.
          By forward reduction, we have that R_{T2}(v).
       *)
      destruct (R_halts H0) as [v [P Q]].
      pose proof (multistep_preserves_R _ _ _ P H0).

      (*
         We now need to show that R_{T1}(\x: T2, (γ\x)(t1)).
         This holds by backward reduction!
       *)
      apply multistep_preserves_R' with (msubst ((x,v)::env0) t1).
      {
        eapply T_App. eauto.
        apply R_typable_empty; auto.
      }
      {
        eapply multi_trans.
        eapply multistep_App2; eauto.
        eapply multi_R.
        simpl.
        rewrite subst_msubst.
        eapply ST_AppAbs; eauto.
        eapply typable_empty__closed.
        apply (R_typable_empty H1).
        eapply instantiation_env_closed; eauto.
      }
      eapply (IHHT ((x,T2)::c)).
      intros. unfold update, t_update, lookup.
      destruct (eqb_string x x0); auto.
      constructor; auto.
    }
  }
  {
    (*         Γ ⊢ t1 : T2 -> T1    Γ ⊢ t2 : T2
       case  ------------------------------------ T_App
                      Γ ⊢ t1 t2: T1

       We need to show R_{T1}(γ(t1 t2)).

       By msubst_app, we can equivalently show R_{T1}(γ(t1) γ(t2))
       This follows by our induction hypothesis.
       
       Note: this is where we got stuck last time!
       This case is now trivially solved by our inductive hypthesis.
       All the "pain" was transferred to the lambda case.
     *)
    rewrite msubst_app.
    destruct (IHHT1 c H env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c H env0 V) as P2.
    fold R in P1. auto.
  }
  {
    (*         
       case  ------------------- T_True
               Γ ⊢ true : Bool

       We need to show R_{Bool}(γ(true)).
       Equivalently, we need to show 
       1. empty ⊢ γ(true) : Bool
       2. halts γ(true).
     *)
    simpl.
    repeat split; auto.
    + (*
         Item 1 follows because γ substitution preserves typing.
       *)
      eapply msubst_preserves_typing; eauto.
    + (*
         Item 2 follows because γ(true) = true is a value and values halt.
       *)
      apply value_halts.
      rewrite msubst_true.
      auto.
  }
  {
    (*         
       case  -------------------- T_False
               Γ ⊢ false : Bool

       We need to show R_{Bool}(γ(false)).
       Equivalently, we need to show 
       1. empty ⊢ γ(false) : Bool
       2. halts γ(false).       
     *)
    simpl.
    repeat split; auto.
    + (*
         Item 1 follows because γ substitution preserves typing.
      *)
      eapply msubst_preserves_typing; eauto.
    + (*
         Item 2 follows because γ(false) = false is a value and values halt.
       *)
      apply value_halts.
      rewrite msubst_false.
      auto.
  }
  {
     (*         Γ ⊢ t1 : Bool   Γ ⊢ t2 : T   Γ ⊢ t3 : T   
       case  -------------------------------------------- T_If
                    Γ ⊢ if t1 then t2 else t3 : T
     *)
    rewrite msubst_if.
    (* Exercise *)
    admit.
  }
Admitted.


(** *** Finally Strong Normalization 

   Putting the pieces together
   1.  empty ⊢ t: T -> R_{T}(t)
   2.  R_{T}(t) -> halts(t)

*)

Theorem normalization :
  forall t T,
    empty ⊢ t \in T ->
    halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  apply (@R_halts T).
  apply (msubst_R nil); eauto.
  eapply V_nil.
Qed.



(** ** Type-Safety Using Logical Relations *)


(** *** Types *)
(*

  V[Bool] := {true, false}
  
  V[T1 -> T2] := { \x:T1, t | ∀ v ∈ V[T1], [x := v]t ∈ V[T2] }

*)

Print normal_form.

(** *** Logical Relation *)
(*
  
  E[T] := { t | ∀ t', t -->* t' /\ normal_form(t) -> t' ∈ V[T] }
   
 *)

(** *** Safety *)
(*

  safe(t) := ∀ t', t -->* t' -> value t' \/ ∃ t''. t' --> t''
   
 *)


(** *** Proof Setup *)
(*

   1. empty ⊢ t: T -> t ∈ E[T]
   2. t ∈ E[T] -> safe(t)
   

   Γ ⊢ t: T -> γ ⊧ Γ -> γ(t) ∈ E_{T}
   
 *)


(** ** Summary

   - We introduced the idea of _logical relations_, a powerful proof technique
     that can be used to obtain a stronger induction hypothesis.
   - We saw how this technique can be used to show that STLC is strongly normalizing,
     i.e., that every well-typed STLC term terminates.

 *)
