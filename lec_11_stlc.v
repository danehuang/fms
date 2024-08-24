(** * Simply-Typed Lambda Calculus *)

From Coq Require Import Strings.String.
Require Import Maps.
Require Import Multi.

(** ** References

   - https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html
   - https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html

 *)

(** ** Recap

  - Last time, we introduced Lambda Calculus, a theory of
    "substitution".
  - In particular, we saw that *capture-avoid substitution* was
    the appropriate notion of substitution.
  - We then gave two semantics for Lambda Calculus: call-by-value
    and call-by-name and saw that they could give different semantics.
  - At the end, we introduced an extension of Lambda Calculus with booleans
    and translated them away using Church encodings.
  - This extension can create terms that get "stuck" in evaluation.
  - Today we'll look at a solution of "stuck" terms and solution to that
    problem via _type-system_.
  - More concretely, we'll introduce the *simply-typed lambda calculus*,
    which forms the foundation of every modern functional programming
    language including Coq.

*)


(** ** Goal for today

   - Introduce the simply-typed Lambda Calculus (STLC) and it's type-system.
   - Prove _type-soundness_ via _progress_ and _preservation_.
   - Show that STLC cannot express recursion.
 *)


(** ** Problem *)

Module UNTYPED_LAMBDA_CALCULUS.

Require Import lec_10_lambda.


(**
   - Recall the lambda calculus with booleans.
 *)
  
Print tm'.
(** *** Terms
<<
Inductive tm' : Set :=
| tm_var' : string -> tm'
| tm_app' : tm' -> tm' -> tm'
| tm_abs' : string -> tm' -> tm'
| tm_true' : tm'
| tm_false' : tm'
| tm_if' : tm' -> tm' -> tm' -> tm'
>>
 *)

Print cbv_step'.
(** *** Call-by-value Semantics
<<     
Inductive cbv_step' : tm' -> tm' -> Prop :=
| _cbv_app1 :
forall t1 t2 t1' : tm',
t1 ~--> t1' ->
tm_app' t1 t2 ~--> tm_app' t1' t2
| _cbv_app2 :
forall v t2 t2' : tm',
value' v -> t2 ~--> t2' -> tm_app' v t2 ~--> tm_app' v t2'
| _cbv_beta :
forall (x : string) (t v : tm'),
value' v -> tm_app' (tm_abs' x t) v ~--> subst' x v t
| _if_cond :
forall tcond ttrue tfalse tcond' : tm',
tcond ~--> tcond' ->
tm_if' tcond ttrue tfalse ~--> tm_if' tcond' ttrue tfalse
| _if_true :
forall ttrue tfalse : tm',
tm_if' tm_true' ttrue tfalse ~--> ttrue
| _if_false :
forall ttrue tfalse : tm',
tm_if' tm_true' ttrue tfalse ~--> tfalse.
>>
*)


(** *** Stuck Terms
     
   Example 1:

     false true

     Can't apply false to true.

   Example 2:

     true (\x, x)

     Can't apply true to lambda.


   Example 3:

     if (\x, x) (\y, y) (\z, z)

     Can't apply if to lambda.

   Example 4:

     if true (false (\x, x)) (\z, z)

     The if true reduces to a (false (\x, x)) which is stuck.
*)


(** *** Types: idea

  - We will introduce a notion called _types_ that will classify 
    terms according to the shape of values they compute.
  - We can then prove a _type-soundness_ theorem:
    well-typed terms do not get stuck.
  - A sufficiently powerful type-system cannot be both *sound* and 
    _complete_.
  - _Soundness_ means: if a term is well-typed, then it does not
    get stuck.
  - _Completeness_ means: if a term does not get stuck, then it is
    well-typed.
  - Type-systems are generally designed to be sound.
  - We will introduce type-systems via the _simply-typed lambda calculus_ (STLC).
  - Coq is a sophisticated verion of typed lambda calculus.
*)
End UNTYPED_LAMBDA_CALCULUS.


(** ** Simply-Typed Lambda Calculus Syntax *)

(** *** Types or the shape of a value
   
   - We first need the "shape" of values.
   - Let us remind ourselves what the values were.
 *)

(**
<<
Inductive value' : tm' -> Prop :=
| v_abs' : forall (x : string) (t1 : tm'), value' (tm_abs' x t1)
| v_true' : value' tm_true'
| v_false' : value' tm_false
>>
*)

(** *** Type Syntax *)
(*

    T ::= Bool
        | T -> T

*)
Inductive ty : Type :=
| Ty_Bool : ty                (* for the boolean values *)
| Ty_Arrow : ty -> ty -> ty   (* t1 -> t2, for the abstraction values *)
.


(** *** Examples *)
(*
   Example 1:

     true: Bool
     false: Bool
*)

(*
   Example 2:

     negation: Bool -> Bool
*)

(*
   Example 3:

     and: Bool -> (Bool -> Bool) = Bool -> Bool -> Bool
*)

(*

   Example 4:
    
     \f, true: (Bool -> Bool) -> Bool

*)


(** *** Syntax *)
(*    
    t ::= x 
        | t t
        | \x: T, t    (lambda parameters get a type T)
        | true
        | false
        | if t t t
 *)
Inductive tm : Type :=
| tm_var : string -> tm
| tm_app : tm -> tm -> tm
| tm_abs : string -> ty -> tm -> tm  (* parameter augmented with type *)
| tm_true : tm
| tm_false : tm
| tm_if : tm -> tm -> tm -> tm
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


Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition f : string := "f".
Definition g : string := "g".
Definition h : string := "h".
(*
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold f : core.
Hint Unfold g : core.
Hint Unfold h : core.
*)


(** *** Examples *)

Example ex1 :=
  <{ \x: Bool, x }>.


Example ex2 :=
  <{ \x: Bool, (f (g x)) }>.


Example ex3 :=
  <{ (\x: Bool, \y: Bool -> Bool, x) }>.


Example ex4 :=
  <{ (\x: Bool -> Bool, x) (\x: Bool, x) }>.


Example ex5 :=
  <{ (\x: Bool -> Bool -> Bool, x) h }>.


Example ex6 :=
  <{ (\x: Bool, \y: (Bool -> Bool) -> Bool, \x: Bool -> Bool, y x) }>.


Example not :=
  <{ (\x: Bool, if x then false else true) }>.


Example and :=
  <{ (\x: Bool, \y: Bool, if x then y else false) }>.


Example or :=
  <{ (\x: Bool, \y: Bool, if x then true else y) }>.


(** ** Semantics *)

(** *** Values
   
   - Our values are essentially the same, although we will use the
     new version of lambda's that have been decorated with types.
 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>   (* this case changed *)
  | v_true :
      value <{true}>
  | v_false :
    value <{false}>.
Hint Constructors value : core.

(** *** Capture-avoid Substitution
   
   - Nothing changes about substitution.
   - Thus we should expect beta-reduction to stay the same.

 *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).


(** *** Call-by-value Semantics
   
   - Nothing changes with the semantics.
   - Intuitively, this makes sense: we shouldn't expect types to change
     the semantics of our programs.
   - In other words, types are a *static* construct as opposed to a
     *dynamic* construct.
*)
(*
  Note that the type is ignored by the semantics!   

                value v2
  ----------------------------------- ST_AppAbs
    (\x: T2, t1) v2 --> [x := v2]t1


       t1 --> t1'
  -------------------- ST_App1
    t1' t2 --> t1 t2
 

    value t1   t2 --> t2'
  ------------------------ ST_App2
      v1 t2 --> v1 t2


  ------------------------ ST_IfTrue
    if true t1 t2 --> t1


  ------------------------ ST_IfFalse
   if false t1 t2 --> t2


              t1 --> t1'
  ------------------------------ ST_If
   if t1 t2 t3 --> if t1' t2 t3

 *)

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


(** *** Multi-step reduction *)
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


(** *** Examples *)

Lemma step1 :
  <{ (\x: Bool, x) true }> -->* <{ true }>.
Proof.
  eapply multi_step.
  + apply ST_AppAbs.
    apply v_true.
  + simpl.
    apply multi_refl.
Qed.
(**
   - <{ true }> is a value.
   - So this term intutively has a good reduction sequence.
 *)


Lemma step2 :
  <{ (\x: Bool, (f (g x))) true }> -->* <{ f (g true) }>.
Proof.
  eapply multi_step.
  + apply ST_AppAbs.
    apply v_true.
  + simpl.
    apply multi_refl.
Qed.
(**
   - <{ f (g true) }> is not a value and cannot be reduced anymore.
   - So this term intutively has a bad reduction sequence.
 *)


Lemma step3 :
  <{ (\x: Bool, \y: Bool -> Bool, x) (\x: Bool -> Bool, x) false }> -->*
  <{(\x: Bool -> Bool, x) }>.
Proof.
  eapply multi_step.
  + apply ST_App1.
    apply ST_AppAbs.
    apply v_abs.
  + simpl.
    eapply multi_step.
    * apply ST_AppAbs.
      apply v_false.
    * simpl.
      apply multi_refl.
Qed.
(**
   - This term could be reduced to a value.
   - But intuitively the types are off because we are passing in
     [(\x: Bool -> Bool)] for a [Bool] and [false] for a [Bool -> Bool].
   - We will see that a *type-system* will reject these terms even
     though the reduction is ok.
 *)


Lemma step4 :
  <{ and (not true) (not false) }> -->* <{ false }>.
Proof.
  unfold and, not.
  eapply multi_step. {
    apply ST_App1.
    apply ST_App2.
    apply v_abs.
    apply ST_AppAbs.
    apply v_true.
  } {
    simpl.
    eapply multi_step. {
      apply ST_App1.
      apply ST_App2.
      apply v_abs.
      apply ST_IfTrue.
    } {
      eapply multi_step. {
        apply ST_App1.
        apply ST_AppAbs.
        apply v_false.
      } {
        simpl.
        eapply multi_step. {
          apply ST_App2.
          apply v_abs.
          apply ST_AppAbs.
          apply v_false.
        } {
          simpl.
          eapply multi_step. {
            apply ST_App2.
            apply v_abs.
            apply ST_IfFalse.
          } {
            eapply multi_step. {
              apply ST_AppAbs.
              apply v_true.
            } {
              simpl.
              eapply multi_step.
              + apply ST_IfFalse.
              + apply multi_refl.
            }
          }
        }
      }
    }
  }
Qed.

(** *** Exercise

  - Try drawing the proof tree corresponding to the reduction sequence above.
  - Imagine what the reduction sequence would look like with Church encodings!

 *)


(** ** Typing Relation 

   - We will now formalize a typing relation which will accept "good terms",
     i.e., those with "good" reduction sequences and reject "bad" terms,
     i.e., those with "bad" reduction sequences.
   - As the examples hint at, we will reject some terms that have "good"
     reduction sequences.
   - Similar to how we needed to define substitution for the operational
     semantics, we first need to define a *context* that will help us interpret 
     the types of lambda bindings.
 *)

(** *** Context

   - A _context_ is a partial map from variables to types. This means that
     we are not required to assign every variable to a type.
   - You may sometimes see a context can be presented as an associative list.
   - It is typically given the name Γ (Gamma).

 *)

Print partial_map.
Print total_map.
Definition context := partial_map ty.


(** *** Typing Judgement

   The typing judgement is notated Γ ⊢ t : T where
   - Γ is a context
   - the turnstyle ⊢ is common notation for "proves"
   - t is a term
   - T is a Type

   The typing judgement Γ ⊢ t : T can be read:
   The term t can be shown to have type T under context Γ.
 
 *)
Reserved Notation "Gamma '⊢' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).


(** *** Typing Rules *)
(*
     The type of a variable is what the context says it is.

         Γ(x) = Some T
     --------------------- T_Var
           Γ ⊢ x : T


     If under the context with x mapped to T2, t1 can be shown to have type T1,
     then the abstraction \x: T2, t1 has type T2 -> T1. Note that t1 is a term
     that may have x free.

              Γ, x: T2 ⊢ t1 : T1
     --------------------------------- T_Abs
          Γ ⊢ \x: T2, t1 : T2 -> T1


     We require the abstraction's parameter type and the argument's type to match.

           Γ ⊢ t1 : T2 -> T1    Γ ⊢ t2: T2
     ----------------------------------------- T_App
                  Γ ⊢ t1 t2 : T1


     ----------------------- T_True
          Γ ⊢ true : Bool


     ------------------------ T_False
          Γ ⊢ false : Bool

     
     We require each branch to have the same type.

        Γ ⊢ t1 : Bool       Γ ⊢ t2 : T1        Γ ⊢ t3 : T1
     -------------------------------------------------------- T_If
                     Γ ⊢ if t1 t2 t3 : T1

 *)

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma ⊢ x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma ⊢ t1 \in T1 ->
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


(** *** Example 1 *)
(*
              
            --------------------- T_Var
              x: Bool ⊢ x : Bool
      ------------------------------------ T_Abs
       empty ⊢ \x:Bool, x : (Bool -> Bool)

 *)

Example typing_example_1 :
  empty ⊢ \x:Bool, x \in (Bool -> Bool).
Proof.
  apply T_Abs.
  apply T_Var.
  reflexivity.
Qed.


(** *** Example 2 *)
(*

                                          --------------------- T_Var  ------------- T_Var
                                           Γ ⊢ y : Bool -> Bool         Γ ⊢ x : Bool
        --------------------- T_Var  ------------------------------------------------ T_App
            Γ ⊢ y : Bool -> Bool          Γ ⊢ y x : Bool
 ------------------------------------------------------------------------------------- T_App
                     Γ = x: Bool, y: Bool -> Bool ⊢ y (y x) : Bool
        ------------------------------------------------------------------ T_Abs
           x: Bool ⊢ \y:Bool -> Bool, (y (y x) : (Bool -> Bool) -> Bool
 --------------------------------------------------------------------------------- T_Abs
  empty ⊢ \x:Bool, \y:Bool -> Bool, (y (y x)) : (Bool -> (Bool -> Bool) -> Bool)

 *)

Example typing_example_2 :
  empty ⊢
    \x:Bool,
       \y:Bool -> Bool,
          (y (y x)) \in
    (Bool -> (Bool -> Bool) -> Bool).
Proof.
  apply T_Abs.
  apply T_Abs.
  eapply T_App.
  + apply T_Var.
    apply update_eq.
  + eapply T_App.
    * apply T_Var.
      apply update_eq.
    * apply T_Var.
      apply update_neq.
      intros Contra.
      discriminate.
Qed.


(** *** Not Complete 1 *)
(*

 -------------------------------------------- ??
  empty ⊢ if true (\x: Bool, x) true : ?

 *)


(** *** Not Complete 2 *)
(*

 ---------------------------------------------------------- ??
    empty ⊢ if true (\x: Bool, x) (true (\x: Bool, x)) : ?

 *)


(** ** Type Soundness 

  - We will now prove a type-soundness result.
  - In words, a well-typed term does not get stuck.
  - _well-typed_ means that a term can be assigned a type according to 
    the typing relation.
  - _not stuck_ means that every term reduces to a value with the
    appropriate type.
  - The proof proceeds in two major steps: _progress_ and _preservation_.
  - The basic idea of *progress* is that either we have reached a value
     (no more computation) or we can take a step.
  - The basic idea of _preservation_ is that taking a step does not change
    the type of a term.
  - By interweaving _progress_ and _preservation_, we will get that
    we eventually hit a value of the appropriate type.
  - This leads us to a few _canonical forms_ lemmas.

*)


Lemma canonical_forms_bool : forall t,
  empty ⊢ t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.


Lemma canonical_forms_fun : forall t T1 T2,
  empty ⊢ t \in (T2 -> T1) ->
  value t ->
  exists x u, t = <{\x:T2, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal; inversion HT; subst.
  exists x0, t1.
  reflexivity.
Qed.


(** ** Progress *)

(** *** Proving Progress

   - We prove progress now.
   - We have two inductive relations that we can induct on.
   - Either the derivation of the typing judgement or the term.
   - It turns out in this case it is possible to induct on either terms
     or the typing judgement.

 *)

Theorem progress : forall t T,
  empty ⊢ t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  (*
     We proceed by induction on the typing derivation Γ ⊢ t : T. 
   *)
  intros t T Ht.
  remember empty as Gamma.
  induction Ht.
  
  {
    (*
       Case

        empty(x) = Some T
     --------------------- T_Var
         empty ⊢ x : T

       We show that this case is impossible.
       In particular, observe that we have that empty(x) = Some T which is impossible.
     *)
    subst Gamma.
    inversion H.
  }
  {
    (*
       Case

           empty, x: T2 ⊢ t1 : T1
     --------------------------------- T_Abs
       empty ⊢ \x: T2, t1 : T2 -> T1

       We have to show that either value (\x: T2, t1) or exists t', \x: T2, t1 --> t'.
       We choose to show that value (\x: T2, t1).
       This follows because we can derive value (\x: T2, t1) with v_abs. 
     *)
    subst Gamma.
    left.
    apply v_abs.
  }
  { (*
       Case

       empty ⊢ t1 : T2 -> T1   empty ⊢ t2: T2
     ----------------------------------------- T_App
                empty ⊢ t1 t2 : T1

       We have to show that either value (t1 t2) or exists t', t1 t2 --> t'.
       We choose to show that exists t', t1 t2 --> t' (it's definitely not a value).
       We have two inductive hypotheses.

       IHHt1: empty = empty -> (value t1 \/ (exists t' : tm, t1 --> t'))
       IHHt2: empty = empty -> (value t2 \/ (exists t' : tm, t2 --> t'))

       Clearly, empty = empty, so our inductive hypotheses simplify to

       IHHt1: value t1 \/ (exists t' : tm, t1 --> t')
       IHHt2: value t2 \/ (exists t' : tm, t2 --> t')
       
        *)
    right.
    
    assert (Gamma = Gamma) as HTriv by reflexivity.
    subst Gamma.
    specialize (IHHt1 HTriv).
    specialize (IHHt2 HTriv).
    clear HTriv.

    (*    
       We proceed by case analysis on IHHt1.
     *)   
    destruct IHHt1.
    {
      (*     
         Case value t1: 
         
           We proceed by case analysis on IHHt2.

           Case value t2:
             Recall that we have to show that exists t', t1 t2 --> t'.

             We have that empty ⊢ t1 \in (T2 -> T1) from the induction on the
             typing derivation.
             We also have that t1 = \x: T2, t0 by canoncial forms of arrow
             types for some variable x and term t0.

             Thus we have to show that exists t', (\x: T2, t0) t2 --> t'.
             We claim that t' = [x:=t2] t0.
             Thus we have to show that (\x: T2, t0) t2 --> [x:=t2] t0.
             This is the rule for ST_AppAbs where we use that value t2.

           Case exists t' : tm, t2 --> t':
             Recall that we have to show that exists t', t1 t2 --> t'.

             We have that t2 --> t2' for some t2' by assumption.
             We claim that t' = t1 t2'.
             Thus we have to show that t1 t2 --> t1 t2'.
             This is the rule for ST_App2.
       *)
      destruct IHHt2.
      + eapply canonical_forms_fun in Ht1; auto.
        destruct Ht1 as [x [t0 H1]]; subst.
        exists (<{ [x:=t2] t0 }>).
        apply ST_AppAbs.
        assumption.
      + destruct H0 as [t2' Hstp].
        exists (<{t1 t2'}>).
        apply ST_App2.
        assumption.
        assumption.
    }
    {
      (*    
         Case exists t' : tm, t1 --> t':
         
           Recall that we have to show that exists t', t1 t2 --> t'.
           We have that t1 --> t1' for some t1' by assumption.
           We claim that t' = t1' t2.
           Thus we have to show that t1' t2 --> t1 t2.
           This is exactly the rule for ST_App1.           
       *)
      destruct H as [t1' Hstp].
      exists (<{t1' t2}>).
      apply ST_App1.
      assumption.
    }
  }
  {
    (*
       Case

     ----------------------- T_True
        empty ⊢ true : Bool

      We have to show that either value true or exists t', true --> t'.
      We choose to show that value true.
      This can be constructed with an application of v_true.
     *)
    left.
    apply v_true.
  }
  {
    (*
       Case

     ----------------------- T_False
       empty ⊢ false : Bool

      We have to show that either value false or exists t', false --> t'.
      We choose to show that value false.
      This can be constructed with an application of v_false.
     *)
    
    left.
    apply v_false.
  }
  {
    (*
       Case

        empty ⊢ t1 : Bool   empty ⊢ t2 : T1  empty ⊢ t3 : T1
     -------------------------------------------------------- T_If
                     empty ⊢ if t1 t2 t3 : T1

       We have to show that either value (if t1 t2 t3) or exists t', if t1 t2 t3 --> t'.
       We choose to show that exists t', if t1 t2 t3 --> t' (it's definitely not a value).
       We have three inductive hypotheses.

       IHHt1: empty = empty -> (value t1 \/ (exists t' : tm, t1 --> t'))
       IHHt2: empty = empty -> (value t2 \/ (exists t' : tm, t2 --> t'))
       IHHt3: empty = empty -> (value t3 \/ (exists t' : tm, t3 --> t'))

       Clearly, empty = empty, so our inductive hypotheses simplify to

       IHHt1: value t1 \/ (exists t' : tm, t1 --> t')
       IHHt2: value t2 \/ (exists t' : tm, t2 --> t')
       IHHt3: value t3 \/ (exists t' : tm, t3 --> t')

     *)

    right.
    
    assert (Gamma = Gamma) as HTriv by reflexivity.
    subst Gamma.
    specialize (IHHt1 HTriv).
    specialize (IHHt2 HTriv).
    specialize (IHHt3 HTriv).    
    clear HTriv.

    (*
       We proceed by case analysis on IHHt1.
     *)
    destruct IHHt1.   
    {
      (*
         Case value t1:
         
           We have that empty ⊢ t1 : Bool from our induction on the typing derivation.
           Thus t1 = true or t1 = false by canonical forms on booleans.
           We proceed by case analysis.
       *)

      assert (t1 = <{true}> \/ t1 = <{false}>) as HTorF. {
        apply canonical_forms_bool.
        assumption.
        assumption.
      }
      destruct HTorF; subst.
      + (*
           Case t1 = true:
             Recall that we have to show that exists t', if t1 t2 t3 --> t'.
             We claim that t1' = t2.
             We have that if true t2 t3 --> t2 by ST_IfTrue.
         *)
        exists t2.
        apply ST_IfTrue.
      + (*
           Case t1 = false:
             Recall that we have to show that exists t', if t1 t2 t3 --> t'.
             We claim that t1' = t2.
             We have that if true t2 t3 --> t2 by ST_IfTrue.
         *)
        exists t3.
        apply ST_IfFalse.
    }
    {
      (*
         Case exists t' : tm, t1 --> t':
         
         We have that t1 --> t1' for some t1' by assumption.
         Recall that we have to show that exists t', if t1 t2 t3 --> t'.
         We claim that t' = if t1' t2 t3.
         We have that if t1 t2 t3 --> if t1' t2 t3 by ST_If.
       *)
      destruct H as [t1' Hstp].
      exists <{if t1' then t2 else t3}>.
      apply ST_If.
      assumption.
    }
  }
Qed.


(** ** Preservation *)

(** *** Non-empty contexts

   - You may have noticed that the proof of progress assumed an
     empty context.
   - The proof of preservation will require us to work with
     non-empty contexts.
   - We need a few extra lemmas on contexts.
   - First, let's start with a theorem that illustrates more
     the idea of inducting on typing derivations but with
     non-empty contexts.

 *)

Theorem unique_types : forall Gamma e T T',
  Gamma ⊢ e \in T ->
  Gamma ⊢ e \in T' ->
  T = T'.
Proof.
  intros Gamma e T T' H.
  generalize dependent T'.

  (*
     By induction on the typing derivation Γ ⊢ t : T. 
   *)

  induction H; intros T' H'.
  {
    (*
       Case

          Γ(x) = Some T
     --------------------- T_Var
            Γ ⊢ x : T

       We have to show that T = T'.
       By inversion on Γ ⊢ x : T', we have that Γ(x) = T'.
       Since Γ(x) = T as well, we have that T = T'.
     *)
    inversion H'; subst.
    rewrite H2 in H.
    inversion H.
    reflexivity.
  }
  {
    (*
       Case

             Γ, x: T2 ⊢ t1 : T1
     --------------------------------- T_Abs
         Γ ⊢ \x: T2, t1 : T2 -> T1

       We have to show that T2' -> T1' = T2 -> T1 whenever Γ ⊢ \x: T2', t1 : T2' -> T1'
       By inversion on Γ ⊢ \x: T2', t1 : T2' -> T1', we have that
       Γ, x: T2' ⊢ t1 : T2' -> T1'.
       Moreover, by our inductive hypothesis, we obtain that T2' -> T1' = T2 -> T1,
       which is what we wanted to show.
     *)
    inversion H'; subst.
    apply IHhas_type in H5.
    subst.
    reflexivity.
  }
  {
    (*
       Case

           Γ ⊢ t1 : T2 -> T1   Γ ⊢ t2: T2
     ----------------------------------------- T_App
                  Γ ⊢ t1 t2 : T1

       We have to show that T1 = T1' if Γ ⊢ t1 t2: T1'.
       By inversion on Γ ⊢ t1 t2: T1', we have that
       Γ ⊢ t2: T2' and Γ ⊢ t1: T2' -> T1'.
       By our inductive hypothesis, we have that T2' -> T1' = T2 -> T1.
       Thus the result follows.

     *)
    inversion H'; subst.
    apply IHhas_type1 in H4.
    inversion H4; subst.
    reflexivity.
  }
  {
    (*
       Case

     ----------------------- T_True
          Γ ⊢ true : Bool

       By inversion on Γ ⊢ true : Bool, we have that Bool = Bool.
        
     *)
    inversion H'; subst.
    reflexivity.
  }
  {
     (*
       Case

     ----------------------- T_False
          Γ ⊢ false : Bool

       By inversion on Γ ⊢ false : Bool, we have that Bool = Bool.
        
     *)

    inversion H'; subst.
    reflexivity.
  }
  {
    inversion H'; subst.
    apply IHhas_type2 in H8.
    assumption.
  }
Qed.


Print inclusion.

Lemma weakening : forall Gamma Gamma' t T,
 inclusion Gamma Gamma' ->
 Gamma ⊢ t \in T ->
 Gamma' ⊢ t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.

  (*
     By induction on the typing derivation Γ ⊢ t : T. 
   *)
  induction Ht; intros.
  {
    (*
       Case

          Γ(x) = Some T
     --------------------- T_Var
            Γ ⊢ x : T

       We have to show that Γ' ⊢ x : T.
       It suffices to show that Γ'(x) = T by T_Var.
       By assumption, we have that Γ ⊢ x : T and Γ' extends Γ.
       By inversion on Γ ⊢ x : T, we have that Γ(x) = T.
       Since Γ' extends Γ, we clearly have Γ'(x) = T as well.
     *)
    apply T_Var.
    unfold inclusion in H0.
    auto.
  }
  {
    (*
       Case

             Γ, x: T2 ⊢ t1 : T1
     --------------------------------- T_Abs
         Γ ⊢ \x: T2, t1 : T2 -> T1

       We have to show that Γ' ⊢ \x: T2, t1: T2 -> T1.
       It suffices to show that Γ', x: T2 ⊢ t1 : T1 by T_Abs.

       Our inductive hypothesis states:

       inclusion Γ Γ' and Γ, x: T2 ⊢ t1 : T1 implies that Γ', x: T2 ⊢ t1 : T1.

       Thus it suffices to show that inclusion (Γ, x: T2) (Γ', x: T2) and
       Γ, x: T2 ⊢ t1 : T1 by our inductive hypothesis.
       The first requirement follows by inclusion_update.
       The second requirement follows by assumption.
     *)
    apply T_Abs.
    apply IHHt.
    apply inclusion_update.
    assumption.
  }
  {
    (*
       Case

           Γ ⊢ t1 : T2 -> T1   Γ ⊢ t2: T2
     ----------------------------------------- T_App
                  Γ ⊢ t1 t2 : T1

       We have to show that Γ' ⊢ t1 t2: T1.
       It suffices to show that Γ' ⊢ t1 : T2 -> T1 and Γ' ⊢ t2: T1 by T_App.

       We have two inductive hypotheses:
       IHHt1: inclusion Γ Γ' and Γ ⊢ t1 : T2 -> T1 implies that Γ' ⊢ t1 : T2 -> T1.
       IHHt2: inclusion Γ Γ' and Γ ⊢ t2 : T2 implies that Γ' ⊢ t2 : T2.

       We have Γ' ⊢ t1 : T2 -> T1 by IHHt1 and assumption that Γ' extends Γ.
       We have Γ' ⊢ t2 : T2 by IHHt2 and assumption that Γ' extends Γ.

     *)
    eapply T_App.
    + eapply IHHt1.
      assumption.
    + eapply IHHt2.
      assumption.
  }
  {
    (*
       Case

     ----------------------- T_True
          Γ ⊢ true : Bool

       The rule T_True can be applied in any context.
        
     *)
    apply T_True.
  }
  {
    (*
       Case

     ----------------------- T_False
          Γ ⊢ false : Bool


       The rule T_False can be applied in any context.

     *)
    apply T_False.
  }
  {
    (*
       Case

          Γ ⊢ t1 : Bool     Γ ⊢ t2 : T1      Γ ⊢ t3 : T1
     -------------------------------------------------------- T_If
                     Γ ⊢ if t1 t2 t3 : T1

       We have to show that Γ' ⊢ if t1 t2 t3: T1.
       It suffices to show that Γ' ⊢ t1 : Bool, Γ' ⊢ t2: T1, and Γ' ⊢ t3: T1 by T_If.

       We have three inductive hypotheses:
       IHHt1: inclusion Γ Γ' and Γ ⊢ t1 : Bool implies that Γ' ⊢ t1 : Bool.
       IHHt2: inclusion Γ Γ' and Γ ⊢ t2 : T1 implies that Γ' ⊢ t2 : T1.
       IHHt3: inclusion Γ Γ' and Γ ⊢ t3 : T1 implies that Γ' ⊢ t2 : T1.

       We have Γ' ⊢ t1 : Bool by IHHt1 and assumption that Γ' extends Γ.
       We have Γ' ⊢ t2 : T1 by IHHt2 and assumption that Γ' extends Γ.
       We have Γ' ⊢ t3 : T1 by IHHt3 and assumption that Γ' extends Γ.

     *)
    eapply T_If.
    + eapply IHHt1.
      assumption.
    + eapply IHHt2.
      assumption.
    + eapply IHHt3.
      assumption.
  }
Qed.


(**
   - Here's a simple consequence of weakening.
 *)
Corollary weakening_empty : forall Gamma t T,
  empty ⊢ t \in T ->
  Gamma ⊢ t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.


(** *** Substitution and Typing

   - The main lemma we need is that substituting terms preserves types.
   - Note that the term t has type T in any context
   - However, the value that we are substituting must be a closed term, i.e.,
     typeable under the empty context.
 *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma ⊢ t \in T ->
  empty ⊢ v \in U ->
  Gamma ⊢ [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma.
  generalize dependent T.

  (*
     We proceed by induction on terms t.
   *)
  induction t.
  {
    (*
       Case t = y:

       We have that Γ, x: U(y) = Some T by inversion on Γ, x: U ⊢ y: T.

       We have to show that Γ ⊢ ([x := v] y): T.
       We proceed by case analysis on whether x == y or not.
       
     *)
    intros T Gamma H; inversion H; clear H; subst; simpl.
    rename s into y.
    destruct (eqb_stringP x y); subst.
    + (*
          Case x=y 
          
            We have that Γ, y: U(y) = Some T so that U = T.
            From induction on terms we have that empty ⊢ v : U.
            Thus the result follows by weakining.
       *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty.
      assumption.
    + (* 
         Case x<>y 

            We have to show that Γ, y: U(y) = Some T when x <> y.
            This follows by T_Var and properties of updating a context.
       *)
      apply T_Var.
      rewrite update_neq in H2; auto.
  }
  {
    (*
       Case t = t1 t2:

       We have to show that Γ ⊢ ([x := v] t1) ([x := v] t2) \in T.
       
       It suffices to show that 
       1) Γ ⊢ ([x := v] t1) \in T2 -> T
       2) Γ ⊢ ([x := v] t2) \in T2
       by T_App.

       We have that
       H1:  x |-> U; Gamma ⊢ t1 \in (T2 -> T)
       H2:  x |-> U; Gamma ⊢ t2 \in T2      
       by inversion on x |-> U ; Gamma ⊢ t1 t2 \in T1.

       We have two induction hypotheses
       IHt1: (x |-> U;  Γ ⊢ t1 \in T)  ->  Γ ⊢ [x := v] t1 \in T for any T
       IHt2: (x |-> U;  Γ ⊢ t2 \in T)  ->  Γ ⊢ [x := v] t2 \in T for any T

       We have that Γ ⊢ [x := v] t1 \in T2 -> T by IHt1 and H1.
       We have that Γ ⊢ [x := v] t1 \in T2 by IHt2 and H2.

     *)
    intros T Gamma H; inversion H; clear H; subst; simpl.
    eapply T_App.
    + eapply IHt1.
      eapply H3.
    + eapply IHt2.
      assumption.     
  }
  {
    (*
       Case t = \y: T2, t0 : T2 -> T1:

       We have to show that Γ ⊢ ([x := v] \y: T2, t0) : T2 -> T1.

       We have that
       H1:  Gamma, x: U, y: T2 ⊢ t0 : T1
       by inversion on Gamma, x: U ⊢ \y: T2, t0 : T2 -> T1.
       
       It suffices to show that 
       Γ, y: T2  ⊢ if x == y then (\y: T2, to) else ([x := v] t0) : T2 -> T1
       by T_Abs.     
     *)
    intros T Gamma H; inversion H; clear H; subst; simpl.
    rename s into y, t into S.

    (*
       We proceed by case analysis on x == y.
     *)
    destruct (eqb_stringP x y); subst; apply T_Abs.
    + (*
         Case x=y 

           y shadows x and therefore has the appropriate type.
       *)
      rewrite update_shadow in H5.
      assumption.
    + (**
         Case x<>y:
         
           We have one inductive hypothesis
           IHt1: (Γ, x: U ⊢ t1: T) -> Γ ⊢ [x := v] t0: T for any T
           
           The result follows by the induction hypothesis and permutation
           of the context.
       *)
      apply IHt.
      rewrite update_permute; auto.
  }
  {
    (*
       Case t = true:

       T_True can be applied in any context.
       
     *)
    intros T Gamma H; inversion H; clear H; subst; simpl.
    apply T_True.
  }
  {
    (*
       Case t = false:

       Similar to case t = true.
       
     *)
    intros T Gamma H; inversion H; clear H; subst; simpl.
    apply T_False.
  }
  {
    (*
       Case t = if t1 t2 t3

       Similar to case t = t1 t2.
     *)
    intros T Gamma H; inversion H; clear H; subst; simpl.
    apply T_If.
    + apply IHt1.
      assumption.
    + apply IHt2.
      assumption.
    + apply IHt3.
      assumption.
  }
Qed.

(**
   - Finally the proof of preservation.
 *)
Theorem preservation : forall t t' T,
  empty ⊢ t \in T ->
  t --> t' ->
  empty ⊢ t' \in T.
Proof with eauto.
  intros t t' T HT.
  generalize dependent t'.
  remember empty as Gamma.

  (**
     By induction on the typing derivation.
   *)
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst; eauto.
    (* Most of the cases are immediate by induction,
       and eauto takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2.
      inversion HT1; subst.
      assumption.
      assumption.
Qed.


(** ** Type-Soundness: Putting It Together 

   - We can now formalize the statement that well-typed terms
     do not get stuck.
   - First recall the definition of normal forms.
 
 *)

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(**
   - A term is stuck if there is no reduction it can take and it is
     not a value (which syntactically indicates that there is no more
     computation left to be done).
   - Thus this notionof stuck does not assume that  normal forms and
     values coincide.
 *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.


Corollary type_soundness : forall t t' T,
  empty ⊢ t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti.
  unfold stuck.
  intros [Hnf Hnot_val].
  unfold normal_form in Hnf.

  (*
     By induction on multi-step relation.
   *)
  induction Hmulti.
  {
    (*
       Case

        ---------------- multi_refl
            t -->* t

       We have to show that t is not stuck.
       By progress, we have that either t is a value or or it has a step.
       Thus this case is proven.
     *)
    apply progress in Hhas_type.
    destruct Hhas_type; auto.
  }
  {
    (*
       Case

          t --> t1      t1 -->* t'
        --------------------------- multi_step
                t -->* t'

        We have to show that t' is not stuck.
        Our inductive hypothesis is: 
        empty ⊢ t' : T and t1 -->* t' implies that t' is not stuck.

        Thus it suffices to show that empty ⊢ t' : T.
        This holds by preservation provided we can show that t --> t1 which
        we have in this case of the induction.        
     *)
    apply IHHmulti; auto.
    eapply preservation in Hhas_type.
    eapply Hhas_type.
    apply H.
  }
Qed.


(** ** Recursion 

   - STLC has many nice properties.
   - At this point, we may wonder if we lost expressive power?
   - As it turns out, we will no longer be able to write recursive terms.

 *)

(** *** Can you type the Y-Combinator? *)
(*

   (\f, (\x, f (x x)) (\x, f (x x))


   (\f: ?T, (\x: ?S, f (x x)) (\x: ?U, f (x x))
*)

(**

   - Let's look at (\x: ?S, f (x x)
   - We have that x has type ?S
   - Moreover x is applied to itself.
   - By application, we know that ?S = ?S2 -> ?S1 and ?S = ?S2.
   - In other words, we have that ?S2 -> ?S1 = ?S2.
   - This only has trivial solutions.
   - Thus we cannot type the Y-combinator

*)


(** *** Syntax *)
(*    
    t ::= ...
        | fix t
 *)


(** *** Values
    
    - Nothing changes

 *)


(** *** Operational Semantics *)
(*

   same operational rules and ...

    
  ---------------------------------------------- ST_fix
    fix (\x: T, t) --> [x := fix (\x: T, t)] t

 *)


(** *** Typing Rules *)
(*

   same typing rules and ...

    Γ ⊢ t : T -> T
  ------------------ T_fix
    Γ ⊢ fix t : T

 *)


(** *** Example 1: Factorial *)
(*

 Γ ⊢ (\f: nat -> nat, \n: nat, if n == 0 then 0 else f (n-1)) : (nat -> nat) -> (nat -> nat)
  -------------------------------------------------------------------------------------- T_fix
     Γ ⊢ fix (\f: nat -> nat, \n: nat, if n == 0 then 0 else f (n-1)) : nat -> nat

 *)


(** *** Example 2: Non-termination *)
(*

     Γ ⊢ (\f: nat -> nat, \n: nat, f n) : (nat -> nat) -> (nat -> nat)
  ----------------------------------------------------------------------- T_fix
          Γ ⊢ fix (\f: nat -> nat, \n: nat, f n) : nat -> nat

 *)


(** ** Goal for today

   - We saw the simply-typed Lambda Calculus (STLC) and it's type-system.
   - We proved type-soundness via progress and preservation.
   - We saw that STLC could not express recursion, and hence, is not
     Turing complete.
 *)
