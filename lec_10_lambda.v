(** * Lambda Calculus *)

From Coq Require Import Strings.String.
Require Import Multi.

(** ** Recap 

    - Last time we looked at Hoare Logic, which gave us a way to verify 
      properties of single programs that contains state.
    - As a reminder, the ability to read/write to state is what gave us
      Turing completeness.
    - Today, we'll introduce another language that gives an alternative
      to Turing-completeness: substitution in _Lambda Calculus_.
 *)


(** ** Goal for today

   - Introuduce Lambda Calculus, including _alpha-equivalence_,
     _free variables_, and _substituion_.
   - Introduce _call-by-value_ and _call-by-need_ semantics.
   - Show how to perform _Church encodings_.
   - Illustrate non-termination, recursion, and the Y-combinator in 
     Lambda Calculus.
   - Introduce the idea of definitional translation which will give us
     a way to extend the Lambda Calculus.
 *)


(** ** Lambda Calculus 

   - Lambda calculus was invented by Alonzo Church in the 1930s for studying the
     foundations of mathematics.
   - The original system was shown inconsistent (Kleene–Rosser paradox) and now the
     (untyped) lambda calculus is used as a model of computation.
   - There are weaker versions of lambda calculus such as typed lambda calculus that
     we will look at later that can be used a logic.
   - Today we will look at untyped lambda calculus, or simply, lambda calculus.
   - Lambda calculus (i.e., λ-calculus) is a "notation" for describing functions.
   - The word "lambda" comes from use of the Greek letter lambda (λ) in
     defining functions.
   - The word "calculus" means symbolic calculation and is not related to
     high-school calculus.
*)

(** *** Syntax *)
(*
   e ::= x         (variable)
       | e e       (application)
       | \x. e     (abstraction)
 *)

Inductive tm : Type :=
| tm_var : string -> tm          (* variable *)
| tm_app : tm -> tm -> tm        (* application *)
| tm_abs : string -> tm -> tm    (* abstraction *)
.


(** *** Notation *)

Declare Custom Entry lambda.
Notation "<{ e }>" := e (e custom lambda at level 99).
Notation "( x )" := x (in custom lambda, x at level 99).
Notation "x" := x (in custom lambda at level 0, x constr at level 0).
Notation "x y" := (tm_app x y) (in custom lambda at level 1, left associativity).
Notation "\ x , y" :=
  (tm_abs x y) (in custom lambda at level 90, x at level 99,
                     y custom lambda at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.


Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition f : string := "f".
Definition g : string := "g".
Definition h : string := "h".


(** *** Examples *)

Example ex1 :=
  <{ \x, x }>.


Example ex2 :=
  <{ \x, (f (g x)) }>.


Example ex3 :=
  <{ (\x, \y, x) }>.


Example ex4 :=
  <{ (\x, x) (\x, x) }>.


Example ex5 :=
  <{ (\x, x) h }>.

Example ex6 :=
  <{ (\x, \y, \x, y x) }>.


(** *** Alpha-Equivalence

   - Lambda terms are equivalent up to *alpha-conversion*, i.e., renaming of variables.
*)

(*

   \x, x = \y, y

   \x, (f (g x)) = \z, (f (g z))

   (\x, x) (\x, x) =  (\z, z) (\a, a)

   (\x, \y, \x, y x) = (\x, (\y, (\a, y a)))

 *)


(** *** Associativity

   - Lambda abstraction associates to the right.
*)
(*

  (\x, \y, \x, y x) = (\x, (\y, (\x, y x)))

 *)


(** *** Bound variables

   - A variable is _bound_ if it is referred to by a lambda abstraction.
*)
(*

    \x, x           (x is bound)

    (\x, \y, x)     (x is bound, y is bound and not used)

    \x, (f (g x))   (x is bound, f and g are not bound)

 *)


(** *** Free variables

   - A variable is _free_ if it is not bound.
*)   
(*

    (\x, x) h          (h is free)

    (\x, \y, \x, y x)  (no free variables)

 *)


Require Import Coq.Lists.ListSet.

Fixpoint free_var (t: tm): set string :=
  match t with
  | tm_var y =>
      set_add string_dec y (empty_set string)
  | <{\y, t1}> =>
      set_remove string_dec y (free_var t1)
  | <{t1 t2}> =>
      set_union string_dec (free_var t1) (free_var t2)
  end.


Print ex5.
Eval compute in free_var ex5.

Print ex6.
Eval compute in free_var ex6.



(** ** Substitution *)


(** *** Variables

    - The "only interesting" part of lambda calculus is variables.
    - Believe it or not, the rest of lecture will focus on this concept.
    - The idea of variables is actually very simple: a variable is a placeholder
      for any other term. In other words, any time you see a variable, you can
      replace it with any other term in the language. Put another way, variables
      enable copy-and-paste.
    - Warning: a variable in lambda calculus is not the same as a variable in many
      imperative programming languages. The language IMP has references and not
      variables.
    - We'll model variables with strings. We want variables to be denumerable and
      for equality to be decidable.
 *)


Check string_dec.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.


(** *** Substitution attempt 

  - A very first attempt at writing substitution might look like the code below.
 *)

Fixpoint subst_wrong (x: string) (s: tm) (t: tm): tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y, t1}> =>
      let t1' := subst_wrong x s t1 in
      <{ \y, t1' }> (* wrong *)
  | <{t1 t2}> =>
      let t1' := subst_wrong x s t1 in
      let t2' := subst_wrong x s t2 in
      <{ t1' t2' }>
  end.

(** 
   - It is helpful to look at a few examples to see where this
     definition of substitution goes wrong.
 *)


Eval compute in subst_wrong f y <{ \x, (f (g x)) }>.
(** Ok *)


Eval compute in subst_wrong g y <{ \x, (f (g x)) }>.
(** Ok *)


Eval compute in subst_wrong x y <{ (\x, x) }>.

(** *** Why is this wrong?

   - We haven't given the semantics of lambda calculus yet.
   - But intuitively we might expect this to be wrong.
   - Because we changed an identity function into a non-identity function after
     we performed the substitution.
   - One possible fix is to not substitute in this case, which will lead to a 
     concept called capture-avoid substitution.
*)


(** *** Capture-avoid Substitution *)


Reserved Notation "'[' x ':=' s ']' t" (in custom lambda at level 20, x constr).
Fixpoint subst (x: string) (s: tm) (t: tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y, t1}> =>
      if eqb_string x y then t else <{\y, [x:=s] t1}> (* fixed here *)
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom lambda).


Eval compute in <{[g := y] \x, (f (g x)) }>.
(* Ok *)


Eval compute in <{[g := y] \x, (f (g x)) }>.
(* Ok *)


Eval compute in <{[x := y] (\x, x) }>.
(* Ok *)


(** ** Call-by-value semantics *)

(**
   - Before we define semantics, we will need to introduce values.
 *)


(** *** Values

    - A _value_ is a syntactically-identified subset of terms that signals
      that there is no more computation left to be run.
    - We will need values to define small-step semantics.
    - In lambda calculus, there is only 1 value: a lambda.
*)
(*

    --------------------- v_abs
        value (\x. t)
 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x t1,
      value <{\x, t1}>.


(** *** Call-by-value Semantics *)
(*

        t1 --> t1'
   -------------------- cbv_app1
     t1 t2 --> t1' t2


     value t1   t2 --> t2'
   ------------------------ cbv_app2
      t1 t2 --> t1 t2'

            value v
   ------------------------ cbv_beta
   (\x. t) v --> [x := v] t

 *)

Reserved Notation " t '-->' t' "
                  (at level 40, t' at level 39).
Inductive cbv_step : tm -> tm -> Prop :=
| cbv_app1 : forall t1 t2 t1',
    t1 --> t1' ->
    <{ t1 t2 }> --> <{ t1' t2 }>
| cbv_app2 : forall v t2 t2',
    value v ->
    t2 --> t2' ->
    <{ v t2 }> -->  <{ v t2' }>
| cbv_beta : forall x t v,
    value v ->
    <{ (\x, t) v }> -->  <{ [ x:= v] t }>
where " t '-->' t' " := (cbv_step t t').


(** *** Multi-step reduction *)
Notation multistep := (multi cbv_step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


(** *** Example 1 *)
(*

   (\x, x) (\x, x) -->* (\x, x)

 *)

Example cbv_ex1:
  <{ (\x, x) (\x, x) }> -->* <{ (\x, x) }>.
Proof.
  eapply multi_step; eauto.
  apply cbv_beta.
  apply v_abs.
Qed.


(** *** Example 2 *)
(*

   ((\x, \y, x) (\x, x)) ((\x, \y, x) (\x, x)) 
      -->
   ((\y, (\x, x)) ((\x, \y, x) (\x, x)) 
      -->
   ((\y, (\x, x)) ((\y, (\x, x)) 
      -->
   (\x, x)

 *)


Example cbv_ex2:
  <{ ((\x, \y, x) (\x, x)) ((\x, \y, x) (\x, x)) }> -->* <{ \x, x }>.
Proof.
  eapply multi_step.
  {
    apply cbv_app1.
    apply cbv_beta.
    apply v_abs.
  }
  {
    eapply multi_step.
    {
      apply cbv_app2.
      apply v_abs.
      apply cbv_beta.
      apply v_abs.
    }
    {
      simpl.
      eapply multi_step.
      {
        apply cbv_beta.
        apply v_abs.
      }
      {
        simpl.
        apply multi_refl.
      }
    }
  }
Qed.


(** *** Large-step semantics *)
(*

   ------------ cbv_refl'
      v ==> v


                      value v'         value v
      t0 ==> \x, t   t1 ==> v'   [x := v'] t ==> v
   -------------------------------------------------- cbv_beta'
                       t0 t1 ==> v

 *)


Reserved Notation " t '==>' v "
                  (at level 40, v at level 39).
Inductive cbv_big_step : tm -> tm -> Prop :=
| cbv_refl' : forall v,
    value v ->
    v ==> v
| cbv_beta' : forall x t t0,
    t0 ==> <{ \x, t }> ->
    forall v',
      value v' ->
      forall t1, 
        t1 ==> v' ->
        forall v, 
          value v ->
          <{ [x := v'] t }> ==> v ->
          <{ t0 t1 }> ==> v
where " t '==>' v " := (cbv_big_step t v).



(** *** Call-by-value is deterministic
   
   - It's a function, so we just need the relation for non-termination.
 *)

Lemma cbv_deterministic :
  forall t t',
    t ==> t' ->
    forall t'',
      t ==> t'' ->
      t' = t''.
Proof.
  intros t t' H.
  induction H.
  { (* cbv_refl' *)
    intros.
    inversion H; subst.
    inversion H0; subst.
    reflexivity.
  }
  { (* cbv_beta' *)
    intros.
    inversion H0; subst.
    inversion H2; subst.
    apply IHcbv_big_step3.
    inversion H4; subst.
    + inversion H5; subst.
    + inversion H10; subst.
      apply IHcbv_big_step1 in H7.
      inversion H7; subst.
      inversion H8; subst.
      apply IHcbv_big_step2 in H9.
      inversion H9; subst.
      assumption.
  }
Qed.


(** ** Call-by-need semantics *)

(** *** Motivation

    - Up until this point, we have only looked at eager evaluation where
      we evaluate terms to values before performing further reductions. 
    - What if we computed the values on demand, i.e., when we needed them?
    - This is what *call-by-need* semantics does.
 *)


(** *** Call-by-need Semantics *)
(*

        t1 --> t1'
   -------------------- cbn_app
     t1 t2 --> t1' t2


   ------------------------------ cbn_beta
    (\x. t1) t2 --> [x := t2] t1

 *)

Reserved Notation " t '--->' t' "
                  (at level 40, t' at level 39).
Inductive cbn_step : tm -> tm -> Prop :=
| cbn_app : forall t1 t2 t1',
    t1 ---> t1' ->
    <{ t1 t2 }> ---> <{ t1' t2 }>
| cbn_beta : forall x t t',
    <{ (\x, t) t' }> ---> <{ [x := t'] t }>
where " t '--->' t' " := (cbn_step t t').

(** *** Multi-step reduction *)
Notation multistep' := (multi cbn_step).
Notation "t1 '--->*' t2" := (multistep' t1 t2) (at level 40).


(** *** Example 1 *)
(*

   (\x, x) (\x, x) --->* (\x, x)

 *)

Example cbn_ex1:
  <{ (\x, x) (\x, x) }> --->* <{ (\x, x) }>.
Proof.
  eapply multi_step; eauto.
  apply cbn_beta.
Qed.


(** *** Example 2 *)
(*

   ((\x, \y, x) (\x, x)) ((\x, \y, x) (\x, x)) 
      -->
   ((\y, (\x, x)) ((\x, \y, x) (\x, x)) 
      -->
   \x, x

 *)

Print cbv_ex2.

Example cbn_ex2:
  <{ ((\x, \y, x) (\x, x)) ((\x, \y, x) (\x, x)) }> --->* <{ \x, x }>.
Proof.
  eapply multi_step.
  {
    apply cbn_app.
    apply cbn_beta.
  }
  {
    simpl.
    eapply multi_step.
    {
      apply cbn_beta.
    }
    {
      simpl.
      eapply multi_refl.
    }
  }
Qed.


(** *** Big-step semantics *)

Reserved Notation " t '===>' v "
                  (at level 40, v at level 39).
Inductive cbn_big_step : tm -> tm -> Prop :=
| cbn_refl' : forall v,
    value v ->
    v ===> v
| cbn_beta' : forall x t t0 t1 v,
    t0 ==> <{ \x, t }> ->
    value v ->
    <{ [x := t1] t }> ==> v ->
    <{ t0 t1 }> ===> v
where " t '===>' v " := (cbn_big_step t v).


(**
   - Call-by-value and call-by-need do not give equivalent semantics.
   - We'll be able to see this when we see how to code up non-terminating, i.e.,
     infinite reduction sequences with lambda calculus.
 *)


(** ** Non-termination *)

(** *** Infinite loops?
    
  - Can we write an infinite loop in Lambda calculus?
  - If we could, then we basically have "shown" that Lambda calculus
    is Turing complete.
  - Consider the following term.
 *)

Example Omega := <{ (\x, x x) (\x, x x) }>.

Lemma cbv_Omega:
  <{ Omega }> --> <{ Omega }>.
Proof.
  unfold Omega.
  apply cbv_beta.
  apply v_abs.
Qed.

(**
  - We have shown that the term Omega reduces to itself under
    call-by-value semantics.
  - Thus we have an infinite loop!
  - So lambda calculus with call-by-value semantics is Turing complete.
 *)


Lemma cbn_Omega:
  <{ Omega }> ---> <{ Omega }>.
Proof.
  apply cbn_beta.
Qed.

(**
  - We have shown that the term Omega reduces to itself under call-by-name
    semantics.
  - Thus we have an infinite loop under another semantics!
 *)


(** 
  - We might wonder when call-by-value and call-by-name differ.
  - Consider the following example.
 *)

Example ex_cbv_Omega :=
  <{ (\x, \y, y) Omega }>.

Example cbv_Omega2:
  <{ (\x, \y, y) Omega }> --> <{ (\x, \y, y) Omega }>.
Proof.
  apply cbv_app2.
  apply v_abs.
  apply cbv_Omega.
Qed.

(**
  - Thus the term above reduces to itself.
  - So we have another infinite loop.
  - What about for call-by-name?
 *)

Example cbn_Omega2:
  <{ (\x, \y, y) Omega }> ---> <{ (\y, y) }>.
Proof.
  apply cbn_beta.
Qed.

(**
  - The call-by-name semantics terminates with an identity function.
  - What a complicated way to write an identity function!
  - In general, call-by-value and call-by-name will give different semantics.
  - And cbn_Omega2 gives us one example.
 *)


(** ** Lambda Calculus Encodings *)

(** *** Towards more realistic programs

   - Perhaps surprisingly, lambda calculus is Turing complete.
   - Even though it is Turing complete, it can be difficult to see how
     to write real programs in lambda calculus.
   - We'll show how to encode familiar data such as booleans and natural
     numbers as lambda terms now.
 *)


(** *** Booleans 

   - We'll model booleans as a two function argument.
   - TRUE will return the first argument.
   - FALSE will return the second argument.
*)

Example TRUE :=
  <{ \x, \y, x }>.

Example FALSE :=
  <{ \x, \y, y }>.


(**
   - Next we'll show how to define some logical operators.
 *)

Definition b : string := "b".
Definition b1 : string := "b1".
Definition b2 : string := "b2".


(** *** NOT
   
   - NOT should take a boolean and return a boolean
   - So b is of type boolean, which means its a two argument function.
   - If b is TRUE, it should return it's first argument. Hence we should
     pass in FALSE as the first argument.
   - By symmetry, we should pass in TRUE as the second argument.
 *)
Example NOT :=
  <{ \b, b FALSE TRUE }>.


(** *** AND
   
   - AND should take two booleans and return a boolean.
   - So b1 and b2 are booleans, which means they are both two argument function.
   - If b1 is TRUE, we should just return the second boolean b2.
   - If b1 is FALSE, then it is for sure FALSE.
 *)
Example AND :=
  <{ \b1, \b2, b1 b2 FALSE }>.


(** *** OR
    
   - Similar reasoning to AND.
 *)
Example OR :=
  <{ \b1, \b2, b1 TRUE b2}>.


(** *** IF
    
   - b is a boolean, which means its a two-argument function.
   - f and g are arbitrary functions containing the TRUE and FALSE branches.
   - Thus if b is TRUE, we should execute f.
   - And if b is FALSE, we should execute g.
 *)

Example IF' :=
  <{ \b, \f, \g, b f g }>.


(** *** Church Numerals 

   - We have already worked with Church numerals as a shallow embedding.
   - We'll now see the deep embedding version of Church numerals.
   - The idea is that we will represent the number n as f applied to x n times.
 
 *)

Example ZERO :=
  <{ \f, \x, x }>.


Definition n : string := "n".

Example SUCC :=
  <{ \n, \f, \x, f (n f x) }>.


Example _1 :=
  <{ SUCC ZERO }>.

Example _2 :=
  <{ SUCC _1 }>.

Example _3 :=
  <{ SUCC _2 }>.


(** *** Addition

   - PLUS should take two numbers, which are two argument functions.
   - The first argument is a function to apply and the second argument is the
     value to apply it to.
 *)

Definition n1 : string := "n1".
Definition n2 : string := "n2".

Example PLUS :=
  <{ \n1, \n2, n1 SUCC n2 }>.


(**
   - The infamous? predecessor function.
   - Don't ask me how it works.
 *)
Example PRED :=
  <{ \n, \f, \x, n (\g, \h, h (g f)) (\b, x) (\b, b) }>.

Example ISZERO :=
  <{ \ n, n (\ x, FALSE) TRUE }>.


(** ** Recursion and the Y-Combinator *)

(**
   - Suppose we wanted to write multiplication as an ordinary fix-point.
   - Can we come up with an encoding for defining a fix-point with lambda calclus?
 *)

Fixpoint my_times (n m: nat) :=
  match n with
  | O => O
  | S n' => m + my_times n' m
  end.


(** *** Goal *)
(*

   TIMES = \n, \m, IF (ISZERO n) ZERO (PLUS m (TIMES (PRED n) m))
 *)
(**
   - The issue is that we don't have a way to directly define recursive functions!
   - In other words, what we have is an equation to solve and not a definition.
 *)


(** *** Wishful thinking
  
   - Pass in an extra argument f.
   - f should have the same type of TIMES'
 *)

Example TIMES' :=
  <{ \f, \n, \x, IF' (ISZERO n) ZERO (PLUS x (f f (PRED n) x)) }>.

Example TIMES :=
  <{ TIMES' TIMES' }>.


(** *** Recursion encoded! *)
(*

   TIMES' TIMES'
   = (\f, \n, \x, IF' (ISZERO n) ZERO (PLUS x (f f (PRED n) x))) TIMES'
   = \n, \x, IF' (ISZERO n) ZERO (PLUS x (TIMES' TIMES' (PRED n) x))
   = \n, \x, IF' (ISZERO n) ZERO (PLUS x (TIMES (PRED n) x))
 *)


(** *** Y Combinator 

   - We can also define a lambda term that finds the fix-point for us directly.
   - Here is the Y-combinator.
 *)

Example cbn_Y :=
  <{ \f, (\x, f (x x)) (\x, f (x x)) }>.


(*
     cbn_Y TIMES' 
   = (\f, (\x, f (x x)) (\x, f (x x))) TIMES'
   = (\x, TIMES' (x x)) (\x, TIMES' (x x))
   = TIMES' ((\x, TIMES' (x x)) (\x, TIMES' (x x)))
   = TIMES' (TIMES' ((\x, TIMES' (x x)) (\x, TIMES' (x x))))
   = ...
 *)


Example cbv_Y :=
  <{ (\f, (\x, \y, f (x x) y) (\x, \y, f (x x) y)) }>.


(** ** Translation *)

(**
   - At this point, we have seen two orders of evaluation: call-by-value and
     call-by-need.
   - We might want to translate terms under one semantics into terms in another
     another.
   - This is called *translation*.
   - You may have heard of the terms *transpiling* or even *compiling*

 *)


(** *** Call-by-name to Call-by-value
   
   - The translation is given below and does something called *thunking*.
   - Thunking delays evaluation by wrapping arguments to functions with
     a lambda. We then have to call variables with a throw-away argument
     to force evaluation when it is used.
 *)


Definition fresh_var (vars: set string): string :=
  set_fold_left (fun b a => append b a) vars z.

Fixpoint cbn_to_cbv (t: tm): tm :=
  match t with
  | tm_var y =>
      <{ y (\x, x) }>                  
  | <{\y, t1}> =>
      let t1' := cbn_to_cbv t1 in
      <{ \y, t1' }>
  | <{t1 t2}> =>
      let t1' := cbn_to_cbv t1 in
      let t2' := cbn_to_cbv t2 in
      let fv := free_var t2 in
      if set_mem string_dec z fv
      then
        let z' := fresh_var (free_var t2) in
        <{ t1' (\z', t2') }>
      else <{ t1' (\z, t2') }>  (* thunking *)
  end.

Print ex1.
Eval compute in cbn_to_cbv ex1.

Print ex2.
Eval compute in cbn_to_cbv ex2.

Print ex3.
Eval compute in cbn_to_cbv ex3.

Print ex4.
Eval compute in cbn_to_cbv ex4.

Print Omega.
Eval compute in cbn_to_cbv Omega.


(** *** Adequacy of translation

   - Soundness: 
     [forall t \in tm, if translate[e] ==> v' then \exists v. e ===> v]
     and [v'] equivalent to [v].

   - Completeness:
     [forall t \in tm, if e ===> v then \exists v', translate[e] ==> v']
     and [v'] equivalent to [v].

   - Equivalence is a notion that you will have to define. We will look at
     *contextual equivalence* later which is a powerful and general method for
     defining equivalence.
 *)


(** ** Extending Lambda Calculi *)

(**
   - Now that we have a notion of translation, we can extend Lambda
     Calculus with more terms.
   - This won't increase the computational power of Lambda Calculus---it
     is already Turing complete.
   - However, it will allow us to reason about programs at a higher-level
     of abstraction.
   - For example, we might not want to reason about Church encodings all
     the time.
 *)

Inductive tm' : Type :=
| tm_var' : string -> tm'             (* variable *)
| tm_app' : tm' -> tm' -> tm'         (* application *)
| tm_abs' : string -> tm' -> tm'      (* abstraction *)
| tm_true' : tm'                      (* true *)
| tm_false' : tm'                     (* false *)
| tm_if' : tm' -> tm' -> tm' -> tm'   (* if *)
.

(**
   - However, the downside is that our language is now larger.
   - And we will need to define new functions / semantics.
   - We've updated substitution to work with the larger language.
 *)

Fixpoint subst' (x: string) (s: tm') (t: tm') : tm' :=
  match t with
  | tm_var' y =>
      if eqb_string x y then s else t
  | tm_abs' y t1 =>
      if eqb_string x y then t else tm_abs' y (subst' x s t1)
  | tm_app' t1 t2 =>
      tm_app' (subst' x s t1) (subst' x s t2)
  | tm_true' =>
      tm_true'
  | tm_false' =>
      tm_false'
  | tm_if' tcond ttrue tfalse =>
      tm_if' (subst' x s tcond) (subst' x s ttrue) (subst' x s tfalse)
  end.

(**
   - Our space of values also changes.
   - In particular, we have boolean values now.
 *)

Inductive value' : tm' -> Prop :=
| v_abs' : forall x t1,
    value' (tm_abs' x t1)
| v_true' :
  value' tm_true'
| v_false' :
  value' tm_false'.
              
(**
   - And our semantics needs to be extended as well ...
   - Here is the updated small-step semantics.
 *)

Reserved Notation " t '~-->' t' "
                  (at level 40, t' at level 39).
Inductive cbv_step' : tm' -> tm' -> Prop :=
| _cbv_app1 : forall t1 t2 t1',
    t1 ~--> t1' ->
    tm_app' t1 t2 ~--> tm_app' t1' t2
| _cbv_app2 : forall v t2 t2',
    value' v ->
    t2 ~--> t2' ->
    tm_app' v t2 ~--> tm_app' v t2'
| _cbv_beta : forall x t v,
    value' v ->
    tm_app' (tm_abs' x t) v ~--> subst' x v t
| _if_cond : forall tcond ttrue tfalse tcond',
    tcond ~--> tcond' ->
    tm_if' tcond ttrue tfalse ~--> tm_if' tcond' ttrue tfalse
| _if_true : forall ttrue tfalse,
    tm_if' tm_true' ttrue tfalse ~--> ttrue
| _if_false : forall ttrue tfalse,
    tm_if' tm_true' ttrue tfalse ~--> tfalse
where " t '~-->' t' " := (cbv_step' t t').


(**
   - Finally we can perform a translation.
   - In other words, we can compile away the extra language features.
 *)

Fixpoint tm'_to_tm (t: tm'): tm :=
  match t with
  | tm_var' x =>
      tm_var x
  | tm_app' t1 t2 =>
      tm_app (tm'_to_tm t1) (tm'_to_tm t2)
  | tm_abs' x t =>
      tm_abs x (tm'_to_tm t)
  | tm_true' =>
      TRUE
  | tm_false' =>
      FALSE
  | tm_if' tcond ttrue tfalse =>
      let tcond' := (tm'_to_tm tcond) in
      let tt' := (tm'_to_tm ttrue) in
      let tf' := (tm'_to_tm tfalse) in
      <{ IF' tcond' tt' tf'  }>
  end.


(**
   - Naturally, we can aim to prove soundness and completeness of the
     translation.
   - We won't have the proof techniques powerful enough to show this
     yet though.
   - The essential problem is we won't know how to say that two lambda
     terms are equivalent.
 *)


(** ** Summary

   - We saw the Lambda Calculus, a notation for talking about variables.
   - We saw call-by-value and _call-by-need_ semantics.
   - We looked at various encodings in the Lambda Calculus and saw that
     it was Turing complete.
 *)
