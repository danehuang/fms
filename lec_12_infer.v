(** * More Types, Type-Checking, and Type-Inference *)

From Coq Require Import Strings.String.
Import Nat.
Require Import Maps.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Bool.Bool.

Require Import lec_11_stlc.

(** ** References

   - https://softwarefoundations.cis.upenn.edu/plf-current/MoreStlc.html
   - https://softwarefoundations.cis.upenn.edu/plf-current/Typechecking.html
   - https://softwarefoundations.cis.upenn.edu/plf-current/References.html

 *)

(** ** Recap
    
   - Last time, we introduced STLC which took the Lambda calculus and layered
     a type-system on top.
   - The advantage was that we could get rid of stuck terms.
   - The disadvantage was that we lost expressive power.
   - Today, we'll introduce more types and also look into how to make
     type-systems practical by introducing algorithmic versions a la
     _type-checking_ and _type-inference_.

 *)


(** ** Goal for today

   - Introduce more simple types: let, unit, products/sums, and records.
   - Introduce reference types.
   - Introduce more type system extensions: parameteric polymorphism and subtyping.
   - Give _type-checking_ and _type-inference_ algorithms.

 *)


(** ** More Simple Types *)


(** *** Fix *)

Print tm.

(** **** Syntax *)
(*
    
    t ::= ...            (same as before and ...)
        | fix t          (fix-points)

 *)


(** **** Types

    - Nothing changes

 *)


(** **** Values
    
    - Nothing changes

 *)


(** **** Operational Semantics *)
(*

   same operational rules and ...

    
  ---------------------------------------------- ST_fix
    fix (\x: T, t) --> [x := fix (\x: T, t)] t

 *)


(** **** Typing Rules *)
(*

   same typing rules and ...

    Γ ⊢ t : T -> T
  ------------------ T_fix
    Γ ⊢ fix t : T

 *)


(** **** Example 1: Factorial *)
(*

 Γ ⊢ (\f: nat -> nat, \n: nat, if n == 0 then 0 else f (n-1)) : (nat -> nat) -> (nat -> nat)
  -------------------------------------------------------------------------------------- T_fix
     Γ ⊢ fix (\f: nat -> nat, \n: nat, if n == 0 then 0 else f (n-1)) : nat -> nat

 *)


(** **** Example 2: Non-termination *)
(*

     Γ ⊢ (\f: nat -> nat, \n: nat, f n) : (nat -> nat) -> (nat -> nat)
  ----------------------------------------------------------------------- T_fix
          Γ ⊢ fix (\f: nat -> nat, \n: nat, f n) : nat -> nat

 *)


(** *** Let *)

(** **** Syntax *)
(*
    
    t ::= ...            (same as before and ...)
        | let x=t in t   (let bindings)

 *)


(** **** Types

    - Nothing changes

 *)

Definition let_ex1: nat :=
  let x: nat := 1 in
  x + 1.

Eval compute in let_ex1.


Definition let_ex2: nat :=
  let x: bool := true in
  (let y: nat := if x then 1 else 2 in
   y).

Eval compute in let_ex2.


Definition let_ex3: bool :=
  let x: nat := 1 in
  let x: bool := true in  (* shadowing *)
  x.

Eval compute in let_ex3.

(** **** Values
    
    - Nothing changes

 *)

(** **** Operational Semantics *)
(*

   same operational rules and ...


                   t1 --> t1'
   ------------------------------------------ ST_Let1
     let x = t1 in t2 --> let x = t1' in t2 


                   value v1
   ------------------------------------------ ST_LetValue
        let x = t1 in t2 --> [x:= v1] t2

 *)


(** **** Typing Rules *)
(*

   same typing rules and ...

     Γ ⊢ t1 : T1  Γ, x : T1 ⊢ t2 : T2
  ------------------------------------- T_Let
        Γ ⊢ let x = t1 in t2 : T2

 *)


(** *** Unit *)


(** **** Syntax *)
(*
    
    t ::= ...            (same as before and ...)
        | ()             (unit)

 *)


(** **** Types *)
(*

    T ::= ...            (same as before and ...)
        | unit           (unit type)
   
 *)

Print unit.
Definition unit: unit := tt.


(** **** Values *)
(*
    
    v ::= ...            (same as before and ...)
        | ()             (unit)
  
 *)

(** **** Operational semantics

   - nothing changes

 *)

(** **** Typing rules *)
(*

   same typing rules and ...


  ------------------------------ T_Unit
             Γ ⊢ () : unit

 *)


(** *** Products *)

(** **** Syntax *)
(*
    
    t ::= ...            (same as before and ...)
        | (t, t)         (pair)
        | fst t          (first projection)
        | snd t          (second projection)

 *)

(** **** Types *)
(*

    T ::= ...            (same as before and ...)
        | T * T          (product type)
   
 *)


Definition prod1 : nat * bool := (1, true).

Definition prod2 : ((nat * bool) * nat) := ((1, true), 2).


(** **** Values *)
(*
    
    v ::= ...            (same as before and ...)
        | (v, v)         (pair)

 *)

(** **** Operational semantics *)
(*

   same operational rules and ...


            t1 --> t1'
   --------------------------- ST_Pair1
     (t1, t2) --> (t1', t2)



       value v1   t2 --> t2'
   --------------------------- ST_Pair2
     (v1, t2) --> (v1, t2')


             t --> t'
   --------------------------- ST_Fst1
         fst t --> fst t'


       value v1    value v2
   --------------------------- ST_FstPair
       fst (v1, v2) --> v1


             t --> t'
   --------------------------- ST_Snd1
         snd t --> snd t'


       value v1    value v2
   --------------------------- ST_SndPair
       snd (v1, v2) --> v1

 *)


(** **** Typing rules *)
(*

   same typing rules and ...


     Γ ⊢ t1 : T1     Γ ⊢ t2 : T2
  --------------------------------- T_Pair
       Γ ⊢ (t1, t2) : T1 * T2


       Γ ⊢ t : T1 * T2
  ------------------------- T_Fst
       Γ ⊢ fst t : T1


       Γ ⊢ t : T1 * T2
  ------------------------- T_Fst
       Γ ⊢ snd t : T2

 *)


Eval compute in fst ((1 + 1, true), 2).


(** *** Sums *)

(** **** Syntax *)
(*

    t ::= ...            (same as before and ...)
        | inl T t        (inject left)
        | inr T t        (inject right)
        | case t of
          | inl x => t
          | inr y => t   (case)

 *)

(** **** Types

    T ::= ...            (same as before and ...)
        | T + T          (sum type)
   
 *)


Definition sum1 : nat + bool := inl 1.

Definition sum2 : nat + bool := inr true.

Definition sum3 (x: nat + bool) : bool + nat :=
  match x with
  | inl n => inr n
  | inr b => inl b
  end.
  

(** **** Values
    
    v ::= ...            (same as before and ...)
        | inl T v        (inject left)
        | inr T v        (inject right)

 *)


(** **** Operational semantics *)
(*

   same operational rules and ...

             t1 --> t1'
   ---------------------------- ST_Inl
     inl T2 t1 --> inl T2 t1'


             t2 --> t2'
   ---------------------------- ST_Inr
     inr T1 t2 --> inr T1 t2'


                      t0 --> t0'
   ---------------------------------------------- ST_Case
     case t0 of inl x1 => t1 | inr x2 => t2 -->	
      case t0' of inl x1 => t1 | inr x2 => t2	


                                  value v1
   --------------------------------------------------------------------- ST_Case
     case (inl T2 v1) of inl x1 => t1 | inr x2 => t2 --> [x1 := v1]t1


                                  value v2
   --------------------------------------------------------------------- ST_Case
     case (inr T1 v2) of inl x1 => t1 | inr x2 => t2 --> [x2 := v2]t2

 *)


(** **** Typing rules *)
(*

  same typing rules and ...

              Γ ⊢ t1 : T1
  --------------------------------- T_Inl
       Γ ⊢ inl T2 t1 : T1 + T2


              Γ ⊢ t2 : T2
  --------------------------------- T_Inr
       Γ ⊢ inr T1 t2 : T1 + T2


     Γ ⊢ t0 : T1 + T2   Γ, x1: T1 ⊢ t1 : T3   Γ, x2: T2 ⊢ t3 : T3
  ------------------------------------------------------------------ T_Case
          Γ ⊢ case t0 of inl x1 => t1 | inr x2 => t2 : T3

 *)



(** *** Records *)

(** **** Syntax *)
(*
    
    t ::= ...               (same as before and ...)
        | {x=t, ..., x=t}   (record)
        | t.x               (projection)

 *)


(** **** Types *)
(*

    T ::= ...               (same as before and ...)
        | {x: T, ..., x: T} (record type)
   
 *)


Record recTy1 : Set :=
  mkRecTy1
    {
      field1: nat
    }.

Definition rec1 : recTy1 :=
  {|
    field1 := 1
  |}.


Record recTy2 : Set :=
  mkRecTy2
    {
      field2: nat;
      field3: bool
    }.

Definition rec2 : recTy2 :=
  {|
    field2 := 1;
    field3 := true;
  |}.


(** **** Values *)
(*
    
    v ::= ...               (same as before and ...)
        | {x=v, ..., x=v}   (unit)
  
 *)


(** **** Operational Semantics *)
(*

   same operational rules and ...

                   value v_1  ...  value v_{i-1}  t_i --> t_i'
   ---------------------------------------------------------------------------- ST_Rec
     {x_1=v_1, ..., x_i=v_{i-1}, x_i=t_i, x_{i+1}=t_{i+1}, ... x_n=t_n} -->
        {x_1=v_1, ..., x_i=v_{i-1}, x_i=t_i', x_{i+1}=t_{i+1}, ... x_n=t_n}


          t --> t'
   -------------------- ST_ProjRec1
       t.x --> t'.x


                   value v_1  ...  value v_n
   ---------------------------------------------------- ST_ProjRec2
     {x_1=v_1, ..., x_i=v_i, ... x_n=v_n}.x_i --> v_i

 *)


(** **** Typing Rules *)
(*

   same typing rules and ...

               Γ ⊢ t_1 : T_1  ... Γ ⊢ t_n : T_n  
  --------------------------------------------------------- T_Rec
    Γ ⊢ {x_1=t_1, ..., x_n=t_n} : {x_1:T_1, ..., x_n: T_n}

 *)


(** *** Reference Types *)

(** **** Syntax *)
(*
    
    t ::= ...               (same as before and ...)
        | ref t             (create reference)
        | !t                (read reference)
        | t := t            (write reference)

 *)

(** **** Types *)
(*

    T ::= ...               (same as before and ...)
        | Ref t             (reference type)
   
 *)

(** **** Examples?

    - Coq does not have references!
    - We can use a programming model called _monads_ to model state.
    - This is a programming model that is used in Haskell.

 *)


(** **** Stores

    - A _store_, or computer memory, is modeled as a list of terms.
    - Each cell can be accessed by referencing it's _location_.
    - Thus a _location_ can be modeled as a natural number.
    - This should remind of us the identifiers from IMP which were modeled as strings.
*)
(*

    ---------------
    | | | | | | | |
    ---------------
       ^
       |
    location
       
 *)


(** **** Values *)
(*

    v ::= ...               (same as before and ...)
        | loc l             (location)
    
 *)


(** **** Operational semantics

   - Just like IMP, we now need to define operational semantics involving
     transformations on state.
   - With STLC + references, we will also need to involve the term reduction.
   - Thus every operational rule will transform pairs of states and terms
     to pairs of states and terms.
*)
(*
                  
          (σ, t) --> (σ' ,t')
   -------------------------------- ST_Ref1
      (σ, ref t) --> (σ', ref t')


          value v     σ' = σ ++ [v]
   ------------------------------------------- ST_Ref2
      (σ, ref v) --> (σ', loc (length σ'))


          (σ, t) --> (σ ,t')
   -------------------------------- ST_Deref1
         (σ, !t) --> (σ, !t')


              l < length σ
   -------------------------------- ST_Deref2
       (σ, !loc l) --> (σ, σ[l])


           (σ, t1) --> (σ, t1')
   ------------------------------------ ST_Assign1
     (σ, t1 := t2) --> (σ, t1' := t2)


      value v1   (σ, t2) --> (σ, t2')
   ------------------------------------ ST_Assign2
     (σ, v1 := t2) --> (σ, v1 := t2')


       value v2   σ' = update σ l v2
   ------------------------------------ ST_Assign3
         (σ, loc l := v2) --> (σ', ())

 *)


(** **** Store Typings Wrong *)
(*
         Γ; σ ⊢ σ[l] : T
   -------------------------- WrongRef
      Γ; σ ⊢ loc l : Ref T
*)
(**
    - Intuitively, we might want to say that the type of a location is the
      the type of the term stored in that cell.
    - However, this rule fails to deal with cycles.
 *)


(** **** Infinite Derivation with Cycles *)
(*   
   Suppose σ = [\x:unit. !(loc 1), \x:unit. !(loc 0)]

                                     .
                                     .
                                     .
    ------------------------------------------------------------------- WrongRef
                    Γ, x: unit, x: unit; σ ⊢ !loc 0 : T3
    ------------------------------------------------------------------- Abs
              Γ, x: unit; σ ⊢ \x:unit. !(loc 0) : unit -> T3
    ------------------------------------------------------------------- WrongRef
                     Γ, x: unit; σ ⊢ !(loc 1) x : T2
    ------------------------------------------------------------------- Abs
                 Γ; σ ⊢ \x:unit. !(loc 1) : unit -> T2 
    ------------------------------------------------------------------- WrongRef
                        Γ; σ ⊢ !(loc 0) : Ref T1
 *)


(** **** Store Typing

   - We will need to introduce an idea called a *store typing* Σ.
   - A store typing maps each location to a type.
   - This breaks the cyclic self-reference with using a concrete store σ.
 *)
(*

         Γ; Σ ⊢ Σ[l] : T
   -------------------------- TLoc
      Γ; Σ ⊢ loc l : Ref T


          Γ; Σ ⊢ t : T
   -------------------------- TRef
      Γ; Σ ⊢ ref t : Ref T


         Γ; Σ ⊢ t : Ref T
   -------------------------- TDeref
          Γ; Σ ⊢ !t : T


        Γ; Σ ⊢ t1 : Ref T    Γ; Σ ⊢ t2 : T
   ------------------------------------------ TAssign
              Γ; Σ ⊢ t1 := t2 : unit
   
 *)

(** **** Fixing Infinite Derivations with Store Typings
   
   - Suppose σ = [\x:unit. !(loc 1), \x:unit. !(loc 0)]
   - We can use Σ = [unit -> unit -> unit, unit -> unit -> unit]

 *)
(*

                    Γ; Σ ⊢ Σ[0] : unit -> unit -> unit
    ------------------------------------------------------------------- WrongRef
             Γ; Σ ⊢ !(loc 0) : Ref (unit -> unit -> unit)

 *)


(** **** Progress and Preservation?
   
   - Unlike all the previous extensions, references change our
     operational semantics and typing relation substantially.
   - Consequently, we might wonder if progress and preservation still hold.
   - First, how do we even state progress and preservation?

 *)

(** **** Preservation Wrong
   
   - A first attempt at phrasing preservation might look like the following:

     ∀ Σ T t σ t' σ',
       empty ; Σ ⊢ t : T ->
       (σ, t) --> (σ', t') ->
       empty ; Σ ⊢ t' : T.

   - This isn't quite right because we are not relating the store typing Σ
     and a concrete store σ.
   - We will need an extra condition that relates the two.

 *)


(** **** Well-Formed Stores *)
(*
   
      dom(Σ) = dom(σ)   ∀ l \in dom(σ), empty; Σ ⊢ σ[l] : Σ[l]
    -------------------------------------------------------------
                               Σ ⊢ σ
 *)


(** **** Preservation Wrong 2
   
   - A second attempt at phrasing preservation might look like the following:

     ∀ Σ T t σ t' σ',
       Σ ⊢ σ ->
       empty ; Σ ⊢ t : T ->
       (σ, t) --> (σ', t') ->
       empty ; Σ ⊢ t' : T.

   - The reason this is wrong is because ref t creates a larger store.
   - Similar to a "weakening" lemma on contexts, we need to define
     extensions of store typings.

 *)


(** **** Preservation Right 
   
   - The correct statement of preservation is given below:

     ∀ Σ T t σ t' σ',
       Σ ⊢ σ ->
       empty ; Σ ⊢ t : T ->
       (σ, t) --> (σ', t') ->
       ∃ Σ',
         Σ' ⊢ σ' /\
         Σ ⊆ Σ' /\
         empty ; Σ ⊢ t' : T.

 *)



(** ** Complex Types *)

(** *** Parametric Polymorphism *)

(** **** Syntax *)
(*
    
    t ::= ...               (same as before and ...)
        | ΛX.t              (type abstraction)
        | t[T]              (type application)

 *)

(** **** Types *)
(*
    T ::= ...               (same as before and ...)
        | ∀X.T              (polymorphic type)
   
 *)

Definition id: forall A: Type, A -> A :=
  fun (A: Type) => fun (x: A) => x.

Definition id' (A: Type) (x: A): A :=
  x.

Definition swap: forall A: Type, forall B: Type, A * B -> B * A :=
  fun (A: Type) => fun (B: Type) => fun (p: A * B) => (snd p, fst p).

Definition swap' (A B: Type) (p: A * B): B * A :=
  (snd p, fst p).


(** **** Values *)
(*

    v ::= ...               (same as before and ...)
        | ΛX.t              (type abstraction)
  
 *)


(** **** Operational semantics *)
(*

   same operational rules and ...

                
   ---------------------------- ST_TypeRed
       (ΛX.t)[T] --> [X:=T]t

 *)


(** **** Type abstraction contexts

   - Similar to lambda abstractions, we need to ensure that our type variables
     are well-formed.
   - We do this with type variable contexts Δ, which is a set of type variables
     in scope.

*)


(** **** Typing rules *)
(*

   similar typing rules where we use Δ and


     Δ, X; Γ ⊢ t : T   fv(T) ⊆ Δ, X
  ------------------------------------ T_TypeAbs
             Δ; Γ ⊢ ΛX.t : ∀X.T


     Δ; Γ ⊢ t : ∀X.T1   fv(T1) ⊆ Δ
  ------------------------------------ T_TypeApp
       Δ; Γ ⊢ t[T2] : [X := T2]T1

 *)


(** *** Subtyping *)


(** **** Subsumption  *)
(*    

         Γ ⊢ t : T1   T1 ≤ T2
  -------------------------------- T_Subsume
             Γ ⊢ t: T2
 *)


(** **** Subtyping structural rules *)
(*    

  -------------- Refl
      T ≤ T


      T1 ≤ T2    T2 ≤ T3
  ------------------------- Trans
          T1 ≤ T3

 *)


(** **** Subtyping on Records *)
(*

                            perm is permutation
  -------------------------------------------------------------------- Sub_REc
    {x_1=t_1, ..., x_{n+k}=t_{n+k}} ≤ perm({x_1:T_1, ..., x_n: T_n})

 *)

(** **** Subtyping on Products *)
(*

       T1 ≤ T1'    T2 ≤ T2'
  ----------------------------- Sub_Prod
      (T1, T2) ≤ (T1', T2')

 *)

(** **** Subtyping on Functions *)
(*

       T1' ≤ T1     T2 ≤ T2'
  ----------------------------- Sub_Prod
      T1 -> T2 ≤ T1' -> T2'
*)
(**
   - Contravariant in input type
   - Covariant in return type
 *)


(** ** Type-Checking 

   - The typing rules give us a way to separate well-typed terms from
     stuck terms.
   - But we don't have an algorithm.
   - We now show that we can make this algorithmic by giving a
     _type-checking_ algorithm
*)

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | <{ Bool }> , <{ Bool }> =>
      true
  | <{ T11 -> T12 }>, <{ T21 -> T22 }> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.


Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T. induction T; simpl.
  reflexivity.
  rewrite IHT1. rewrite IHT2. reflexivity.
Qed.


Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1 = T1_1->T1_2 *)
    rewrite andb_true_iff in H0.
    inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1.
    apply IHT1_2 in Hbeq2.
    subst...
Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      Gamma x
  | <{\x:T2, t1}> =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | Some T1 => Some <{T2 -> T1}>
      | _ => None
      end
  | <{t1 t2}> =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some <{T11 -> T12}>, Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | <{true}> =>
      Some <{Bool}>
  | <{false}> =>
      Some <{Bool}>
  | <{if guard then t else f}> =>
      match type_check Gamma guard with
      | Some <{Bool}> =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.


Eval compute in type_check empty <{true}>.
(* ==> Some <{ Bool }> *)

Eval compute in type_check empty <{\x: Bool, x}>.
(* ==> Some <{ Bool -> Bool }> *)

Eval compute in type_check empty <{\x: Bool, \x: Bool, x x}>.
(* ==> None *)

Eval compute in type_check empty <{\f: Bool -> Bool, \x: Bool, f x}>.
(* ==> Some <{ (Bool -> Bool) -> Bool -> Bool }> *)


(**
   - We should check that our algorithm and our typing rules match.
   - We do this by showing that our type-checker is sound for the given
     typing rules.
*)
Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  Gamma ⊢ t \in T.
Proof with eauto.
  intros Gamma t.
  generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  {
    (* var *)
    rename s into x.
    destruct (Gamma x) eqn:H.
    rename t into T'.
    inversion H0; subst.
    eauto.
    inversion H0.
  }
  {
    (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|].                       
    destruct T1 as [|T11 T12].
    inversion H0. 
    remember (type_check Gamma t2) as TO2.
    destruct TO2.    
    destruct (eqb_ty T11 t) eqn: Heqb.
    apply eqb_ty__eq in Heqb; subst.
    inversion H0; subst; eauto.
    inversion H0.
    inversion H0.
    inversion H0.
  }
  {
    (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2.
    inversion H0; subst. auto.
    inversion H0.
  }
  {
    (* tru *)
    eauto.
  }
  {
    (* fls *)
    eauto.
  }
  {
    (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|].
    destruct Tc.
    destruct TO1 as [T1|].
    destruct TO2 as [T2|].
    destruct (eqb_ty T1 T2) eqn:Heqb. inversion H0; subst.
    apply eqb_ty__eq in Heqb; subst. auto.
    inversion H0.
    inversion H0.
    inversion H0.
    inversion H0.
    inversion H0.
  }
Qed.


(**
   - We can also show completeness!
   - That is, if there exists a derivation, our type-checker will verify it.
*)
Theorem type_checking_complete : forall Gamma t T,
  Gamma ⊢ t \in T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  (* Question: what should we do induction on? *)





  
  induction Hty; simpl.
  {
    (* T_Var *)
    destruct (Gamma x) eqn:H0; assumption.
  }
  {
    (* T_Abs *)
    rewrite IHHty; auto.
  }
  { (* T_App *)
    rewrite IHHty1.
    rewrite IHHty2.
    rewrite (eqb_ty_refl T2); auto.
  }
  {
    (* T_True *)
    eauto.
  }
  {
    (* T_False *)
    eauto.
  }
  {
    (* T_If *)
    rewrite IHHty1.
    rewrite IHHty2.
    rewrite IHHty3.
    rewrite (eqb_ty_refl T1); auto.
  }
Qed.



(** ** Type-Inference 

   - The goal of type-inference is to have an algorithm that gives
     us the types of terms without us having to write them down.
   - We define a new syntax of types that contains guesses.
   - We define a typing relation that generates *constraints* involving guesses.
   - We solve for the constraints using *unification* producing a type substitution.
   - The resulting type substitution gives us the types.
 *)

Module TypeInfer.

  Require Import List.
  Require Import Coq.Lists.ListSet.
  
  (** *** Updated Syntax for Types *)
  (*
     
     T ::= Bool
         | T -> T
         | X                    (* guess *)

   *)
  
  Inductive ty : Type :=
  | Ty_Bool : ty                (* for the boolean values *)
  | Ty_Arrow : ty -> ty -> ty   (* t1 -> t2, for the abstraction values *)
  | Ty_Var : string -> ty       (* guess *)
  .


  (** *** Types now have free variables
     
     - We could compute free variables in terms.
     - Now that types have variables, we have a similar notion.

   *)

  Fixpoint free_var (t: ty) : set string :=
    match t with
    | Ty_Bool =>
        empty_set string
    | Ty_Arrow t1 t2 =>
        set_union string_dec (free_var t1) (free_var t2)
    | Ty_Var X =>
        set_add string_dec X (empty_set string)
    end.

  
  (** *** Terms use new Types *)
  (*
     
     t ::= x
        | t t
        | \x: T. t
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


  (** *** Syntax for constraints *)
  (*

      C ::= T = T    (type equality)

   *)
  Inductive constraint : Type :=
  | Ty_eq : ty -> ty -> constraint.


  (** *** Free variables for constraints
      
      - We can collect the free variables in the types in a constraint.
        and lists of constraints.

   *)
  
  Fixpoint free_var_constraint (c: constraint) : set string :=
    match c with
    | Ty_eq t t' => set_union string_dec (free_var t) (free_var t')
    end.
      
  Definition free_var_constraints (cs: list constraint) : set string :=
    List.fold_left (fun acc x => set_union string_dec acc x) (List.map free_var_constraint cs) (empty_set string).

  (** *** Typing Relation with Constraints *)
  (*

              Γ(x) = T
        -------------------- T_Var
            Γ ⊢ x: T ~> {}
      

             Γ, x: T2 ⊢ t: T1 ~> C
        ------------------------------- T_Abs
         Γ ⊢ \x: T2, t: T2 -> T1 ~> C
      

           Γ ⊢ t1: T2 ~> C1    Γ ⊢ t2: T1 ~> C2   X ∉ fv(C1 ∪ C2)
        ----------------------------------------------------------- T_App
                  Γ ⊢ t1 t2: T1 ~> C1 ∪ C2 ∪ {T2 = T1 -> X}


              
        --------------------------- T_True
            Γ ⊢ true: Bool ~> {}


        --------------------------- T_False
            Γ ⊢ false: Bool ~> {}


           Γ ⊢ t1 : Bool ~> C1    Γ ⊢ t2 : T ~> C2   Γ ⊢ t3 : T ~> C3
        ---------------------------------------------------------------- T_False
                           Γ ⊢ if t1 t2 t3: T ~> C1 ∪ C2 ∪ C3

   *)
  
  Definition context := partial_map ty.
  
  Inductive has_typeC : context -> tm -> ty -> list constraint -> Prop :=
  | T_Var : forall Gamma a T1,
      Gamma a = Some T1 ->
      has_typeC Gamma (tm_var a) T1 nil
  | T_Abs : forall Gamma x T1 T2 t1 C,
      has_typeC (x |-> T2 ; Gamma) t1 T1 C ->
      has_typeC Gamma (tm_abs x T2 t1) (Ty_Arrow T2 T1) C
  | T_App : forall T1 T2 Gamma t1 t2 C1 C2 X,
      has_typeC Gamma t1 (Ty_Arrow T2 T1) C1 ->
      has_typeC Gamma t2 T2 C2 ->
      set_mem string_dec X (free_var_constraints (C1 ++ C2)) = false ->
      has_typeC Gamma (tm_app t1 t2) T1 (C1 ++ C2 ++ (Ty_eq T2 (Ty_Arrow T1 (Ty_Var X)) :: nil))
  | T_True : forall Gamma,
      has_typeC Gamma tm_true Ty_Bool nil
  | T_False : forall Gamma,
      has_typeC Gamma tm_false Ty_Bool nil
  | T_If : forall t1 t2 t3 T1 Gamma C1 C2 C3,
      has_typeC Gamma t1 Ty_Bool C1 ->
      has_typeC Gamma t2 T1 C2 ->
      has_typeC Gamma t3 T1 C3 ->
      has_typeC Gamma (tm_if t1 t2 t3) T1 (C1 ++ C2 ++ C3).


  (** *** Interpreting Type Variables
      
      - Just like we might interpret variables in a term with an environment,
        we can interpret type variables in a type variable with an environment.

   *)
  
  Definition type_context := partial_map ty.
  
  Fixpoint type_substitution (ty_ctx: type_context) (t: ty) :=
    match t with
    | Ty_Bool => Ty_Bool
    | Ty_Arrow t1 t2 => Ty_Arrow (type_substitution ty_ctx t1) (type_substitution ty_ctx t2)
    | Ty_Var x =>
        match (ty_ctx x) with
        | Some ty => ty
        | None => Ty_Var x
        end
    end.

  Definition type_substitution_constraints (ty_ctx: type_context) (constraints: list constraint) :=
    List.map
      (fun c =>
         match c with
         | Ty_eq t1 t2 => Ty_eq (type_substitution ty_ctx t1) (type_substitution ty_ctx t2)
         end) constraints.
  
  
  (** *** Unification

     - Now we reach the famous Hindley-Milner unification algorithm.
     - If a type substitution exists, then unification finds it, and the term
       with that type under that type substitution has a typing derivation.
     - If a type substitution does not exist, then unification will return None,
       and the term does not have a typing derivation.
     - It is a remarkably simple algorithm.
     - Note that it is not easy to show that this algorithm terminates in Coq,
       so we pass in some fuel.

   *)
  Fixpoint unify (n: nat) (constraints: list constraint) (ty_ctx: type_context): option type_context :=
    match n with
    | O => None
    | S n' =>
        match constraints with
        | nil => Some ty_ctx
        | c::constraints' =>
            match c with
            | Ty_eq Ty_Bool Ty_Bool =>
                unify n' constraints' ty_ctx
            | Ty_eq (Ty_Var X) t' =>
                if set_mem string_dec X (free_var t')
                then None
                else
                  let ty_ctx' := X |-> t' ; ty_ctx
                  in
                    unify n' (type_substitution_constraints ty_ctx' constraints') ty_ctx'
            | Ty_eq t (Ty_Var X) =>
                if set_mem string_dec X (free_var t)
                then None
                else
                  let ty_ctx' := X |-> t ; ty_ctx
                  in
                    unify n' (type_substitution_constraints ty_ctx' constraints') ty_ctx'
            | Ty_eq (Ty_Arrow t1 t2) (Ty_Arrow t1' t2') =>
                (**
                   - This case increases the constraints lists.
                   - Hence we need to do the "fuel" trick.
                 *)
                unify n' (constraints' ++ (Ty_eq t1 t1'::Ty_eq t2 t2'::nil)) ty_ctx
            | Ty_eq _ _ =>
                None
            end
        end
    end.

  
  (** *** Example 1: no constraints *)
  Definition u1 := unify 100 nil empty.
  Eval compute in u1.


  (** *** Example 2: single constraint *)
  Definition u2 := unify 100 (Ty_eq (Ty_Var "X") Ty_Bool::nil) empty.
  
  Eval compute in
    (match u2 with
     | Some ctx => ctx "X"%string
     | None => None
     end).

  Eval compute in
    (match u2 with
     | Some ctx => ctx "Y"%string
     | None => None
     end).  


  (** *** Example 3: consistent constraints *)
  Definition constraints3 :=
    Ty_eq (Ty_Var "X") Ty_Bool::
    Ty_eq (Ty_Arrow Ty_Bool Ty_Bool) (Ty_Arrow Ty_Bool (Ty_Var "X"))::
    nil.      

  Definition u3 := unify 100 constraints3 empty.

  Eval compute in
    (match u3 with
     | Some ctx => ctx "X"%string
     | None => None
     end).

  Eval compute in
    (match u3 with
     | Some ctx => ctx "Y"%string
     | None => None
     end).  

   (** *** Example 4: inconsistent constraints *)
  Definition constraints4 :=
    Ty_eq (Ty_Var "X") Ty_Bool::
    Ty_eq (Ty_Arrow Ty_Bool Ty_Bool) (Ty_Arrow Ty_Bool (Ty_Arrow Ty_Bool (Ty_Var "X")))::
    nil.  

  Definition u4 := unify 100 constraints4 empty.

  Eval compute in u4.
  

  (**     
     - Hindley-Milner type inference has the property that
       it returns the minimal substitution that makes the term
       typeable.
     - And, if the term is not typeable, then it returns None.
   *)
  
End TypeInfer.

  
(** ** Summary

   - More simple types
     * FIx
     * Let / Unit
     * Products / Sums
     * Records
   - Reference Types (problem of cycles)
   - Complex extensions
     * Parametric Polymorphism
     * Subtyping
   - Type-Checking
   - Type-Inference
 *)
