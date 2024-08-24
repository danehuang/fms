(** * Functional Programming in Coq *)


(** ** References

   - https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html
   - https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html
 *)


(** ** Recap

  - Last time, we saw that we could define basic data types in Coq including
  booleans and natural numbers.
  - These data types are *syntactic* objects that have no *semantics*, i.e.,
  meaning associated with them.
  - We had to prove proerties of those data types to show that booleans indeed
  behaved liked booleans and naturals behaved like natural numbers.
  - Before we can explore the rich world of mechanized proofs, we will need to
  get more comfortable defining complex data types and operations on them.
*)


(** ** Goal for today

  - More data types in Coq including product and lists
  - Polymorphism in Coq
  - Higher-order functions in Coq
 *)


(** ** Pair of natural numbers *)

Module NatProd.

Inductive natprod: Type :=
| mkNatProd : nat -> nat -> natprod.

Check mkNatProd 0 2.

Check mkNatProd 20 13.

(**
  - We can now make tuples with the *constructor* [mkNatProd].
  - We may also refer to [mkNatProd] as an *introduction* form.
  - How do we compute with natprod? We may need a rule for *eliminating* them.
 *)

Definition fst (p: natprod): nat :=
  match p with          (* we can pattern match even if there is only 1 case *)
  | mkNatProd n _ => n  (* _ means we don't care what it is *)                    
  end.

Check fst.
(* ==> natprod -> nat *)

Compute (fst (mkNatProd 0 1)).

Definition snd (p: natprod): nat :=
  match p with
  | mkNatProd _ n => n
  end.

Check snd.
(* ==> natprod -> bool *)

Compute (snd (mkNatProd 0 1)).


(**
  - Like our other inductive data types, we can check that natprod behaves
    like a product of natural numbers.
 *)

Theorem intro_elim1 :
  forall (n m: nat),
    fst (mkNatProd n m) = n.
Proof.
  intros n.
  intros m.
  simpl.
  reflexivity.
Qed.

Theorem intro_elim2 :
  forall (n m: nat),
    snd (mkNatProd n m) = m.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.


(**
  - Another "natural" oepration to perform on products is to swap their
    elements.
 *)

Definition swap (p: natprod): natprod :=
  match p with
  | mkNatProd n m => mkNatProd m n
  end.

(**
  - Like before, we should check that swap indeed has the behavior that
    we expect it to have.
 *)

Theorem swap_works1 :
  forall (p: natprod),
    fst p = snd (swap p).
Proof.
  intros p.
  destruct p.
  simpl.
  reflexivity.
Qed.

(**
  - We should expect a symmetric situation to hold for [snd p].
  - But before we do that, let's prove another theorem first. 
 *)

Theorem swap_swap_idempotent :
  forall (p: natprod),
    swap (swap p) = p.
Proof.
  intros p.
  destruct p.
  simpl.
  reflexivity.
Qed.

(**
  - Let's try to use [swap_swap_idempotent] to prove the other version of [swap_works1].
 *)

Theorem swap_works2 :
  forall (p: natprod),
    snd p = fst (swap p).
Proof.
  intros p.

  (* substitute all reference of fst p with snd (swap p) for any p *)
  rewrite swap_works1.

  (* substitute all references of swap (swap p) with p for any p *)
  rewrite -> swap_swap_idempotent.

  reflexivity.
Qed.


(** *** Summary

  - We defined pairs of natural numbers.
  - This is an example of an inductive type that has only one constructor.
  - We saw an example proof where we use previous theorems to prove the current one.
 *)


End NatProd.


(**
  - What is we want an arbitrary number of natural numbers?
  - We accomplish this with list data types.
  - Lists are a fundamental data structure. It can, for example, be used
    to model an idealized version of computer memory where the address is an
    integer index and the contents is a natural number. That natural number
    can be interpreted as encoding some value.
*)


(** ** List Types *)

Module NatList.

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.


Definition ls1 := nil.
Compute ls1.

Definition ls2 := cons 1 nil.
Compute ls2.

(* [2, 1] *)
Definition ls3 := cons 2 (cons 1 nil).
Compute ls3.

(* [1, 2] *)
Definition ls4 := cons 1 (cons 2 nil).
Compute ls4.


(**
  - As with natural numbers, we can define notation that will make it
    easier to work with lists.
 *)

Notation "[ ]" := nil.
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition ls1' := [].
Compute ls1'.

Definition ls2' := [1].
Compute ls2'.

Definition ls3' := [2; 1].  (* Note that lists are built in reverse. *)
Compute ls3'.


(**
  - We just defined an inductive datatype that we wish to interpret as a list.
  - As before, we need to define operations on that data type and then
    prove properties of those operations to show that the datatype can be
    interpreted with the usual semantics.
  - One of the first things we may want to do with lists is to take them apart.
 *)


(** 
  - The programming langauge for Coq, called Gallina, is a pure functional
    programming language. That means that every function in Coq must be _total_
    like a standard mathematical function.
  - We already run into a problem for getting the first element of a list, i.e.,
    the head of the list.
  - Namely, what do we do for an empty list?
 *)
Definition head (default: nat) (ls : natlist): nat :=
  match ls with
  | nil => default  (* return a default element for a list *)
  | hd :: tl => hd
  end.

Compute head 42 [].
Compute head 42 [1; 2; 3].


Definition tail (ls : natlist): natlist :=
  match ls with
  | nil => nil
  | hd :: tl => tl
  end.

Compute tail [].
Compute tail [1; 2; 3].


(** 
  - Some other operations we may want to perform on lists include getting
    its length and appending lists.
  *)

Fixpoint length' (ls: natlist): nat :=
  match ls with
  | nil => 0
  | cons _ tl => 1 + (length' tl)
  end.

(** 
  - We can also pattern match on our notation.
 *)

Print Nat.add.

Fixpoint length (ls: natlist) : nat :=
  match ls with
  | nil => 0
  | _ :: tl => 1 + (length tl) (* Question: what if we wrote S (length tl)? *)
                               (* Question: what if we wrote length tl + 1? *)
  end.

Fixpoint append (ls1 ls2: natlist): natlist :=
  match ls1 with
  | nil => ls2
  | hd :: tl => hd :: (append tl ls2)
  end.

(**
   - Some helpful notation for appending lists.
 *)
Notation "x ++ y" := (append x y) (right associativity, at level 60).

Compute [1] ++ [].
Compute [1; 2] ++ [3; 4].
Compute [1; 2; 3] ++ [4].


(** 
  - It's time to prove some theorems!
  - Let's start with [tail].
 *)

Check pred.
Print Nat.pred.

Theorem tl_length_pred :
  forall ls: natlist,
    pred (length ls) = length (tail ls).
Proof.
  intros ls.
  destruct ls as [| hd tl].
  - (* ls = nil *)
    simpl.
    reflexivity.
  - (* ls = cons hd tl *)
    simpl.
    reflexivity.
Qed.


(** 
  - What if we used [-] instead of [pred]?
*)

Theorem tl_length_minus1 :
  forall ls: natlist,
    length ls - 1 = length (tail ls).
Proof.
  intros ls.
  destruct ls as [| hd tl].
  - (* ls = nil *)
    simpl.
    reflexivity.
  - (* ls = cons hd tl *)
    simpl.

    Require Import Coq.Arith.Minus.
    Check minus_n_O.

    (* reflexivity no longer works! we need to use a theorem
       from the standard library. *)
    rewrite <- minus_n_O.
    reflexivity.
Qed.

(** 
  - Formal proofs are finicky ...
  - On one hand, we used [pred]. On the other hand, we used - 1.
  - Semantically they are equivalent. But all the proof assistant sees is a
    bunch of syntax.
  - The cost of rigour is extremely high!
*)


(** 
  - [natlist] is an example of recursive data structures.
  - [append] is a recursive function that operates on lists.
  - How do we prove stuff about list append?
*)

Theorem append_associative' :
  forall ls1 ls2 ls3: natlist,
    (ls1 ++ ls2) ++ ls3 = ls1 ++ (ls2 ++ ls3).
Proof.
  intros ls1 ls2 ls3.
  destruct ls1.
  - simpl.
    reflexivity.
  - simpl.
    (* Oh no, reflexivity does not work! *)
Abort.


(** 
  - While induction on natural numbers may be familiar, induction on lists
    may be less familiar.
  - Recall that every inductive type in Coq comes with an induction principle.
  - Let's recall the natural number induction principal first.
*)

Check nat_ind.
(*
  nat_ind:
  forall P : nat -> Prop,                for any proposition P on natural numbers
  P 0 ->                                 if P holds on 0
  (forall n : nat, P n -> P (S n)) ->    and if P (n + 1) holds assuming P n holds for any n
  forall n : nat, P n                    then we can conclude that P n holds for any n.
*)

(** 
  - Now let's look at the induction principal for lists.
  - Notice how similar it is to the one for natural numbers.
*)

Check natlist_ind.
(*
  natlist_ind:
  forall P : natlist -> Prop,            for any proposition P on natlist
  P [ ] ->                               if P holds on the empty list
  (forall (n : nat) (n0 : natlist),      and if P (n :: ls) holds assuming P ls holds
    P n0 -> P (n :: n0)) ->                for any list ls
  forall n : natlist, P n                then we can conclude that P ls holds for any ls.
*)


(** 
  - Let's compare and contrast the proof for + associative and append associative.
*)

Theorem plus_associative :
  forall n1 n2 n3: nat,
    (n1 + n2) + n3 = n1 + (n2 + n3).
Proof.
  intros n1 n2 n3.
  induction n1.
  - (* base case: n1 = 0 *)
    simpl.
    reflexivity.
  - (* inductive case: n1 = S n1 *)
    simpl.
    rewrite IHn1.
    reflexivity.
Qed.


Theorem append_associative :
  forall ls1 ls2 ls3: natlist,
    (ls1 ++ ls2) ++ ls3 = ls1 ++ (ls2 ++ ls3).
Proof.
  intros ls1 ls2 ls3.
  induction ls1.
  - (* base case: ls1 = [] *)
    simpl.
    reflexivity.
  - (* inductive case: ls1 = n :: ls5 *)
    simpl.
    (* We now have an inductive hypothesis IHls1 *)
    rewrite IHls1.
    reflexivity.
Qed.


(** 
  - It's the "same" proof!
  - Something to think about: how are naturals and lists related?
*)


Fixpoint reverse (ls: natlist): natlist :=
  match ls with
  | nil => nil
  | hd :: tl => reverse tl ++ [hd]
  end.


Theorem rev_length_attempt :
  forall ls: natlist,
    length (reverse ls) = length ls.
Proof.
  induction ls.
  - (* ls = nil *)
    simpl.
    reflexivity.
  - (* ls = cons *)
    simpl.
    (* We're stuck! We need a lemma. *)
Abort.


(** 
  - Sometimes when we prove a theorem, we need a Lemma.
  - We need something about append and length.
  - It's best to come up with the most general theorem statement possible.
*)

Lemma app_length :
  forall ls1 ls2 : natlist,
    length (ls1 ++ ls2) = (length ls1) + (length ls2).
Proof.
  intros ls1 ls2.
  induction ls1.
  - (* ls1 = nil *)
    simpl.
    reflexivity.
  - (* ls1 = cons *)
    simpl.
    rewrite -> IHls1.
    reflexivity.
Qed.


Theorem rev_length :
  forall ls: natlist,
    length (reverse ls) = length ls.
Proof.
  induction ls.
  - (* ls = nil *)
    simpl.
    reflexivity.
  - (* ls = cons *)
    simpl.
    rewrite -> app_length.
    simpl.
    Require Import Coq.Arith.Plus.
    rewrite plus_comm.  (* Using a "lemma" from another library *)
    simpl.
    rewrite IHls.
    reflexivity.
Qed.


End NatList.


(** ** Options *)

(**
  - In our definition of [head], we had to supply a default value.
  - We had to do this because Coq forces all functions to be total like
    in mathematics.
  - What if we want partial functions which are important in computation?
    We might get a partial function because of computational side-effects:
    errors, non-terminiation, etc. 
*)

Module NatOption.
  Import NatList.

  Print head.

  Inductive natoption : Type :=
  | Some (n : nat)
  | None.

  Definition head' (ls: natlist): natoption :=
    match ls with
    | [] => None
    | hd :: _ => Some hd
    end.

  Compute head' [].

  Compute head' [1; 2; 3].

End NatOption.
  


(** ** Polymorphism *)

(**
  - Up until now, we've just worked with products of naturals and lists of naturals.
  - In general, we can make products of naturals and integers. Or lists of
    rational numbers.
  - In other words, we'd like our data structures to hold any type T.
  - This is called *polymorphism*.
*)


Module PolyList.

Inductive list (X: Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.


Check list.
(*
   ==> [list: Type -> Type]
  
   Notice how list is no longer [Type] but [Type -> Type].
   In other words, we need to supply a Type.
 *)


Definition ls1 := nil.
Compute ls1.

Definition ls1' := nil nat.
Compute ls1'.

(** 
  - Compare [ls1] and [ls1'].
  - What's the difference in type?  
*)

Definition ls2 := cons nat 1 (nil nat).
Compute ls2.

Definition ls3 := cons nat 2 (cons nat 1 (nil nat)).
Compute ls3.


(**
  - Our functions on lists now need this extra type argument as well.
 *)

Print NatList.length.

Fixpoint length (X: Type) (ls: list X) : nat :=
  match ls with
  | nil _ => 0
  | cons _ _ tl => 1 + length X tl                              
  end.

(**
  - And so do our theorems ...
*)

Theorem length_cons:
  forall (X: Type) (ls: list X) (x: X),
    length X (cons X x ls) = 1 + length X ls.
Proof.
  intros.
  induction ls.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.  (* It's ok not to use the induction hypothesis! *)
                  (* This means we could have used destruct instead. *)
Qed.    

End PolyList.


(** ** Implicit Arguments *)

Module ImplicitPolyList.

  (**
    - Benefit of polymorphism is that it lets us write really general
      data types.
    - Downside of polymorphism is that we have all these extra type arguments
      floating around.
    - Enter _implicit arguments_.
  *)

  Inductive list {X: Type} : Type :=
  | nil : list
  | cons : X -> list -> list.

  Check list_ind.

  (** 
     - Notice that everything is the same.
     - We will just end up having extra syntactic support.
   *)

  Set Printing All.

  (* We can use the @ symbol to manually give the arguments *)
  Definition ls1 :=  @nil nat.
  Compute ls1.

  (* But Coq can infer it when the data type in the list can be inferred from context. *)
  Definition ls2 := cons 1 nil. 
  Compute ls2.

  Definition ls3 := cons 2 (cons 1 nil).
  Compute ls3.

  (** 
     - Rewriting the [length] function from before with implicit arguments.
     - Notice how many type arguments go away.
   *)
  
  Fixpoint length {X: Type} (ls: @list X) : nat :=
  match ls with
  | nil  => 0
  | cons _ tl => 1 + length tl                              
  end.

  Unset Printing All.

  (** 
     - This also works for Theorems.
   *)
  
  Theorem length_cons:
  forall (X: Type) (ls: @list X) (x: X),
    length (cons x ls) = 1 + length ls.
  Proof.
    intros.
    destruct ls.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

End ImplicitPolyList.


(**
  - Of course, the Coq standard library has lists and theorems on lists.
  - Note that what we formalized is different. 
*)
Print list.
Check list.


(** ** Polymorphic Product Types *)

Module PolyProd.

  (**
     - We can of course quantify over multiple generic types.
     - We'll show an example with products.
   *)

  Inductive prod (X Y: Type): Type :=
  | pair : X -> Y -> prod X Y. (* compare with previous definition *)
  
  (** Let's make the arguments implicit *)
  Arguments pair {X} {Y}.

  Print pair.
  Check pair.

  Check pair 0 true.
  (* ==> prod nat bool *)

  (** 
    - Still can give the implicit arguments explicitly.
   *)
  Check @pair nat bool 0 true.

  (**
     - Notation still works.
   *)
  Notation "( x , y )" := (pair x y).

  Check (false, 20).
  (* ==> prod nat bool *)

  Check (true, nat).
  (* ==> prod nat Type *)

  Definition fst {X Y: Type} (p: prod X Y): X :=
    match p with
    | pair x y => x
    end.

  Check fst.
  
  Definition snd {X Y: Type} (p: prod X Y): Y :=
    match p with
    | pair x y => y
    end.
  
  Theorem surjective_pairing :
    forall (X Y: Type) (p : prod X Y),
      p = (fst p, snd p).
  Proof.
    intros X Y p.
    destruct p as [x y].
    simpl.
    reflexivity.
  Qed.

End PolyProd.


(** ** Higher-Order Functions in Coq *)

Module HigherOrderFunctions.

  (**
     - We'll now introduce the concept of a _higher-order function_.
     - This might also be called _first-class function_.
     - And is related to *anonymous function*.
     - In my opinion, this is one of the most important abstractions ever
       developed.
     - You may be wondering why we talked about products and polymorphism
       before we talk about a special kind of function. These concepts will
       appear when we talk about higher-order functions.
   *)

  (**
     - Before we get to higher-order functions, it's helpful to introduce the
       idea of an  anonymous function first.
   *)

  Definition idNat (x: nat): nat :=
    x.

  Check idNat.
  
  Compute idNat 1.
  Compute idNat 2.

  (**
     - That was a lot of work to define an identity function.
     - In particular, we had to come up with a name for the function.
     - An _anonymous_ function provides a way to write a function without giving it a name.
   *)
  
  Check (fun x: nat => x).  (* idNat as an anonymous function *)
  Check (fun x: nat => x) 1.
  Check (fun x: nat => x) 2.
  

  (**
     - We can give an anonymous function a name by assigning it one.
     - If your language enables you to assign a function to a variable,
       then your language supports _first-class_ or _higher-order_ functions.
     - Note how the types change.
   *)
  Definition idNat' : nat -> nat :=
    fun x: nat => x.

  Check idNat'.
  Compute idNat' 1.
  Compute idNat' 2.

  (**
     - Wait ... can we make an anonymous function a body of another anonymous function?
   *)

  Check fun x: nat => (fun y: nat => y).
  Compute (fun x: nat => fun y: nat => y) 1.
  Compute (fun x: nat => fun y: nat => y) 1 2.

  Definition whatAmI : nat -> (nat -> nat) :=
    fun x: nat => fun y: nat => y.

  Definition whatAmI1 : nat -> nat :=
    whatAmI 1.

  Definition whatAmI2 : nat :=
    whatAmI1 2.

  Compute whatAmI.
  Compute whatAmI1.
  Compute whatAmI2.

  (**
     - And we can keep going for any natural n.
     - We have just arrived at higher-order functions.
   *)

  (** 
      - Does whatAmI look familiar?
      - It's exactly [snd] for nat prod!
      - Higher-order functions or lambdas are extremely powerful. They can be
        used to formulate any computation. We have just stumbled upon what is
        called a Church encoding for pairs.
      - Let's add the polymorphism back in.
   *)

  Definition churchPair {X Y P: Type}: X -> Y -> (X -> Y -> P) -> P :=
    fun x => fun y => fun p => p x y.
  
  Definition churchFst {X Y: Type} : ((X -> Y -> X) -> X) -> X :=
    fun p: (X -> Y -> X) -> X => p (fun x: X => fun y: Y => x).

  Definition churchSnd {X Y: Type} : ((X -> Y -> Y) -> Y) -> Y:=
    fun p: (X -> Y -> Y) -> Y => p (fun x: X => fun y: Y => y).
  
  
  Check churchFst (churchPair 1 true).
  Compute churchFst (churchPair 1 true).
  Compute churchSnd (churchPair 1 true).
  
  (** 
     - There is a deeper relation between higher-order functions and products.
   *)

  Locate "*".
  
  Definition curry {X Y Z: Type} (f: X * Y -> Z): X -> (Y -> Z) :=
    fun (x: X) => fun (y: Y) => f (x, y).

  Definition uncurry {X Y Z: Type} (f: X -> Y -> Z): X * Y -> Z :=
    fun p => f (fst p) (snd p).
  
  Theorem curry_uncurry :
    forall (X Y Z: Type),
    forall f: X -> Y -> Z,
      curry (uncurry f) = f.
  Proof.
    intros.
    unfold curry.   (* [unfold] tactic tells Coq to "unfold" the definition
                       in the context *)
    unfold uncurry.
    simpl.
    change (fun x y => f x y) with f.
    reflexivity.
  Qed.  
  
  (** 
     - Useful higher-order functions on lists.
   *)
  
  Fixpoint filter {X: Type} (predicate: X -> bool) (ls: list X) : list X :=
    match ls with
    | nil => nil
    | cons h t =>
        if predicate h
        then cons h (filter predicate t)
        else filter predicate t
    end.

  Fixpoint map {X Y: Type} (f: X -> Y) (ls: list X): list Y :=
    match ls with
    | nil => nil
    | cons hd tl => cons (f hd) (map f tl)
    end.
  
End HigherOrderFunctions.


(** ** Summary

  - We covered more data types in Coq including product, lists, and
    natural numbers.
  - We covered polymorphism in Coq.
  - We covered higher-order functions in Coq.
 *)
