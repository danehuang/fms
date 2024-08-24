(** * Turing Machines and Decidability *)


Add LoadPath "./cook-levin/coq-library-undecidability/theories/" as Undecidability.

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.
Require Import Vector List.

Unset Implicit Arguments.


(** ** References

   - Asperti & Ricciotti's "A formalization of multi-tape Turing machines" (2015)
   - https://uds-psl.github.io/cook-levin/
   - https://github.com/bmsherman/finite/blob/master/Iso.v
   
 *)


(** ** Recap
   
   - Last time, we saw the simplest abstraction machine: the DFA.
   - We also saw that DFAs recognized regular languages and that
     non-regular languages exist.
   - This begs the question: what would a more powerful machine look
     like?
   - Today, we'll see that this more powerful, and in fact, _universal_
     machine is the _Turing machine_.
 *)


(** ** Goal for today
   
   - We'll introduce Turing machines (TMs) and give big-step semantics.
   - We'll show that this notion of computation is robust.
   - We'll introduce the Universal Turing Machine (UTM) + Church-Turing Thesis.
   - We'll introduce the proof techniques of _diagonalization_ and _reduction_.
 *)


(** ** Machine vs. Language
 
   - Machine view:
      - deterministic finite automata (DFA)
      - non-deterministic finite automata (NFA)
      - epsilon non-deterministic finite automata (eNFA)
   - Language view:
      - regular expressions (REs)

   - The machine (or language) recognize subsets of words from an alphabet Σ.
   - That is, they compute functions f:  Σ^* -> {true, false}
 *)


(** * Why all these machines?
   
   |----> RE -----|   (structural induction on RE, epsilon useful for * and concat)
   |              |
   |              v
   |    NFA <-> eNFA  (embed/epsilon-closure)
   |     ^
   |     |  (embed/powerset)
   |     v
   |--->DFA

  - RE -> eNFA (structural induction on RE, epsilon useful for * and concat)
  - NFA <-> eNFA
    * NFA -> eNFA: embed
    * eNFA -> NFA: epsilon-closure
  - NFA <-> DFA
    * DFA -> NFA: embed
    * NFA -> DFA: powerset
  - DFA -> RE
    * Challenge: we didn't cover this in lecture.
    * What would you induct on?
 *)


(** *** Why finite automata?
   
   - Good first setting to look into computation where everything is finite.
   - As a reminder, both RE and DFA/NFA compute f: Σ^* -> {true, false}.
   - We identified the languages recognized by RE/DFA/NFA as the _regular languages_.
   - In our formalization we defined a regular language as those for which a
     DFA recognizes a word in that language.
   - Based on our characterization, a language is regular iff it is
     recognized by a RE, hence the name regular language.
   - As we saw with the *pumping lemma*, there are non-regular languages.
 
 *)

(** *** Where to next?

   - Today, we'll expand our notion of computation by introducing a new machine,
     the Turing Machine (TM).
   - We'll see that TMs compute functions [f: Σ^* -> Option {true, false}].
   - As with RE/DFA, we might wonder:
     * What languages are recognized by TMs? These will be called _decidable_.
     * Following up, are there things TMs cannot do? Yes, we will see that a
       TM cannot decide the _halting_ problem. We will need to introduce a
       _diagonlization technique_ to prove this. It is essentially the
       infinite version of the _pigeon-hole principle_.
     * How large is the set of problems that a TM cannot solve? It turns out
       there are an (uncountably) infinite number of them.
     * Can we weaken the notion of decidability? Yes, we can go with
       _semi-decidable_ languages. These are functions [f: Σ^* -> Option {true}].
       (For those of you interested in topology, Option {true} is
       the Sierpinski space.)
 *)


(** ** Turing Machines *)

(** *** What was missing from a DFA?
   
   - A DFA could only _read_ from state.
   - We now need to create a machine that can _write_ to state.
 *)


(** *** Scratchpads, aka, Tapes *)


(** **** Formalizing "writing" to a scratchpad

   - How would we formalize writing to a scratchpad for the purposes
     of proving stuff about it?
   - Strategy we will take: make it as simple and primitive as possible.
   - Why? Simplicity means less cases to prove.
   - The downside: to actually use the scratchpad will take a lot of work.
 *)


(** **** Tapes and Heads: a formal scratchpad
   
   - Imagine you have a list of cells called a *tape* and a pointer to the
     current location called a *head*
 *)
(*
        _________
  tape  |_|_|_|_|...
           ^
           |
          head
   
  The tape + head will be our scratchpad.
 *)

Record ScratchPad :=
  {
    sp_tape: list bool;
    sp_head: nat;
  }.

(** **** Formalization?

   - For the purposes of paper-pencil proofs, this is fine.
   - But for proving stuff formally, we have a lot of invariants to take care of.
 *)

(**
   - Can read, but we are not always guaranteed to get a symbol out.
 *)
Definition read (sp: ScratchPad): option bool :=
  List.nth_error (sp_tape sp) (sp_head sp).

(**
   - How will we implement write?
   - Suppose we want to write to a place that doesn't exist?
   - Then we need to extend the list.
*)


(** **** Tapes and Heads: take two

   - From Asperti & Ricciotti's "A formalization of multi-tape
     Turing machines" (2015) and the accompanying Matita code.
 *)


Section SCRATCHPAD.

  (* The alphabet type *)
  Variable Σ : Type.

  (** **** Tapes

     Tapes are either
     - empty (niltape),
     - non-empty with the head to the left of the content (leftof),
     - non-empty with the head to the right of the content (rightof),
     - or non-empty with the head on the content (midtape).

     - Blank symbols need to be part of the alphabet.
     - This enables a unique representation of the tape.
   *)

  Inductive tape : Type :=
  | niltape : tape
  | leftof : Σ -> list Σ -> tape
  | rightof : Σ -> list Σ -> tape
  | midtape : list Σ -> Σ -> list Σ -> tape.

  (** **** Reading

      - The current function returns the current symbol, if there is one.
      - If None is returned, this means that the head is on a part of the tape
        which has never been written before. Remember, blank symbols are part of
        the alphabet.
   *)
  Definition current (t : tape) : option Σ :=
    match t with
    | midtape _ a _ => Some a
    | _ => None
    end.


  (** **** Moving
      - Can move left, right, or do nothing.
   *)

  Inductive move : Type :=
  | Lmove : move
  | Rmove : move
  | Nmove : move.

  Definition mv (m : move) (t : tape) :=
    match m, t with
    | Lmove, rightof l ls => midtape ls l nil
    | Lmove, midtape nil m rs => leftof m rs
    | Lmove, midtape (l :: ls) m rs => midtape ls l (m :: rs)
    | Rmove, leftof r rs => midtape nil r rs
    | Rmove, midtape ls m nil => rightof m ls
    | Rmove, midtape ls m (r :: rs) => midtape (m :: ls) r rs
    | _, _ => t
    end.


  (** **** Writing
      - Optionally write s to the tape t.
      - We need an option because we might want to write nothing to the tape.
   *)
  
  Definition wr (s : option Σ) (t : tape) : tape :=
    match s, t with
    | None, t => t
    | Some a, niltape => midtape nil a nil
    | Some a, leftof r rs => midtape nil a (r :: rs)
    | Some a, midtape ls b rs => midtape ls a rs
    | Some a, rightof l ls => midtape (l :: ls) a nil
    end.


  (** **** Difference in formalization from pencil-paper 1:
     
     - Moving to the right of the rightof tape is identity.
     - Traditionally we would have an empty cell that would have a blank symbol written to it.
   *)
  
  Lemma right_right_identity:
    forall (x: Σ) (ls: list Σ),
      mv Rmove (rightof x ls) = rightof x ls.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.
  
  
  (** **** Difference in formalization from pencil-paper 2:
     
     - Moving to the left and then moving to the right is not the same syntactically.
     - But is semantically in the sense that we the same "contents" on the tape.
   *)
  
  Lemma left_then_right_not_same:
    forall (x: Σ) (ls: list Σ),
    exists t,      
      mv Rmove (mv Lmove t) <> t.
  Proof.
    intros.
    exists (leftof x ls).
    simpl.
    unfold not.
    intros.
    inversion H.
  Qed.


  (** **** Difference in formalization from pencil-paper 2:
     
     - Moving to the left and then moving to the right is not the same syntactically.
     - But is semantically in the sense that we the same "contents" on the tape.
   *)

  (** * Summary
      - We are still talking about scratchpads.
      - But constructing everything so that the induction works out formally
        requires us to be extremely careful with defining: empty cells and blank symbols.
   *)
  
End SCRATCHPAD.


Arguments niltape _, {_}.
Arguments leftof _ _ _, {_} _ _.
Arguments rightof _ _ _, {_} _ _.
Arguments midtape _ _ _ _, {_} _ _ _.
Arguments current {_} _.
Arguments wr {_} _ _.
Arguments mv {_} _.

  
(** *** Machine Execution *)


Section EXECUTION.

  (**
     - The alphabet is assumed to be finite 
   *)
  Variable Σ : finType.
  
  (**
     - The number of tapes.
     - Keep this thought for now: does it matter if n = 0, n = 1, or n > 1?
   *)
  Variable n : nat.


  (**
     - Vector is just an array that knows how many elements it has.
   *)
  Print Vector.t.
  
  (**
     - Definition of multi-tape Turing machines
     - Remember we are doing this for any n
   *)
  Record TM : Type :=
    {
      (* 
         - type of states of the TM: 
         - Note: it is finite!
       *)
      state : finType;
      
      (* transition function: *)
      trans : state * (Vector.t (option Σ) n) -> state * (Vector.t ((option Σ) * move) n);
      
      (* start state: *)
      start: state;
      
      (* set of final states (note we are going into bool): *)
      halt : state -> bool 
    }.

  (** *** Evaluation Relation

     - Uses the transition function until a halting state is reached.
   *)
  Inductive eval (M : TM) (q : state M) (t : Vector.t (tape Σ) n) : state M -> Vector.t (tape Σ) n -> Prop :=
  | eval_halt :
      halt M q = true ->
      eval M q t q t
  | eval_step q' a q'' t' :
      halt M q = false ->
      trans M (q, Vector.map current t) = (q', a) ->
      eval M q' (Vector.map2 (fun tp '(c,m) => mv m (wr c tp)) t a) q'' t' ->
      eval M q t q'' t'.
  
End EXECUTION.

Arguments state {_ _} m : rename.
Arguments trans {_ _} m _, {_ _ m} _ : rename.
Arguments start {_ _} m : rename.
Arguments halt {_ _} m _, {_ _ m} _ : rename.
Arguments eval {_ _} _ _ _ _ _.
Arguments Build_TM {_ _ _} _ _ _.


(** *** Challenge 

   - Programming TMs is a pain.
   - Here's a challenge: write a machine that does binary addition on 8 bit numbers
     where the the first 8 cells of the tape contains the first number and the second
     8 cells contains the second number.
   - Point: TMs give a good theoretical model for computation but we might want 
     higher-level languages to program them. The downside is that the computational
     complexity and cost might be abstracted away.
*)


(** ** Semantics of Turing Machines? *)

(** ** How do we define the semantics of a TM?
    
  - We saw with DFA/NFA/eNFA that we could define the language that a DFA/NFA/eNFA recognizes.
  - This was the defined to be the semantics of the machine.
  - In particular, the DFA definition gave us a "small-step semantics" for how the
    machine transitioned and recognized language gave us the meaning of the machine
    in terms of the function it computed.
  - We cannot define the function that TMs compute directly in Coq because TMs
    do not necessarily terminate.
  - We will get around this by defining relations on configurations and defining a
    "big-step" semantics using partial functions.
  - Thankfully this is already done for us.
 *)
Require Import Undecidability.TM.Util.TM_facts.


(** *** Configurations 

 - A _big-step_ or _large-step_ semantics of a TM will be given
    in terms of relations on configurations.
  - We will see that the _big-step_ semantics highlights that TMs define
    _partial computable functions_.
  - A _configuration_ stores the state of the TM and the contents of all the tapes.
  - This notion of configuration will also be useful later on when we talk
    about computation complexity (e.g., in Cook-Levin).
 *)

Print mconfig.
(**
<<
Record mconfig (sig state : finType) (n : nat) : Type := mk_mconfig
  { 
    cstate : eqType_X state;
    ctapes : tapes sig n 
  }
>>
*)


(** *** Initial Configurations 
*)

Print initc.
(**
<<
Definition initc: forall (sig : finType) (n : nat) (M : TM sig n),
                  tapes sig n -> mconfig sig (state M) n := 
  fun (sig : finType) (n : nat) (M : TM sig n) (tapes : tapes sig n) =>
    mk_mconfig (start M) tapes     
>> 
*)


(** *** Halting Configurations 
*)
Print haltConf.
(**
<<
Definition haltConf : forall (sig : finType) (n : nat) (M : TM sig n),
                      mconfig sig (state M) n -> bool := 
  fun (sig : finType) (n : nat) (M : TM sig n) (c : mconfig sig (state M) n) =>
    halt (cstate c)
>>
 *)

  
(** *** Stepping *)

(* One Step

  We need a helper function to go from taking a TM transition to the configuration.

     trans (st1, tp1) = (st2, tp2)
   --------------------------------- 
       (st1, tp1) --> (st2, tp2)
 *)


Print step.
(**
<<
Definition step : forall (sig : finType) (n : nat) (M : TM sig n),
                  mconfig sig (state M) n -> mconfig sig (state M) n := 
  fun (sig : finType) (n : nat) (M : TM sig n) (c : mconfig sig (state M) n) =>
    let (news, actions) := trans (cstate c, current_chars (ctapes c)) in
    mk_mconfig news (doAct_multi (ctapes c) actions).
>>
*)



(** *** Big-Step semantics: while True

   - Remember that Coq only allows terminating functions.
   - How do write while True?
   - We use a common trick: define a loop with a certain amount of "gas".
   - Intuitively, the "gas" counts the number of steps that we take.
 *)
(*

     loopM (st1, tp1) n = Some (st2, tp2)
   --------------------------------------- loopM
          (st1, tp1) -->* (st2, tp2)
 *)

Print loopM.
(**
<<
Definition loopM : forall (sig : finType) (n : nat) (M : TM sig n),
                   mconfig sig (state M) n -> nat -> option (mconfig sig (state M) n) :== 
  fun (sig : finType) (n : nat) (M : TM sig n) => loop (step (M:=M)) (haltConf (M:=M))
>>

<<
Definition loop : forall A : Type, (A -> A) -> (A -> bool) -> A -> nat -> option A = 
  fun (A : Type) (f : A -> A) (p : A -> bool) =>
    fix loop (a : A) (gas : nat) {struct gas} : option A :=
      if p a 
      then Some a
      else match gas with
           | 0 => None
           | S gas' => loop (f a) gas'
           end.
>>    
 *)
  

(** *** Eval <-> Loop, or small-step semantics and big-step semantics are logically equivalent

   - We need to tie together the eval relation with the loop function.
   - If the computation halts, then there exists some amount of gas for which
     we could have run the computation with. 
 *)

Lemma TM_eval_iff (Σ : finType) n (M : TM Σ n) q t q' t' :
  TM.eval M q t q' t' <-> exists n,
      loopM (M := M) (mk_mconfig q t) n = Some (mk_mconfig q' t').
Proof.
  split.  
  - (* (=>) *)
    (* Perform induction on the eval relation *)
    induction 1 as [ | q t q' a q'' t' H0 H1 H2 [m IH]].
    + exists 0. cbn. unfold haltConf. cbn. now rewrite H.
    + exists (S m). cbn. unfold haltConf. cbn. rewrite H0.
      unfold step. cbn. unfold current_chars.
      rewrite H1. erewrite Vector_map2_ext.
      * now rewrite IH.
      * intros [] [[] []]; reflexivity.
  - (* (<=) *)
    intros [k H].

    (* Induction on natural numbers *)
    induction k in q, t, H, q', t' |- *; cbn in H; unfold haltConf in H; cbn in H.
    + destruct halt eqn:E; inv H. now econstructor.
    + destruct halt eqn:E; inv H.
      * now econstructor.
      * unfold step in H1. cbn in H1.
        destruct trans eqn:E2.
        econstructor; [ eassumption .. | ].
        eapply IHk. erewrite Vector_map2_ext.
        -- now rewrite H1.
        -- intros [] [[] []]; reflexivity.
Qed.


(** ** Is this Notion of Computation Robust? *)


(** *** Robust to alphabet?

   - Does changing the alphabet change what we can compute with a TM?
   - No: intuitively we can always encode any finite alphabet in binary.
 *)


(** *** Robust with respect to number of tapes?


   - A 0 tape TM is a trivial TM so let's ignore that for now.
   - What about changing the number of tapes from 1 to 2? No.
   - What about changing the number of tapes from 2 to n for any n > 2? No.
   - How would we prove this?
      - Encode 2 tapes in 1 tape? Even cells contain contents from tape 1 and odd
        cells contain contents from tape 2.
      - Encode n tapes in 1 tape? cell (mod n) on tape 1 contains contents from tape n.
 *)


(** *** How do we encode DFA?

   - Can we simulate a DFA?: Yes: 0 tape TM.
 *)


(** *** How many TMs do we need?

   - Can a TM simulate a TM? Yes.
   - So we only need to build a *universal Turing machine* (UTM).
 *)



(** ** Universal Turing Machines (UTM) *)


(** *** UTM: The one TM to rule them all
    
  - The magical thing about TMs is that we only need to build one TM.
  - How do we do this?
  - The entire description of a TM is finite!
  - So
      1. Encode the description of a TM M, written "M", as a string
      2. The universal Turing machine's (UTMs) transition function interprets these strings.
 *)


(** *** Encoding a TM as a string *)
Require Import Undecidability.TM.Univ.LowLevel.
Print Undecidability.TM.Univ.LowLevel.


(** *** TM Transition

  - Encode the graph of the transition function.
*)

Print graph_of_fun.
(**
<<
Definition graph_of_fun : forall (A : finType) (B : Type), (A -> B) -> list (A * B) = 
   fun (A : finType) (B : Type) (f : A -> B) => map (fun x : A => (x, f x)) enum     
>>
 *)

Print graph_function.
(**
<<
Definition graph_function : forall (sigM : finType) (M : TM sigM 1),
                            option sigM * state M -> option sigM * move * state M
  = 
  fun (sigM : finType) (M : TM sigM 1) '(s, q) =>
    let (q', acts) := trans (q, [ | s | ]) in
    let (w, m) := acts[@Fin0] in (w, m, q')
>>
*)


(** *** Correctness?

    encode(M(x)) <-> UTM("M" ++ encode(x))

 *)
Require Import Undecidability.TM.Univ.Univ.

Check Univ_SpecT.
(**
<<
Lemma Univ_SpecT (M : TM sigM 1) (tp : tape sigM) (q : state M) (k' : nat) :
    TripleT
      (fun tin => exists (q' : state M) (tp' : tape sigM),
           loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]) /\
           ≃≃([],[|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]) tin
           )
      (Univ_steps q tp k') Univ
      (fun _ tout =>
         exists (q' : state M) (tp' : tape sigM),
           loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]) /\
           ≃≃([],[|ContainsWorkingTape tp'; ContainsTrans M; ContainsState q'; Void; Void; Void|]) tout).
>>
 *)


(** ** Halting Problem *)


(** *** Anything is Possible!?

   - At this point, it might appear that TMs can do everything!
   - However, this is not the case.
   - We will show that a TM cannot solve the **halting problem**.
 *)


(** *** Halting problem

  - I can tell if I eventually reach a halting state.
  - In other words, I do not go into an infinite loop.
  - Here is the definition for a TM.
 *)

Definition HaltsTM {Σ: finType} {n: nat} (M : TM Σ n) (t : Vector.t (tape Σ) n) :=
  exists q' t', eval M (start M) t q' t'.
Arguments HaltsTM _ _ _ _, {_ _} _ _.

(**
   - Where did the halting go?
   - Remember, the eval relation had the set of halting states.
   - So if I could build that proof tree, then the TM must have halted.
 *)

Definition HaltTM (n : nat) : {Σ : finType & TM Σ n & Vector.t (tape Σ) n} -> Prop :=
  fun '(existT2 _ _ Σ M t) => HaltsTM M t.

(**
   - How might we prove that a TM cannot solve this problem?
   - Enter **diagonalization**.
 *)




(** *** Diagonalization Technique *)

(**
   - The _diagonalization technique_ is essentially a **counting** argument
     that needs to work on infinite sets.
   - As you might already know or suspect, one can't really count with an
     infinite number of things.
   - So the first thing we need to do is learn how to count with an infinite
     number of things.
 *)



(** *** Bijections and Infinite Sets *)

(**
   - Let's start with the example of natural numbers.
   - "Clearly" every number is even or odd.
   - But are there wice as many even numbers as natural numbers?
 *)

Definition Even := {m | exists k, m = 2 * k}.

(**
   - We can map each number to an even number by doubling it.
 *)

Definition double (n: nat) : Even.
  exists (2 * n).
  exists n.
  reflexivity.
Defined.

(**
   - We can also take each even number and get a natural number from it.
 *)

Definition undouble (ev: Even): nat :=
  match ev with
  | exist _ m _ => m / 2
  end.

(**
   - These operations are inverses of each other.
 *)
Theorem double_undouble :
  forall (n: nat), undouble (double n) = n.
Proof.
  intros.
  unfold double.
  unfold undouble.
  rewrite Nat.mul_comm.
  destruct n.
  + simpl.
    reflexivity.
  + rewrite Nat.div_mul; auto.
Qed.

Theorem undouble_double :
  forall (ev: Even),
    double (undouble ev) = ev.
Proof.
  intros.
  Opaque Nat.div.
  destruct ev.
  destruct e.
  rewrite e.
  simpl.
  assert ((x0 + (x0 + 0))/ 2 = x0). {
    rewrite Nat.add_0_r.
    assert (x0 + x0 = x0 * 2). lia.
    rewrite H.
    rewrite Nat.div_mul; auto.
  }
  rewrite H.
  unfold double.
  reflexivity.
Qed.


(**
   - We have done something called defining a _bijection_.
   - A *bijection* is a 4-tuple (to, from, to_from, from_to) where
     * to: A -> B
     * from: B -> A
     * to_from and from_to are proofs that we are mutually inverse.
 *)

Record bijection (A B: Type) :=
  {
    to: A -> B;
    from: B -> A;
    to_from: forall b, to (from b) = b;
    from_to: forall a, from (to a) = a
  }.


(**
   - Here is the bijection for Even numbers and natural numbers.
   - Thus we will use the idea that if we have a bijection between two sets, then
     they have the same cardinality.
   - This is a generalization of counting for infinite sets.
   - So the question "are there twice as many natural numbers as even numbers"?
     isn't well formed.
   - But it does make sense to asks "can the evens be put in bijection with the naturals"?
     The answer is: yes.
 *)

Definition even_nat_bijection :=
  {|
    to := double;
    from := undouble;
    to_from := undouble_double;
    from_to := double_undouble
  |}.

            

(** ** Diagonalization via Cantor's Theorem on Naturals *)


(**
   - If a set can be put in bijection with the natural numbers, we say that it is *countable*.
   - Claim:
     The set of functions nat -> nat is not countable.
 *)


(** ** Proof

  - Suppose for the sake of contradiction that is is countable.
  - Thus we can put the set of functions nat -> nat in bijection with the natural numbers.
  - Let us list the graph of the function row-by-row.
  - For this piecture, we will write the graph of the function as a sequence.
*)
(*
enumeration of sequences       element of sequence -->
|
v
     0   1   2   3  ...

  0 0,0 0,1 0,2 0,3

  1 1,0 1,1 1,2 1,3 

  2 2,1 2,2 2,2 2,3

  3 3,1 3,2 3,2 3,3 

  ...
*)
(**
  - Now let's change the picture by modifying the diagonal so that
    ?n,n is dfferent from i,n for every i and n, hence the word *diagonalization*
 *)
(*
enumeration of sequences       element of sequence -->
|
v
     0   1   2   3  ...

  0 ?,0 0,1 0,2 0,3

  1 1,0 ?,1 1,2 1,3 

  2 2,1 2,2 ?,2 2,3

  3 3,1 3,2 3,2 ?,3 

  ...
*)
(**
  - What does this accomplish?
  - We have found a new function nat -> nat (technically the graph).
  - Which contradicts the assumption that we have a bijection (we missed exactly 1 sequence).
 *)


(**
   - Let's do this in Coq!
   - Courtesy: https://github.com/bmsherman/finite/blob/master/Iso.v
 *)

Theorem cantor :
  bijection nat (nat -> nat) ->
  False.
Proof.
  destruct 1 as [seq index ? ?].
  
  (* define a function which differs from the nth sequence at the nth index *)
  pose (f := fun n => S (seq n n)).

  (* prove f differs from every sequence *)
  assert (forall n, f <> seq n). {
    unfold not; intros.
    assert (f n = seq n n) by congruence.
    subst f; cbn in H0.
    eapply n_Sn; eauto.
  }
  
  rewrite <- (to_from0 f) in H.
  apply (H (index f)).
  reflexivity.
Qed.



(** *** Aside: Reals and uncountability *)

(** *** Reals

  - Suppose for the sake of contradiction that the reals are countable.
  - Every real number has a binary expansion (module the dyadic rationals).
*)
(*
enumeration of reals       binary expansion -->
|
v
     0   1   2   3  ...

  0 ?,0 0,1 0,2 0,3

  1 1,0 ?,1 1,2 1,3 

  2 2,1 2,2 ?,2 2,3

  3 3,1 3,2 3,2 ?,3 

  ...
*)
(**
  - Create a binary expansion where we flip the bits on the diagonal.
  - This is a real number that is not in the original sequence.
  - We have just "proven" that real numbers are *uncountable*! (Obviously missing
    a lot of details but this illustrate the main idea of diagonalization.)
  - In other words, there are multiple infinities!
 *)


(** ** Decidability *)

Require Import Undecidability.Synthetic.Definitions.
Print Definitions.

Module MY_DEC.

  (* (reflects b P) means that
     provability of the proposition P coincides with b being true *)
  Definition reflects (b : bool) (P : Prop) := P <-> b = true.

  (* (decider f P) means that
   the function f from the domain X of the predicate P to Booleans pointwise reflects P *)
  Definition decider {X} (f : X -> bool) (P : X -> Prop) : Prop :=
    forall x, reflects (f x) (P x).
  (* (decidable P) means that
   there exists a (total, computable, Boolean) decider f of P *)
  Definition decidable {X} (P : X -> Prop) : Prop :=
    exists f : X -> bool, decider f P.

End MY_DEC.


(** *** Is Every Language Decidable?

   - Suppose for the sake of contradiction that every language is decidable.
   - We can enumerate the graph of every TM as follows.
*)
(*
enumeration of TMs       all inputs
|
v
     x1  x2  x3  x4  ...

 M0 ?,0 0,1 0,2 0,3

 M1 1,0 ?,1 1,2 1,3 

 M2 2,1 2,2 ?,2 2,3

 M3 3,1 3,2 3,2 ?,3 

  ...
 *)

(*
  - Flip the bits on the diagonal to construct the complement of the language on the
    diagonal.
  - No TM can recognize this language!
  - Why? It differs from every TM graph in at least one location.
  - And we claimed that we listed them all, contradiction.
  - This shows us that not every language is decidable.
  - Are there interesting problems that are undecidable? Yes, unfortunately.
 *)


(** ** Halting is Undecidable *)

(** ** Decidable

  - A (computable) function [f: X -> option {true, false}] is **decidable** if
    [f(x) = Some true] or [f(x) = Some false] for every input x.
  - We use [None] to model non-terminiation.
  - So this definition also requires f to terminate.
  - By [eval <-> loopM], we have that each TM maps to some partial f.
*)


(** *** Halting is Undecidable

  - Suppose for the sake of contradiction that halt is decidable.
  - That is

    halt(M, x) = true if M halts on x
               = false if M does not halt on x   

  - Recall that every TM has a code-word.
  - Define a function flip s.t.

    flip("M") = negate halt(M, "M")

  - By assumption, halt is a function that decides if M halts on input "M"
    so that flip also terminates.
  - Now consider

    flip("flip") = negate halt(flip, "flip")
    
  - We have that 

    flip("flip") = false if halt(flip, "flip") = true which implies that flip("flip") halts with true. 

  - Moreoever we have that

    flip("flip") = true if halt(flip, "flip") = false which implies that flip("flip") halts with false, a contradiction
    
  - So halt cannot exist.
                 
*)

(** *** Where is the diagonalization?

  - List out TMs on one axis and code-word's on the other axis.
*)
(*
TM       "TM" -->
|
v
    "0" "1" "2" "3"  ...

  0 ?,0 0,1 0,2 0,3

  1 1,0 ?,1 1,2 1,3 

  2 2,1 2,2 ?,2 2,3

  3 3,1 3,2 3,2 ?,3 

  ...
*)

(**
  - Each entry lists out whether machine n halt's on the corresponding input.
 *)

(*
TM       "TM" -->
|
v
    "0" "1" "2" "3"  ...

  0 ?,0 0,1 0,2 0,3

  1 1,0 ?,1 1,2 1,3 

  2 2,1 2,2 ?,2 2,3

  3 3,1 3,2 3,2 ?,3 

  ...
*)

(**
  - If Machine n halts on input "n" with true, then switch it to false.
  - And if Machine n halts on input "n" with false, then switch it to true.
  - So the diagonal is exactly the graph of flip!
  - Which is a TM that halt cannot decide.
 *)


(**
   - How did we formalize this in Coq?
   - We defined it to be undecidable!
 *)
Require Import Undecidability.Synthetic.Undecidability.
Print undecidable.


(**
   - We almost have all the pieces to complete the proof.
   - How?
   - Find a bijection between TMs and natural numbers.
   - Find a bijection bewteen encodings of TMs and natural numbers.
   - Use Cantor's diagonalization on natural numbers to show that the
     graph of the flip TM function does exist.
   - So there is a TM that halt cannot decide.
 *)


(** ** More definitions *)


(** *** Recursive enumerability *)

Module MY_ENUM.

  (* (enumerator f P) means that
   the function f is a surjection from the natural numbers to the positive instances of P *)
  Definition enumerator {X} (f : nat -> option X) (P : X -> Prop) : Prop :=
    forall x, P x <-> exists n, f n = Some x.
  (* (enumerable P) means that
   there exists a (onto the positive instances of P) enumerator f of P *)
  Definition enumerable {X} (P : X -> Prop) : Prop :=
    exists f : nat -> option X, enumerator f P.

End MY_ENUM.


(** *** Semi-Decidability *)


(**
   - What if we wanted one-sided decidability?
   - This would be known as **semi-decidability**.
 *)

Module MY_SEMI_DEC.
  (* (semi_decider f P) means that
    the function f from the domain X of the predicate P to Boolean sequences pointwise reflects P
   with respect to Boolean sequence satisfiability *)
  Definition semi_decider {X} (f : X -> nat -> bool) (P : X -> Prop) : Prop :=
    forall x, P x <-> exists n, f x n = true.

  (* (semi_decidable P) means that
     there exists a (computable, to Boolean sequences) semi-decider f of P *)
  Definition semi_decidable {X} (P : X -> Prop) : Prop :=
    exists f : X -> nat -> bool, semi_decider f P.

End MY_SEMI_DEC.


Locate decidable.

(**
   - Obviously if p is decidable, it should be semi-decidable.
 *)

Lemma decidable_semi_decidable {X} {p : X -> Prop} :
  decidable p -> semi_decidable p.
Proof.
  intros [f H].
  exists (fun x n => f x).
  intros x.
  unfold decider, reflects in H. (* use the decider! *)
  rewrite H.
  firstorder.
  econstructor.
Qed.


(**
   - And if p is decidable, so it it's complement.
 *)

Require Import Undecidability.Synthetic.DecidabilityFacts.
Print complement.
(**
Definition complement : forall X : Type, (X -> Prop) -> X -> Prop := 
  fun (X : Type) (P : X -> Prop) (x : X) => ~ P x   
 *)

Lemma decidable_complement_semi_decidable {X} {p : X -> Prop} :
  decidable p -> semi_decidable (complement p).
Proof.
  intros H.
  now eapply decidable_semi_decidable, dec_compl. (* run the decider on the complement *)
Qed.


(**
   - And of course, if p is both semi_decidable and it's complement is semi-decidable
     then it is is decidable. This is hard to prove? given the current formalization.
 *)


(** ** Proof Technique: Reduction *)


(**
   - How will we show that other problems are undecidable?
   - The primary technique we will use is **reduction**.
   - This is an important technique, not only for undecidability, but also for
     complexity.
 *)


(**
   - What is the idea of reducability?
   - Suppose p is hard problem.
   - We will solve p by using q.
   - Therefore q is at least as hard as p.
   - And p reduces to q.
 *)

Module MY_REDUC.

  (* (reduction f P Q) means that f many-one reduces P to Q, that is
   for the function f from the domain X of P to the domain Y of Q
   P pointwise coincides with Q ∘ f *)  
  Definition reduction {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) :=
    forall x, P x <-> Q (f x).
  (* (reduces P Q) means that
   there exists a (total, computable, many-one) reduction f from P to Q *)
  Definition reduces {X Y} (P : X -> Prop) (Q : Y -> Prop) :=
    exists f : X -> Y, reduction f P Q.
  Notation "P ⪯ Q" := (reduces P Q) (at level 70).

End MY_REDUC.


(**
  - Suppose p is undecidable.
  - We will solve p by using q (i.e., solving p reduces to solving q).
  - Therefore q is also undecidable.
*)

Lemma undecidability_from_reducibility {X} {p : X -> Prop} {Y} {q : Y -> Prop} :
  undecidable p ->
  p ⪯ q ->
  undecidable q.
Proof.
  unfold undecidable, decidable, decider, reduces, reduction, reflects.
  intros H [f Hf] [d Hd].
  eapply H.
  exists (fun x => d (f x)).
  intros x.
  rewrite Hf.
  eapply Hd.
Qed.


(**
   - Many problems can be shown to be undecidable this way.
 *)


(** ** Summary 

  - We did a lot today.
   - We learned about TMs and how to formalize partial functions in Coq.
   - Namely we saw that we could give small-step semantics to TMs as
     well as large-step partial functin semantics to TMs.
   - We finally learned about decidability and its connection with [boolean] vs. [Prop].
   - We learned two important proof techniques: diagonalization and reducibility.
   - The former is a "counting" argument.
   - The latter abstracts away the low-level "counting" argument so that
     we don't need to think about counting arguments again.
 *)
