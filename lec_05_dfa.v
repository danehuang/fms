(** * Deterministic Finite Automata (DFA) *)


(** ** References

   - https://github.com/coq-community/reglang

     Authors: Christian Doczkal and Jan-Oliver Kaiser
     Distributed under the terms of CeCILL-B.

 *)


(** ** Recap

    - Last time, we ended our brief introduction to Coq.
    - In particular, we briefly saw the idea of a small-step semantics,
      which gave us a way to model the behavior of a "machine".
    - Today, we'll look at a very simple machine: a deterministic
      finite automata (DFA).
    - DFA's can't express all computations, which will pave the way
      for Turing machines (TMs).
   
 *)


(** ** Goals for next two lectures 

   - Today:
     - Introduce deterministic finite automata (DFA) as an abstract machine.
     - Define the concept of a regular language using DFAs.
     - Show that non-regular languages exists via the Pumping Lemma.
   
   - Next time:
     - Introduce regular expressions as the "language" corresponding to a DFA.
     - Show the equivalence of regular expressions (REs) and DFAs via
       non-deterministic finite automata (NDFA).

   - Meta-goal: connect paper-pencil intution to the formalism.
 *)


(** ** Ssreflect

   - We will be using the ssreflect package (small scale reflection).
   - This is a Coq library that gives extra notation + tactics for doing
     mathematics in Coq.
   - ssreflect is used in many serious formal developments (e.g., Feit-Thompson).
 *)
From mathcomp Require Import all_ssreflect.


(**
   - Please see: https://ilyasergey.net/util/ssreflect-manual.pdf
     which contains a good explanation of ssreflect.
   - The long and short:
      - [=>] moves stuff from goal into context
      - [:] moves stuff from context back into goal
 *)

Lemma subnK:
  forall (m n: nat),
    n <= m ->
    m - n + n = m.
Proof.
  move => m n.        (* intros m n. *)

  move: m.            (* generalize m. *)
  move: n.            (* generalize n. *)
  move => m n le_n_m.
  move: le_n_m.

  (* move: n {2}n (refl_equal n). *)
  move: (refl_equal n).
  move: {2}n.
  move: n.
  move => n n0 eq_n_n0 le_n_m.
  
  (* elim: n m le_n_m => [|n IHn] m => [_ | lt_n_m]. *)
  elim: n m eq_n_n0 le_n_m.   (* "induction n" *)
  - move => m _.
    admit.
  - move => n IHn m lt_n_m.
Abort.




(** ** Reglang formalization

   - We are using the Coq formalization reglang:
     https://github.com/coq-community/reglang
     in this lecture.
   - Much of the material in this lecture comes from this formalization.
   - First we need to add the following path.
     You will need to change this for yourself.
 *)

(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
Require Import lib_reglang.

(**
   - Not that important ...
 *)
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.


(** ** Definition of DFA 

   - A DFA is a 5-Tuple (Q, \Sigma, \delta, s f) where
     - Q is a finite set of DFA states
     - \Sigma is an alphabet
     - \delta: Q x \Sigma -> Q is a transition function
     - s \in Q is a starting state
     - F \in {set Q} is a finite set of final states.
   - We'll start with a few of pictures of DFAs.

*)

(** ** Pictures of DFAs












 *)


(** ** Sections

   - A section is a Coq feature that lets us define universally quantified
     variables that are available throughout the section.
 *)
Section FA.

(** 
    - Our first universally quanitifed variable throughout this section
      is [char] which stands for character. A character is a [finType].
    - [finType] stands for finite type:
      https://math-comp.github.io/htmldoc/mathcomp.ssreflect.fintype.html 
 *)
Locate finType.  
Variable char : finType.

(**
   - [word] is a list of characters.
   - [word]'s are finite.
 *)
Print word.
Print seq.
Local Notation word := (word char).

(* https://math-comp.github.io/htmldoc/mathcomp.ssreflect.finset.html *)
Check {set bool}.


(** ** Records
   
   - Records are named tuples.
   - We can encode the structure of a DFA as the record below.
 *)
Record dfa : Type := {
    (* Note that alphabet char is implicit in this section. *)
    dfa_state :> finType;                       (* dfa states Q, dfa coerced to dfa_state *)
    dfa_s : dfa_state;                          (* start state s *)
    dfa_fin : {set dfa_state};                  (* final states F *)
    (* transition function \delta: Q x \Sigma -> Q 

       This is a small-step semantics!
     *)
    dfa_trans : dfa_state -> char -> dfa_state
}.


(**
   - A DFA is a simple machine.
   - It reads in a word and either _accepts_ the string if it transitions to 
     a final state or _rejects_ the string if it does not.
   - The set of words that a DFA accepts is called the _language_ of the DFA.
   - We'll define all of this now.
 *)

(** ** DFA Acceptance *)

Section DFA_Acceptance.
  (* Recall this will be coerced to (dfa_state A) when appropriate *)
  Variable A : dfa.

  Implicit Types (p q: dfa_state A) (x y: word).

  (**
     - Transitive closure with the transition function.
     - Question: how does this compare or contrast with the inductive proposition approach?
   *)
  Fixpoint delta (p: dfa_state A) (x: word): dfa_state A := 
    if x is a :: x' then delta (dfa_trans p a) x' else p.

  
  (**
     - Properties of the transitive closure.
   *)
  Lemma delta_cons (p: dfa_state A) (a: char) (x: word):
    delta (dfa_trans p a) x = delta p (a :: x). 
  Proof.    
    by [].          (* ssreflect tactic [done] *)
  Qed.


  (** Aside on ssreflect
     - //         means  try by [].
     - /=         means  simpl
     - //=        means  simpl; try by [].
   *)

  Lemma delta_cat (p: dfa_state A) (x y: word):
    delta p (x ++ y) = delta (delta p x) y.
  Proof.
    (* generalize x. generalize p. induction x. *)
    elim: x p.
    - by [].
    - move => a x IH p /=.
      by rewrite IH.        (* ssreflect for "rewrite IH. by []" *)
  Qed.

  Lemma delta_cat' (p: dfa_state A) (x y: word):
    delta p (x ++ y) = delta (delta p x) y.
  Proof.
    (* compactifying the previous proof *)
    elim: x p => // a x IH p /=.
    by rewrite IH.
  Qed.


  (** *** DFA Acceptance *)

  (** 
      - We are now ready to define what it means for a DFA to accept a word.
      - The idea:
         - run the DFA to consume the entire word
         - check if the final state of the DFA is an accepting state.
   *)
  
  Definition dfa_accept (p: dfa_state A) (x: word): bool :=
    (* 
       - dfa_fin A: {set (dfa_state A)}
       - \in is "set" membership
       - recall that dfa_fin is a finite set
    *)
    delta p x \in dfa_fin A.
  
  (**
     accept_nil: If there's nothing left to consume, then we better be at a final state.
   *)
  Lemma accept_nil (p: dfa_state A):
    dfa_accept p [::] = (p \in dfa_fin A). 
  Proof.
    by [].
  Qed.


  (**
     accept_cons: If we consume one character, then we should also
                  accept the DFA after we take that step.
   *)
  Lemma accept_cons (x: dfa_state A) (a: char) (w: word): 
    dfa_accept x (a :: w) = dfa_accept (dfa_trans x a) w.
  Proof.
    by [].
  Qed.

  
  (**
     Question: can you write down the inference rules for DFA acceptance
     as an inductive proposition?
   *)

  
  (** *** Excercise 1:
     
      - Design a DFA with char {0, 1} that only accepts the word "101".
   *)


  (** *** Exercise 2:
     
     - Design a DFA with char {a, b, c} that accepts any number of a's 
       followed by "bc".

   *)  

  (** *** DFA Language *)
  
  Definition delta_s (w: word): dfa_state A :=
    delta (dfa_s A) w.

  (**
     - The language of a DFA is the language of the starting state.
     - [simpl_pred] is a function from word's to bool, i.e.,
       "decidable" predicate.
     - [pred x | dfa_accept (dfa_s A) x] gives the boolean predicate
          [fun x => dfa_accept (dfa_s A) x]
       for a finite set.
   *)

  Locate pred.
  Definition dfa_lang: simpl_pred word :=
    [pred x | dfa_accept (dfa_s A) x].

  Lemma delta_lang (x: word):
    (delta_s x \in dfa_fin A) = (x \in dfa_lang).
  Proof.
    by [].
  Qed.

  Definition accE := (accept_nil, accept_cons).

  Check accE.

End DFA_Acceptance.


(** ** Regular Languages 

   - A regular language is defined to be the set of Languages that
     are accepted by DFA's.
   - We will see next time that this is equivalent to *regular expressions*.

 *)
Definition regular (L : lang char): Type :=
  { A : dfa | forall x, L x <-> x \in dfa_lang A }.


(**
   - We can convert the [Type] to [Prop].
 *)
Definition regular_prop (L: lang char): Prop :=
  inhabited (regular L).


Locate "=p".

(**
   - Regular languages satisfy extensionality.
 *)
Lemma regular_ext (L1 L2: lang char):
  regular L2 ->
  L1 =p L2 ->
  regular L1.
Proof.
  elim.
  move => A HA B.     (* intros A HA B *)
  rewrite /regular.   (* unfold regular *)
  exists A.
  move => w.          (* intros w *)
  by rewrite B.
Qed.


(** *** Empty automaton 

   - An empty dfa has 1 state tt and no accepting states.
**)

Print tt.
Definition dfa_void :=
  {|
    dfa_s := tt;
    dfa_trans q a := tt;
    dfa_fin := set0
  |}.

Lemma dfa_void_correct (x: word) :
  x \in dfa_lang dfa_void = false.
Proof.
  rewrite -delta_lang /=.  (* rewrite <- delta_lang *)
  Check inE.
  rewrite inE.
  by [].
Qed.


(** *** Empty language is regular *)
Lemma regular0:
  regular (fun _ : word => False).
Proof.
  exists (dfa_void) => x.
  by rewrite dfa_void_correct.
Qed.

(** *** Operations on DFAs 

   - Build complement automata.
   - Build boolean combinations of DFA (&& and ||).
 *)

(** *** Exercises

   - Design a DFA that accepts an even number of 1's.
   - Design a DFA that accepts an odd number of 0's.
 *)


Section DFAOps.

  Variable op : bool -> bool -> bool.
  Variable A1 A2 : dfa.

  (** *** Complement automaton 

     - How will we build a complement automaton?
     - That is, we need to build an automaton that accepts the complement of the
       words accepted by the original language.  
   *)
  Locate "~:".
  
  Definition dfa_compl: dfa :=
    {|
      dfa_s := dfa_s A1;
      dfa_fin := ~: (dfa_fin A1);
      dfa_trans := (@dfa_trans A1)
    |}.


  (** *** Complement automaton is correct *)  
  Lemma dfa_compl_correct (w: word):
    w \in dfa_lang dfa_compl = (w \notin dfa_lang A1).
  Proof.
    rewrite /dfa_lang.    (* unfold dfa_lang *)    
    rewrite !inE.         (* repeat (rewrite inE) *)
    rewrite /dfa_compl.   (* unfold dfa_compl *)
    rewrite /=.           (* simpl *)
    rewrite /dfa_accept.  (* unfold dfa_accept *)
    rewrite !inE.         (* repeat (rewrite inE) *)
    by [].                (* trivial *)
  Qed.


  (** *** BinOp Automaton *)

  (**
     - Determine the final states of the automaton by op (dfa_fin A1) (dfa_fin A2).
   *)
  Definition dfa_op: dfa :=
    {|
      dfa_s := (dfa_s A1, dfa_s A2);
      dfa_fin := [set q | op (q.1 \in dfa_fin A1) (q.2 \in dfa_fin A2)];
      dfa_trans := fun (x: dfa_state A1 * dfa_state A2) (a: char) => (dfa_trans x.1 a, dfa_trans x.2 a)
    |}.


  (** *** BinOp Automaton correct *)  
  
  Lemma dfa_op_correct (w: word):
    w \in dfa_lang dfa_op = op (w \in dfa_lang A1) (w \in dfa_lang A2).
  Proof.
    rewrite !inE.           (* rewrite inE as many times as we can *)
    rewrite {2}/dfa_op /=.  (* unfold 2nd occurrence of dfa_op and simplify *)

    (* elim: w (dfa_s A1) (dfa_s A2) => [| a w IHw] x y; by rewrite !accE ?inE /=. *)
    elim: w (dfa_s A1) (dfa_s A2).

    Locate accE.
    Check accE.
    
    - move => x y /=.
      rewrite !accE inE.
      by [].
    - move => a w IHw x y.
      rewrite !accE /=.
      by [].
  Qed.

End DFAOps.


(** *** Intersection of regular languages is regular *)
Lemma regular_inter (L1 L2 : lang char):
  regular L1 ->
  regular L2 ->
  regular (fun x => L1 x /\ L2 x).
Proof.
  move => [A1 acc_L1].
  move => [A2 acc_L2].
  rewrite /regular.

  (* Interesting step: what are we doing here? *)

  exists (dfa_op andb A1 A2) => x.

  (* Using reflection here! *)
  Locate rwP.
  Check rwP.
  Locate andP.
  Check rwP.

  by rewrite dfa_op_correct acc_L1 acc_L2 (rwP andP).
Qed.


(** *** Union of regular languages is regular *)
Lemma regularU (L1 L2 : lang char) :
  regular L1 ->
  regular L2 ->
  regular (fun x => L1 x \/ L2 x).
Proof.
  move => [A1 acc_L1].
  move => [A2 acc_L2].
  rewrite /regular.

  (* Intereseting step here: witness union with orb *)
  exists (dfa_op orb A1 A2) => x.

  by rewrite dfa_op_correct acc_L1 acc_L2 (rwP orP). 
Qed.


 (** 
   - It may be unsatisfactory to see these proofs go through especially if we want a
     concrete DFA machine that witnesses that thes properties hold.
   - Let's spend some time building such DFAs.
   - Hint: the proofs should give you a hint as to what to do!
   - Exercises
     - Design a DFA that accepts an even number of 1's and an odd number of 0's.
     - Design a DFA that accepts an even number of 1's or an odd number of 0's.
     - Design a DFA that accepts an even number of 1's or an odd number of 0's, but not both.
 *)


(** *** Countable union of regular languages is regular.
   
  - [exists2 x, P x & Q x] says that there is an x that satisfies P and Q.
*)
Lemma regular_bigU (T: eqType) (L: T -> lang char) (s : seq T): 
  (forall (a: T), a \in s -> regular (L a)) ->
  regular (fun (x: word) => exists2 a, a \in s & L a x). 
Proof.
  elim: s. (* induction s *)
  - move => _.

    Locate regular_ext.
    apply: regular_ext regular0 _.    (* refine (regular_ext regular0 _). *)

    split => //=.
    move => IHcontra.
    elim: IHcontra.
    by [].
  - move => a s IH.

    Locate forall_consT.
    Check forall_consT.
    move => /forall_consT [H1 H2].

    pose L' := (fun x => L a x \/ (fun x : word => exists2 a : T, a \in s & L a x) x). 
    apply: (regular_ext (L2 := L')); first by apply: regularU => //; exact: IH. 
    move => x.
    rewrite /L'.

    Locate exists_cons.
    Check exists_cons.
    
    exact: exists_cons.
Qed.


End FA.


(** ** Non-regular Langauges? 

   - You might guess that there are non-regular languages.
   - In other words, there are languages that a DFA cannot recognize.
 *)

(** *** Exercises

   - Attempt to construct a DFA that matches at least 3 1's or informally
     argue why it is not possible (see board).
   - Attempt to construct a DFA that matches n 0's followed by n 1's or
     argue informally why it is not possible for any n (impossible).
   - Attempt to construct a DFA that matches n 0's followed 1 followed by
     n 0's or argue informally why it is not possible (impossible).
   - Attempt to construct a DFA that matches the same number of 01's
     followed by 10's or argue informally why it is not possible.
 *)


Section NonRegular.
  Variables (char: finType) .

  Implicit Types (L: lang char).

  (** *** Canonical counter-example

     - A sequence of n a's followed by n b's.
   *)

  Hypothesis (a b : char) (Hab : a != b).
  Local Set Default Proof Using "Hab".
  
  Definition Lab (w: seq char) :=
    exists n, w = nseq n a ++ nseq n b.

  (** *** Pigeon-Hole Principal (PHP):
     
     If I have n bins and k > n items, then 1 bin contains at least two items.  

     - Deceptively simple.
     - Counting arguments are used a lot in computability proofs.
   *)
  
  (** *** Claim: The language a^n b^n is not regular. *)
  (*
     Proof.

     Suppose for the sake of contradiction that the language a^nb^n is regular.
     Thus there is a DFA A that accepts a^nb^n for any n.
     Fix n = |A| + 1.
     Define a function f: {0..n} -> Q where f(x) = the state of the dfa after
     x a's have been matched.
     Then, by the PHP, we have that f(x) = f(y) for some numbers x != y.
     By construction, the DFA accepts a^xb^x, which means it accepts the
     string b^x from state f(x).
     Since f(x) = f(y), the DFA also accepts a^yb^x, a contradiction.

     Intuition:

     ----   ----    ----
     |q |-> | p| -> |r |
     ----   ----    ----
   
     p is the state of the DFA we are in after x 0's and y 0's have been matched
     thus q matches x 0's and y 0's
     r matches b^x by construction
     thus this DFA matches both a^xb^x and a^yb^x
   *)
  

  (**
     This proof does not exactly follow the proof above.
     But it contains a similar idea.     
   *)
  
  Definition residual (L: lang char) (x: seq char): seq char -> Prop :=
    fun (y: seq char) => L (x ++ y).

  Lemma residualP (f : nat -> word char) (L : lang char) :
    (forall (n1 n2: nat), residual L (f n1) =p residual L (f n2) -> n1 = n2) ->
    ~ inhabited (regular L).
  Proof.
    move => f_spec [[A E]].
    
    pose f' (n : 'I_#|A|.+1) := delta_s A (f n).

    (* suff: injective f' by move/card_leq_inj ; rewrite card_ord ltnn. *)
    suff: injective f'.
    - Print card_leq_inj.
      move /card_leq_inj.
      rewrite card_ord ltnn.
      by [].

    move => [n1 H1] [n2 H2].
    rewrite /f' /delta_s /= => H. 
    apply/eqP; change (n1 == n2); apply/eqP.
    apply: f_spec => w.
    rewrite /residual.
    rewrite !E.
    rewrite !inE.
    rewrite /dfa_accept.
    rewrite !delta_cat.
    by rewrite H.
  Qed.

  Lemma countL (n1 n2: nat):
    count (pred1 a) (nseq n1 a ++ nseq n2 b) = n1.
  Proof. 
    by rewrite count_cat !count_nseq /= eqxx eq_sym (negbTE Hab) mul1n mul0n addn0. 
  Qed.

  Lemma countR (n1 n2: nat):
    count (pred1 b) (nseq n1 a ++ nseq n2 b) = n2.
  Proof.
    by rewrite count_cat !count_nseq /= (negbTE Hab) eqxx //= mul1n mul0n.
  Qed.

  Lemma Lab_eq (n1 n2: nat):
    Lab (nseq n1 a ++ nseq n2 b) ->
    n1 = n2.
  Proof.
    move => [n H].
    by rewrite -[n1](countL _ n2) -{2}[n2](countR n1 n2) H countL countR.
  Qed.
  

  Lemma Lab_not_regular:
    ~ inhabited (regular Lab).
  Proof.
    pose f n := nseq n a.
    apply: (@residualP f) => n1 n2.
    move/(_ (nseq n2 b)) => H.
    apply: Lab_eq.
    apply H.
    by exists n2.
  Qed.
  
End NonRegular.


(** ** Pumping Lemma 

   - Is there a more generic way to construct a counter example?
   - Yes: this is given by the pumping lemma for regular languages.
*)

Section Pumping.
  (** *** Get the substring between i and j *)
  Definition sub (T:eqType) (i j: nat) (s : seq T): seq T :=
    take (j-i) (drop i s).

  (** *** Repeat a substring *)
  Definition rep (T : eqType) (s : seq T) (n: nat) : seq T :=
    iter n (cat s) [::].

  Variable char : finType.

  (**
     - What is this lemma intuitively saying?
     - If I land at the same dfa state after matching x,
       then I can match any number of repititions of x.
   *)
  Lemma delta_rep (A : dfa char) (p : A) (x: seq char) (i: nat) :
    delta p x = p ->
    delta p (rep x i) = p.
  Proof.
    elim: i => //=.
    move => i IH H.
    rewrite delta_cat.
    rewrite H.
    rewrite IH //.
  Qed.

  Locate "/\".
  Check nilp.

  (*
     Claim: 
     
     If
        1. x ++ y ++ z is recognized by a DFA A
        2. |A| < |y|
     Then there exists words u, v, w s.t.
        1. |v| > 0
        2. y = u ++ v ++ w
        3. x ++ u ++ v^* ++ w ++ y is recogized by A
     
     Intuition:

     ----   ----    ----
     |q |-> | p| -> |r |
     ----   ----    ----
   
     q matches x ++ u
     p matches v
     r matches w ++ y

            ----
            |P'|
            ----
            ^ |
            | |
            | v
     ----   ----    ----
     |q |-> | p| -> |r |
     ----   ----    ----

     q matches x ++ u
     p <-> p' matches v by PHP, and therefore, can match any number of v
     r matches w ++ y

   *)
  Lemma pump_dfa (A: dfa char) (x y z: seq char) :
    x ++ y ++ z \in dfa_lang A ->
    #|A| < size y ->
    exists u v w,
    [/\ ~~ nilp v, y = u ++ v ++ w & forall i, (x ++ u ++ rep v i ++ w ++ z) \in dfa_lang A].
  Proof.
    rewrite -delta_lang.
    move => H1 H2.

    (* I'_n gives the set {0, ..., n}. *)
    Locate "''I_' _'".

    (*
       Claim:
       (fun i: {0, ..., |y|} => delta (delta_s A x) (take i y)) is not injective.
     *)
    have /injectivePn:
      ~~ injectiveb (fun i : 'I_(size y) => delta (delta_s A x) (take i y)).
    {
      apply: contraL H2.
      move => /injectiveP.
      move => /card_leq_inj.
      rewrite leqNgt.
      rewrite card_ord.
      by [].
    }

    (* 
       f_{ij} contains the claim that we have two different strings that
       get us to the same DFA state.
     *)
    move => [i] [j] ij fij.
    wlog {ij} ij : i j fij / i < j.
    {
      rewrite neq_ltn in ij.
      case/orP : ij => ij W; exact: W _ ij.
    }

    (* y = u ++ v ++ w
         = take i y ++ sub i j y ++ drop j y *)
    exists (take i y).
    exists (sub i j y). 
    exists (drop j y).
    
    split => [||k].
    {
      (* ~~ nilp v *)
      apply: contraL ij.
      rewrite /nilp.
      rewrite size_take.
      rewrite size_drop.
      rewrite ltn_sub2r //.
      rewrite subn_eq0.
      rewrite leqNgt.
      by [].
    }
    {
      (* y = take i y ++ sub i j y ++ drop j y *)
      rewrite catA.
      rewrite -takeD.
      rewrite subnKC //.
      - rewrite cat_take_drop //.
      - rewrite ltnW //.
    }
    {
      (* x ++ take i y ++ sub i j y ++ drop j y ++ z \in dfa_lang A *)
      rewrite inE.
      rewrite /dfa_accept.
      rewrite !delta_cat.

      (* This is where we get the "cycle". *)
      rewrite delta_rep.
      - rewrite fij. (* *)
        rewrite -!delta_cat.
        rewrite !catA.
        rewrite -[(x ++ _) ++ _]catA.
        rewrite cat_take_drop.
        rewrite -!catA.
        by [].
      rewrite -delta_cat.
      rewrite -takeD.
      rewrite subnKC //.
      exact: ltnW.
    }
  Qed.

  Lemma pumping (L : word char -> Prop) :
    (forall k, exists x y z, k <= size y /\ L (x ++ y ++ z) /\
      (forall u v w, y = u ++ v ++ w -> ~~ nilp v ->
         exists i, L (x ++ u ++ rep v i ++ w ++ z) -> False))
     -> ~ inhabited (regular L).
  Proof.
    move => H.
    move => [[A LA]].
    move/(_ #|A|.+1) : H => [x] [y] [z] [size_y [/LA Lxyz]].

    (* Interesting step: witness using the DFA *)
    move: (pump_dfa Lxyz size_y) => [u] [v] [w] [Hn Hy Hv] /(_ u v w Hy Hn).

    move => [i].
    apply.
    exact /LA.
  Qed.

  Lemma cat_nseq_eq n1 n2 (a : char) :
    nseq n1 a ++ nseq n2 a = nseq (n1+n2) a.
  Proof.
    elim: n1 => [|n1 IHn1] //=.
    by rewrite -cat1s IHn1.
  Qed.


  (** *** Exercise
      
     Try to figure out how to use the pumping lemma to show that
     the language of a^nb^n is not regular before diving into this proof.
   *)

  Example pump_Lab (a b : char) : a != b -> ~ inhabited (regular (Lab a b)).
  Proof.
    move => neq.
    apply: pumping => k.
    exists [::].
    exists (nseq k a).
    exists (nseq k b).
    repeat split.
    - (* k <= size (nseq k a) *)
      by rewrite size_nseq.
    - (* Lab a b ([::] ++ nseq k a ++ nseq k b) *)
      by exists k.
    - (* forall u v w : seq char,
         nseq k a = u ++ v ++ w ->
         ~~ nilp v ->
         exists i : nat, Lab a b ([::] ++ u ++ rep v i ++ w ++ nseq k b)
         -> False *)
      move => u [|c v] w // /eqP e _.
      exists 0 => /= H.
      have Hk: k = size (u ++ (c::v) ++ w) by rewrite -[k](@size_nseq _ _ a) (eqP e).
      rewrite Hk !size_cat -!cat_nseq_eq !eqseq_cat ?size_nseq // in e.
      case/and3P : e => [/eqP Hu /eqP Hv /eqP Hw].
      rewrite -Hu -Hw catA cat_nseq_eq in H.
      move/(Lab_eq neq) : H.
      move/eqP. by rewrite Hk !size_cat eqn_add2l -{1}[size w]add0n eqn_add2r.
  Qed.

End Pumping.


(** ** Summary

   - We introduceed deterministic finite automata (DFA) as an
     abstract machine.
   - In particular, we saw that the DFA transition function was
     a small-step semantics.
   - We saw that DFAs recognize regular languages and that non-regular
     languages exists via the pumping lemma.
 *)
