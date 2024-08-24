(** * Regular Expressions, NFAs, and DFAs *)

From mathcomp Require Import all_ssreflect.


(** ** References

   - https://github.com/coq-community/reglang

     Authors: Christian Doczkal and Jan-Oliver Kaiser
     Distributed under the terms of CeCILL-B.
 *)
Require Import lec_05_dfa.
(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
Require Import lib_reglang.
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** Recap
   - Last time, we saw DFAs as our first example of an abstract machine.
   - As a reminder, the transition function was the small-step semantics.
   - Today, we'll take a linguistic view of the DFA.
 *)

(** ** Goal for today

   - Introduce _regular expressions_ (REs) and show that they are equivalent
     to DFAs.  In particular, we'll see that REs are the "language" corresponding
     to a DFA.
   - We'll show the equivalence of REs and DFAs via non-deterministic
     finite automata (NFA). NFAs will make the proof of equivalence easier.
 *)


Section RegExp.
  Variable char : eqType.

  (** *** Syntax *)
  (*
     e ::= 0
         | \epsilon
         | c
         | e*
         | e + e
         | ee
   *)
  
  Inductive regexp :=
  | Void                      (* empty regular expression *)
  | Eps                       (* match nothing *)
  | Atom of char              (* match a character *)
  | Star of regexp            (* any number of matches *)
  | Plus of regexp & regexp   (* or. this is usually written | *)
  | Conc of regexp & regexp   (* concatenation *)
  .

  (** *** Equality of regular expressions is decidable *)
  Lemma eq_regexp_dec (e1 e2: regexp):
    {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality.
    apply: eq_comparable.
  Qed.

  Definition regexp_eqMixin :=
    EqMixin (compareP eq_regexp_dec).

  Canonical Structure form_eqType :=
    EqType _ regexp_eqMixin.
End RegExp.


Arguments void : clear implicits.
Arguments eps : clear implicits.
Prenex Implicits Plus.
Arguments plusP {char r s w}.
Notation "'Void'" := (@Void _).
Notation "'Eps'" := (@Eps _).


(** 
  - For a DFA, we defined the language that it recognized by those words that
    when fed into a DFA transitioned from the start state to a final state.
  - How might we do this for a regular expression?
  - We define the language recognized by a regular expression by
    structural recursion on the regular expression.
 *)

Fixpoint re_lang (char: eqType) (e: regexp char): dlang char :=
  match e with
  | Void => void char
  | Eps => eps char
  | Atom x => atom x
  | Star e1 => star (re_lang e1)
  | Plus e1 e2 => plus (re_lang e1) (re_lang e2)
  | Conc e1 e2 => conc (re_lang e1) (re_lang e2)
  end.

Print void.
(** ==> [fun char : eqType => pred0] *)

Print eps.
(** ==> [fun char : eqType => pred1 [::]] *)

Print atom.
(** ==> [fun (char : eqType) (x : char) => pred1 [:: x]] *)

Print star.
(**
<<
fun (char : eqType) (l : dlang char) =>
fix star (v : word char) : bool :=
  match v with
  | [::] => true
  | x :: v' => conc (languages.residual x l) star v'
  end
>>
*)

Print plus.
(**
<<
   fun (char : eqType) (l1 l2 : dlang char) => [pred w | (w \in l1) || (w \in l2)]
>>
 *)

Print conc.
(**
<<
   fun (char : eqType) (l1 l2 : dlang char) (v : word char) =>
     [exists i, l1 (take i v) && l2 (drop i v)]
>>
 *)

(*

  We could also define this via the following inductive relation.

   ---------------------------
   (\epsilon, []) \in re_lang

   ---------------------------
      (c, [c]) \in re_lang

   ---------------------------
       (e*, []) \in re_lang

    (e, w1) \in re_lang   (e*, w2) \in re_lang
   ---------------------------------------------
           (e+e*, w1++w2) \in re_lang
         
        (e1, w) \in re_lang
   -----------------------------
       (e1+e2, w) \in re_lang

        (e2, w) \in re_lang
   -----------------------------
       (e1+e2, w) \in re_lang

     (e1, w1) \in re_lang  (e2, w2) \in re_lang
   ---------------------------------------------
             (e1e2, w1++w2) \in re_lang
 *)



(*
  
  What languages do these regular expressions match?

   Example 1:
     101 + 010

   Example 2:
     ((00)*1)*

   Example 3:
     ((11)*0)*
 *)


(**
  - We're going to prove that regular expressions and DFAs recognize the same languages.
  - To do this, we'll introduce two new concepts: nondeterministic finite automata (NFA)
     and epsilon nondterministic finite automata (eNFA).
  - Why are we doing this?
    * It will be easy to convert between DFA and NFA.
    * It will be easy to convert between NFA and eNFA.
    * It will be easier to prove properties of * and + using eNFA.
    * It will be easy to translate DFA into RE.
*)

(* Picture to keep in mind.

     |-> RE
     |   |
     |   v
     |  NFA <-> eNFA
     |  ^ |
     |  | v
     |--DFA

 *)


(** ** Nondeterministic Finite Automata (NFA) *)

(* Picture to keep in mind.

 |-> RE
 |   |
 |   v
 | *NFA* <-> eNFA
 |  * *
 |  ^ |
 |  | v
 |  * *
 |--DFA
  
   Why NFA? It will be easier to connect RE's to DFA's via NFA's.
 *)

      
Section NFA.

  Variable char : finType.
  Local Notation word := (word char).


  (**
     Nondeterministic Finite Automata is a 5-tuple (Q, \Sigma, S, F, \delta) where
     - Q is a finite set of states
     - \Sigma is a finite alphabet of characters
     - S is a set of starting states
     - F is a set of final states
     - \delta: Q x \Sigma x Q -> bool is a transition *relation*
   *)
  Record nfa : Type :=
    {
      nfa_state :> finType;

      nfa_s: {set nfa_state};    (* dfa_s: dfa_state *)
      nfa_fin: {set nfa_state};  (* dfa_fin: {set dfa_state} *)

      (* dfa_trans: dfa_state -> char -> dfa_state *)          
      nfa_trans: nfa_state -> char -> nfa_state -> bool
    }.
  
  (**
     - Defining NFA acceptance by structural recursion on words.    
   *)
  Fixpoint nfa_accept (A: nfa) (x: A) (w: word): bool :=
    if w is a :: w'
    then
      (**
         - Different from DFA.
         - There can be multiple transitions.
       *)
      [exists (y | nfa_trans x a y), nfa_accept y w']
    else
      (* same as DFA *)
      x \in nfa_fin A.


  (**
     - As before, the language of a NFA A is the set of words that it accepts.
   *)
  Definition nfa_lang (A: nfa): simpl_pred word :=
    [pred w | [exists s, (s \in nfa_s A) && nfa_accept s w]].


  Section DFA_TO_NFA.
    (* Goal: DFA -> NFA
 
        |-> RE
        |   |
        |   v
        |  NFA <-> eNFA
        |  * |
        |  ^ |
        |  | |
        |  * v
        |--DFA  
    *)
    Variable A : dfa char.
    
    Definition dfa_to_nfa : nfa :=
      {|
        nfa_s := [set dfa_s A];                 (* singleton set *)
        nfa_fin := dfa_fin A;                   (* nothing changes *)
        nfa_trans :=
          fun (x: A) (a: char) (y: A) => dfa_trans x a == y   (* graph of function *)
      |}.

    (**
       - Hopefully, it is easy to see that this DFA to NFA construction is correct.
       - You might notice that this is an *embedding*.
       - What if you were asked to prove it?
       - Proof: by structural induction on words and "follow the logic/definitions".
     *)
    Locate "=i".
    Lemma dfa_to_nfa_correct:
      dfa_lang A =i nfa_lang dfa_to_nfa.
    Proof.
      move => w.
      rewrite !inE.
      rewrite /nfa_s /=.
      
      (* Induction on word *)
      elim: w (dfa_s A) => [|b w IHw] x; rewrite accE /=.
      {
        (* nil *)
        apply/idP/existsP => [Fx|[y /andP [/set1P ->]]//]. 
        exists x.
        by rewrite !inE eqxx.
      }
      {
        (* cons *)
        rewrite IHw.

        (* Show set equality by showing both directions of inclusion. *)
        apply /exists_inP /exists_inP.
        - case => y.
          case => /set1P -> H.
          exists x; first exact: set11.
          apply/existsP.
          exists (dfa_trans x b).
          by rewrite H eqxx.
        - case => y /set1P -> {y} /existsP [z] /andP [] /eqP-> H.
          exists z; by rewrite ?set11.
      }
    Qed.
    
  End DFA_TO_NFA.

  
  Section NFA_TO_DFA.
    (* Goal: NFA -> DFA
 
        |-> RE
        |   |
        |   v
        |  NFA <-> eNFA
        |  ^ *
        |  | |
        |  | |
        |  | *
        |--DFA   
     *)
    
    Variable A : nfa.

    (**
       - Translating a NFA to a DFA is also possible.
       - This might seem hard to believe if this is your first time seeing such a translation.
       - In particular, a NFA enables non-deterministic transitions whereas a DFA is
         deterministic.
       - The following is a useful trick to convert a problem with non-determinism into
         a deterministic solution: use the *powerset*.
     *)
    Definition nfa_to_dfa :=
      {|
        dfa_s := nfa_s A;
        dfa_fin := [set X | X :&: nfa_fin A != set0];
        dfa_trans :=
          fun (X: set_of_finType A) (a: char) =>
            [set q | [exists (p | p \in X), nfa_trans p a q]] 
      |}.

    (* Example

       Input NFA

            0 
          A -> B
      0/1 |
          v
          C

       Output DFA

             0
         {A} -> {B, C}
     0/1  |
          v
         {C}   {}  {B}  {A, B}  {A, C} {A, B, C} 
     *)

    
    (**
       - Whereas the correctness of embedding a DFA into a NFA might be convincing
         without proof, the reduction of a NFA into a DFA might require "more proof".
       - Proof.
         
         By structural induction on words.

         Case w = nil :
           The definition of accepting states coincide.

         Case w = a::x :
           We have to show
           [exists s, (s \in S) && nfa_accept s (a::x)] = dfa_accept S (a::x)

           which is equivalent to

           [exists s, [exists (y | nfa_trans s a y), nfa_accept y x]] = dfa_accept (dfa_trans X a) x.

           given the IH [exists s, (s \in S) && nfa_accept s x] = dfa_accept S x for any S.
           Using our IH, we now have to show that
           
           [exists s, (s \in S) && [exists (y | nfa_trans s a y), nfa_accept y x]] =
           [exists s, (s \in dfa_trans S a) && nfa_accept s x].

           This follows by proving mutual inclusion and following the definitions.           
     *)
    Lemma nfa_to_dfa_correct : nfa_lang A =i dfa_lang nfa_to_dfa.
    Proof.
      Locate "=i".
      rewrite /eq_mem.
      move => w.      
      rewrite !inE {2}/nfa_to_dfa /=.

      (* structural induction on words *)
      elim: w (nfa_s _) => [|a x IH] X; rewrite /= accE ?inE.
      {
        apply/existsP/set0Pn => [] [p] H; exists p; by rewrite inE in H *.                          }
      {
        rewrite -IH.

        (* Show set equality by showing both directions of inclusion. *)
        apply/exists_inP/exists_inP.
        - (* -> *)
          case => p inX /exists_inP [q ? ?].
          exists q => //.
          rewrite inE. 
          apply/exists_inP.
          by exists p.
        - (* <- *)
          case => p.
          rewrite inE => /exists_inP [q] ? ? ?.
          exists q => //.
          apply/exists_inP.
          by exists p.
      }
    Qed.

  End NFA_TO_DFA.


  (** *** Epsilon Nondeterministic Finite Automata (NFA) or (eNFA) *)

  (* Goal: NFA -> DFA
 
        |-> RE
        |   |
        |   v
        |  NFA <-> *eNFA*
        |  ^ |
        |  | v
        |--DFA

       Why eNFA? It will be easier to connect properties of RE to properties of eNFA.
       - Think about concatenation?
       - Think about *?
     *)
  
  
  (** *** Epsilon NFAs *)

  (**
     A Nondeterministic Finite Automata (eNFA) with empty character is a
     5-tuple (Q, \Sigma, S, F, \delta) where
     - Q is a finite set of states
     - \Sigma is a finite alphabet of characters
     - S is a set of starting states
     - F is a set of final states
     - \delta: option \Sigma x Q x Q -> bool is a transition *relation*

     We model the empty character as option \Sigma.
   *)
  Record enfa : Type :=
    {
      enfa_state :> finType;
      enfa_s : {set enfa_state};
      enfa_f : {set enfa_state};
      (**
         - None means we don't consume a character
         - [Some x] means we have a character
       *)
      enfa_trans : option char -> enfa_state -> enfa_state -> bool
    }.

  Section EpsilonNFA.
    Variable N: enfa.

    (** 
        - We define enfa acceptance relatationally because structural
          recursion over the word is no longer possible. Why?
        - The inference rules are given below
     *)        
    (* Defining enfa_accept

             q \in enfa_f N
       ------------------------ EnfaFin
         enfa_accept (q, [::])

         (Some a, p) -> q   enfa_accept (q, x)
       ---------------------------------------- EnfaSome
                  enfa_accept (p, a::x)
          

         (None, p) -> q    enfa_accept (q, x)
       ---------------------------------------- EnfaNone
                   enfa_accept (p, x)

     *)
    Inductive enfa_accept: N -> word -> Prop :=
    | EnfaFin (q: enfa_state N):
      q \in enfa_f N ->
      enfa_accept q [::]
    | EnfaSome (p: enfa_state N) (a: char) (q: enfa_state N) (x: word):
      enfa_trans (Some a) p q ->
      enfa_accept q x ->
      enfa_accept p (a::x)
    | EnfaNone (p: enfa_state N) (q: enfa_state N) (x: word):
      enfa_trans None p q ->
      enfa_accept q x ->
      enfa_accept p x.

    (**
       - Like before, the language of an eNFA N is the set of words that
         it accepts.
       - Unlike before, we need to use the more general
         [word -> Prop] as opposed to [simpl_pred word].
     *)
    Definition enfa_lang (x: word): Prop :=
      exists2 s, s \in enfa_s N & enfa_accept s x.

    (*
      At this point, we've defined
      1. NFA
      2. eNFA

      Now we're going to show that NFA <-> eNFA
 
        |-> RE
        |   |
        |   v
        |  NFA *<->* eNFA
        |  ^ |
        |  | v
        |--DFA
    *)

    (** 
        - How could NFA's and eNFA's possibly be equivalent?
        - It should hopefully by easy to see that we can convert a NFA into an eNFA.
        - And moreover, an eNFA should accept more words than a NFA.
        - What about the reverse direction?
        - If it is at all equivalent, then at the very minimum, all states reachable by
          empty transitions should be accounted for in the NFA view.
        - We'll do this now.
        - [connect] is a function that takes a relation to a relation and will take the
          reflexive transitive closure.
        - <<
          connect = 
           fun (T : finType) (e : rel T) => [rel x y | y \in dfs (rgraph e) #|T| [::] x]
           : forall T : finType, rel T -> rel T
          >>
          * nugget: why dfs (depth-first search)?
          * 
            <<
            rgraph = 
              fun (T : finType) (e : rel T) (x : T) => enum (e x)
              : forall T : finType, rel T -> T -> seq T
            >>
     *)
    Locate connect.
    Print connect.
    Definition eps_reach (p: enfa_state N): {set enfa_state N} :=
      [set q | connect (enfa_trans None) p q].

    (**
       -  p --> q and q accepts x
       -  means that p also accepts x.
     *)
    Lemma lift_accept (p q: enfa_state N) (x: word) :
      q \in eps_reach p ->
      enfa_accept q x ->
      enfa_accept p x.
    Proof.
      rewrite inE.
      move /connectP.
      move => [s].

      (* Induction on length of path. *)
      elim: s p x q => //=.
      - (* nil *)
        move => p q x _ ->.
        by [].        
      - (* cons *)
        move => q s IHs p x q'.
        case/andP => pq ? ? H.
        apply: EnfaNone pq _.
        exact: IHs H.
    Qed.

    (**
       - Building the corresponding NFA from an eNFA
       - A transition is valid iff 
          1. it is in the eNFA transition relation that consumes a character and
          2. it is in the epsilon-closure
     *)
    Definition nfa_of: nfa :=
      {|
        nfa_s := \bigcup_(p in enfa_s N) (eps_reach p);
        nfa_fin := enfa_f N;
        nfa_trans (p: N) (a: char) (q: N) :=
          [exists p', enfa_trans (Some a) p p' && (q \in eps_reach p') ]
      |}.

    Lemma enfaE (x: word) (p: enfa_state N) :
      (enfa_accept p x) <-> (exists2 q : nfa_of, q \in eps_reach p & nfa_accept q x).
    Proof.
      split.
      { (* (=>) direction *)

        (* Induction on enfa_accept *)
        elim => {p x} [q H|p a q x H _ [q' Hq1 Hq2]|p p' x].
        + (* EnfaFin *)
          exists q => //.
          rewrite inE.
          rewrite connect0.
          by [].
        + (* EnfaSome *)
          exists p => /=; first by rewrite inE connect0.
          apply/exists_inP.
          exists q' => //.
          apply/exists_inP.
          by exists q.
        + (* EnfaNone *)
          move => H1 H2 [q Hq1 Hq2].
          exists q => //.
          rewrite !inE in Hq1 *.
          exact: connect_trans (connect1 _) Hq1.
      }
      { (* (<=) direction  *)

        (* Induction on word *)
        elim: x p => [|a x IH] p [p'] R /= H.
        + (* nil *)
          apply: lift_accept R _.
          exact: EnfaFin.
        + (* cons *)
          case/exists_inP : H => q /exists_inP [q' pq' qq'] H.
          apply: lift_accept R _.
          apply: EnfaSome pq' _.
          apply: IH.
          by exists q.
      }
    Qed.

    (**
       - For reflection purposes.
     *)
    Lemma nfa_ofP (x: word):
      reflect (enfa_lang x) (x \in nfa_lang nfa_of).
    Proof.
      apply: (iffP exists_inP) => [[p Hp1 Hp2]|[s Hs1 /enfaE [p Hp1 Hp2]]].
      - case/bigcupP : Hp1 => s Hs H.
        exists s => //.
        by apply/enfaE; exists p.
      - exists p => //.
        by apply/bigcupP; exists s.
    Qed.
  End EpsilonNFA.


  (** *** Operations on NFAs/eNFAs 

     - For each language construct in a RE, we will define the corresponding
       operation on a NFA or eNFA, whichever is easier. By the equivalence of
       NFA and eNFA, we will be able to convert all the operations defined on
       a eNFA back into a NFA.
     - As a reminder, the following operations are:
        1. eps
        2. char
        3. +
        4. concat
        5. *
   *)

  (** **** 1. eps 

     - Final and starting state are the same.
     - No transitions.
   *)
  Definition nfa_eps : nfa := 
    {|
      nfa_s := [set tt];
      nfa_fin := [set tt];
      nfa_trans :=
        fun p q q => false
    |}.

  Lemma nfa_eps_correct:
    nfa_lang (nfa_eps) =i pred1 [::].
  Proof. 
    move => w.

    (* Set equality by mutual inclusion. *)
    apply/exists_inP/idP.
    + (* (=>) direction *)
      move => [[]].
      case: w => [|a w] //= _.
      by case/exists_inP.
    +(* (<=) direction *)
      move => /=.
      rewrite inE=>/eqP->.
      exists tt; by rewrite /= inE.
  Qed.

  (** **** 2. char 
      - One transition from starting state to final state if b == a.
   *)
  Definition nfa_char (a:char) := 
    {|
      nfa_s := [set false]; 
      nfa_fin := [set true]; 
      nfa_trans :=
        fun p b q => if (p,q) is (false,true) then (b == a) else false
    |}.
  
  Lemma nfa_char_correct (a : char) :
    nfa_lang (nfa_char a) =1 pred1 [:: a].
  Proof. 
    move => w /=.

    (* Set equality by mutual inclusion. *)
    apply/exists_inP/eqP => [[p]|].
    - rewrite inE => /eqP->.
      case: w => [|b [|c w]] /=; first by rewrite inE.
      + by case/exists_inP => [[/eqP->|//]].
      + case/exists_inP => [[_|//]]. by case/exists_inP.
    - move->.
      exists false; first by rewrite inE.
      apply/exists_inP. 
      exists true; by rewrite ?inE //=.
  Qed.

 
  (** **** 3. + 

     - What's the picture for this?
     - Can start in either NFA N or NFA M.
     - Can end in either NFA N or NFA M.
     - Use transitions in either one.
   *)

  Definition nfa_plus (N M : nfa) := 
    {|
      nfa_s := [set q | match q with inl q => q \in nfa_s N | inr q => q \in nfa_s M end ];
      nfa_fin := [set q | match q with inl q => q \in nfa_fin N | inr q => q \in nfa_fin M end ];
      nfa_trans :=
        fun p a q =>
          match p,a,q with  
          | inl p,a,inl q => nfa_trans p a q
          | inr p,a,inr q => nfa_trans p a q
          | _,_,_ => false
          end
    |}.

  Lemma nfa_plus_correct (N M : nfa) : 
    nfa_lang (nfa_plus N M) =i plus (nfa_lang N) (nfa_lang M).
  Proof.
    move => w.

    (* Set equality by mutual inclusion *)
    apply/idP/idP.
    {
      case/exists_inP => [[s|s]]; rewrite !inE => A B;
      apply/orP;[left|right];apply/exists_inP; exists s => //.
      + elim: w s {A} B => /= [|a w IH] s; first by rewrite inE.
        case/exists_inP => [[|]// p A /IH B].
        apply/exists_inP.
        by exists p.
      + elim: w s {A} B => /= [|a w IH] s; first by rewrite inE.
        case/exists_inP => [[|]// p A /IH B].
        apply/exists_inP.
        by exists p.
    }
    {
      rewrite !inE. case/orP => /exists_inP [s A B]; 
      apply/exists_inP; [exists(inl s)|exists(inr s)]; rewrite ?inE //.
      + elim: w s {A} B => /= [|a w IH] s; first by rewrite inE.
        case/exists_inP => [p A /IH B].
        apply/exists_inP.
        by exists (inl p).
      + elim: w s {A} B => /= [|a w IH] s; first by rewrite inE.
        case/exists_inP => [p A /IH B].
        apply/exists_inP.
        by exists (inr p).
    }
  Qed.

  
  (** 
      - We will want to use eNFAs to show concatenation and Kleene star.
      - We can then build the corresponding NFA back from an eNFA.
   *)
  Section eNFAOps.    
    Variables A1 A2 : nfa.

    (** **** 4. concat 

       - What's the picture for this?
     *)
    
    Definition enfa_conc: enfa :=
      {|
        enfa_s := inl @: nfa_s A1;
        enfa_f := inr @: nfa_fin A2;
        enfa_trans :=
          fun c p q =>
            match c,p,q with
            | Some a,inl p',inl q' => nfa_trans p' a q'
            | Some a,inr p',inr q' => nfa_trans p' a q'
            | None,inl p', inr q' => (p' \in nfa_fin A1) && (q' \in nfa_s A2)
            | _,_,_ => false
            end
      |}.

    Definition nfa_conc: nfa :=
      nfa_of (enfa_conc).

    Lemma enfa_concE (p: enfa_conc) (x: word):
      enfa_accept p x ->
      match p with
      | inr p' => nfa_accept p' x
      | inl p' => exists x1 x2, [/\ x = x1 ++ x2, nfa_accept p' x1 & x2 \in nfa_lang A2]
      end.
    Proof.
      elim => {p x} [[?|?] /imsetP [q] // ? [->] //||].
      - move => [p|p] a [q|q] x //.
        + move => pq _ [x1] [x2] [X1 X2 X3]. exists (a::x1); exists x2; subst; split => //.
          by apply/exists_inP; exists q.
        + move => pq _ Hq.
          by apply/exists_inP; exists q.
      - move => [p|p] [q|q] //= x /andP[Hp Hq] _ ?. exists [::]; exists x; split => //.
        by apply/exists_inP; exists q.
    Qed.

    Lemma enfa_concIr (p: A2) (x: word):
      nfa_accept p x ->
      @enfa_accept enfa_conc (inr p) x.
    Proof.
      elim: x p => [p Hp|a x IH p /= /exists_inP [q q1 q2]].
      - (* compat: <mathcomp-1.12 *)
        constructor; solve [exact: imset_f|exact:mem_imset]. 
      - apply: (@EnfaSome enfa_conc _ _ (inr q)) => //.
        exact: IH.
    Qed.

    Lemma enfa_concIl (p: A1) (x1 x2: word) :
      nfa_accept p x1 ->
      x2 \in nfa_lang A2 ->
      @enfa_accept enfa_conc (inl p) (x1++x2).
    Proof.
      elim: x1 p => /= [p Hp /exists_inP [q q1 q2]|a x1 IH p /exists_inP [q q1 q2] H].
      - apply: (@EnfaNone enfa_conc _ (inr q)). by rewrite /= Hp. exact: enfa_concIr.
      - apply: (@EnfaSome enfa_conc _ _ (inl q)). by rewrite /= q1. exact: IH.
    Qed.

    Lemma enfa_concP (x: word):
      reflect (enfa_lang enfa_conc x) (conc (nfa_lang A1) (nfa_lang A2) x).
    Proof.
      apply: (iffP (@concP _ _ _ _)) => [[x1] [x2] [X1 [X2 X3]] |].
      - (* compat: <mathcomp-1.12 *)
        case/exists_inP : X2 => s ? ?. exists (inl s); first solve [exact: imset_f|exact:mem_imset].
        subst. exact: enfa_concIl.
      - move => [[s /imsetP [? ? [?]] /enfa_concE [x1] [x2] [? ? ?] |s]]; last by case/imsetP.
        exists x1; exists x2. repeat (split => //). apply/exists_inP. by exists s;subst.
    Qed.

    Lemma nfa_conc_correct:
      nfa_lang nfa_conc =i conc (nfa_lang A1) (nfa_lang A2).
    Proof.
      move => x.
      apply/nfa_ofP/idP => ?;exact/enfa_concP.
    Qed.

    (** **** 5. star 

        - What's the picture for this?
     *)

    Definition enfa_star : enfa :=
      {|
        enfa_s := [set None];
        enfa_f := [set None];
        enfa_trans :=
          fun (c: option char) p q =>
            match c,p,q with
              Some a,Some p', Some q' =>
                (* transition as before *)
                q' \in nfa_trans p' a
            | None, Some p', None =>
                (* \epsilon transition to final state *)
                p' \in nfa_fin A1
            | None, None, Some s =>
                (* \epsilon transition from start state *)
                s \in nfa_s A1
            | _,_,_ => false
            end
      |}.

    Definition nfa_star : nfa :=
      nfa_of (enfa_star).

    Lemma enfa_s_None:
      None \in enfa_s enfa_star.
    Proof.
      by rewrite inE.
    Qed.

    Lemma enfa_f_None:
      None \in enfa_f enfa_star.
    Proof.
      by rewrite inE.
    Qed.
    
    Hint Resolve enfa_s_None enfa_f_None : core.

    Lemma enfa_star_cat (x1 x2: word) (p : enfa_star):
      enfa_accept p x1 ->
      enfa_lang enfa_star x2 ->
      enfa_accept p (x1 ++ x2).
    Proof.
      (* Question: What are we inducting on? *)
      elim => {p x1}.
      {
        move => p.
        rewrite inE => /eqP->.
        case => q.
        by rewrite inE => /eqP->.
      }
      {
        move => p a q x /=.
        case: p => // p.
        case: q => // q pq ? IH H.
        exact: EnfaSome (IH H).
      }
      {
        move => [p|] [q|] x //= p1 p2 IH H; exact: EnfaNone (IH H).
      }
    Qed.

    Lemma enfa_starI (x: word) (p : A1):
      nfa_accept p x ->
      @enfa_accept enfa_star (Some p) x.
    Proof.
      (* Questio: What are we inducting on? *)
      elim: x p => /= [p H|a x IH p].
      {
        apply: (@EnfaNone enfa_star _ None) => //.
        exact: EnfaFin.
      }
      {
        case/exists_inP => q q1 /IH.
        exact: EnfaSome.
      }
    Qed.

    Lemma enfa_star_langI (x: word):
      x \in nfa_lang A1 -> @enfa_accept enfa_star None x.
    Proof.
      case/exists_inP => s s1 s2.
      apply: (@EnfaNone enfa_star _ (Some s)) => //. exact: enfa_starI.
    Qed.

    Lemma enfa_starE (o: enfa_star) (x: word):
      enfa_accept o x ->
      if o is Some p
      then exists x1 x2, [/\ x = x1 ++ x2, nfa_accept p x1 & star (nfa_lang A1) x2]
      else star (nfa_lang A1) x.
    Proof.
      (* Question: What are we inducting on? *)
      elim => {x o}.
      {
        move => [q|//].
        by rewrite inE; move/eqP.
      }
      {
        move => [p|] a [q|] x // H acc [x1] [x2] [H1 H2 H3].
        exists (a::x1); exists x2.
        rewrite H1.
        split => //.
        by apply/exists_inP; exists q.
      }
      {
        move => [p|] [q|] x //=.
        + move => *. by exists [::]; exists x.
        + move => H acc [x1] [x2] [H1 H2].
          rewrite H1.
          apply: star_cat.
          by apply/exists_inP; exists q.
      }
    Qed.

    (** 
        - For reflection purposes.
     *)
    Lemma enfa_starP (x: word):
      reflect (enfa_lang enfa_star x) (star (nfa_lang A1) x).
    Proof.
      (* Show both sides of inclusion *)
      apply: (iffP idP).
      { (* => *)
        case/starP => vv H ->. elim: vv H => /= [_|v vv].
        + exists None => //. exact: EnfaFin.
        + move => IH /andP[/andP [H1 H2] H3]. exists None => //.
          apply: enfa_star_cat (IH _) => //. exact: enfa_star_langI.
      }
      { (* <= *)
        case => q. rewrite inE => /eqP-> {q}. exact: enfa_starE.
      }
    Qed.

    Lemma nfa_star_correct:
      nfa_lang nfa_star =i star (nfa_lang A1).
    Proof.
      move => x.
      apply/nfa_ofP/idP => ?;exact/enfa_starP.
    Qed.
    
  End eNFAOps.

End NFA.


(** ** Back to Regular Expressions *)

Canonical Structure regexp_predType (char: eqType) :=
  PredType (@re_lang char).


Section DFAofRE.
  (*
     Goal: DFA -> RE
 
      |-> RE
      |   *
      |   |
      |   v
      |   *
      |  NFA <-> eNFA
      |  ^ *
      |  | |
      |  | |
      |  | *
      |--DFA    
   *)
  
  Variable char: finType.

  Fixpoint re_to_nfa (r: regexp char): nfa char :=
    match r with
    | Void => dfa_to_nfa (dfa_void _)
    | Eps => nfa_eps _
    | Atom a => nfa_char a
    | Star s => nfa_star (re_to_nfa s)
    | Plus s t => nfa_plus (re_to_nfa s) (re_to_nfa t)
    | Conc s t => nfa_conc (re_to_nfa s) (re_to_nfa t)
    end.
  
  Lemma re_to_nfa_correct (r: regexp char):
    nfa_lang (re_to_nfa r) =i r.
  Proof.
    (* By structural induction on regular expressions. *)
    elim: r => [||a|s IHs |s IHs t IHt |s IHs t IHt] w //=.
    - (* 0. Void *)
      by rewrite -dfa_to_nfa_correct inE /dfa_accept inE.
    - (* 1. eps *)
      exact: nfa_eps_correct.
    - (* 2. char *)
      exact: nfa_char_correct.
    - (* 4. star *)
      rewrite nfa_star_correct. exact: star_eq.
    - (* 3. + *)
      by rewrite nfa_plus_correct /plus inE IHs IHt.
    - (* 5. conc *)
      rewrite nfa_conc_correct. exact: conc_eq.
  Qed.

  Definition re_to_dfa : regexp char -> dfa char :=
    @nfa_to_dfa _ \o re_to_nfa.

  (** 
      - The final lemma.
   *)
  Lemma re_to_dfa_correct (r: regexp char):
    dfa_lang (re_to_dfa r) =i r.
  Proof.
    move => w.
    by rewrite -nfa_to_dfa_correct re_to_nfa_correct.
  Qed.


End DFAofRE.


(** ** DFA back to RE 

    - We won't cover this final piece, but it can be done with one
      of many constructions.
 *)

(* Goal: DFA -> RE
 
      |->*RE
      |   |
      |   v
      |  NFA <-> eNFA
      |  ^ |
      |  | v
      |-*DFA

   *)


(** ** Summary

   - We introduces REs and showed that they were equivalent to DFAs via
     NFAs.
 *)
