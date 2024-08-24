(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Preliminaries

This file contains a number of auxiliary lemmas that do not mention
any of the representations of regular languages and may thus also be
useful in other contexts *)

(** ** Generic Lemmas not in MathComp *)

(** Logic *)

Notation "P =p Q" := (forall x, P x <-> Q x) (at level 30).

Lemma dec_iff P Q : decidable P -> Q <-> P -> decidable Q.
Proof. firstorder. Qed.

Lemma eqb_iff (b1 b2 : bool) : (b1 <-> b2) <-> (b1 = b2).
Proof. split => [[A B]|->//]. exact/idP/idP. Qed.

Lemma dec_eq (P : Prop) (decP : decidable P) : decP <-> P.
Proof. by case: decP. Qed.

(* equivalence of type inhabitation *)
Variant iffT T1 T2 := IffT of (T1 -> T2) & (T2 -> T1).
Notation "T1 <-T-> T2" := (iffT T1 T2) (at level 30).

Definition iffT_LR T1 T2 : iffT T1 T2 -> T1 -> T2. by case. Qed.
Definition iffT_RL T1 T2 : iffT T1 T2 -> T2 -> T1. by case. Qed.

Hint View for move/ iffT_LR|2 iffT_RL|2.
Hint View for apply/ iffT_LR|2 iffT_RL|2.

(** Arithmetic *)

Lemma size_induction {X : Type} (measure : X -> nat) (p : X ->Prop) :
  ( forall x, ( forall y, measure y < measure x -> p y) -> p x) -> forall x, p x.
Proof.
  move => A x. apply: (A). elim: (measure x) => // n IHn y Hy.
  apply: A => z Hz. apply: IHn. exact: leq_trans Hz Hy.
Qed.

(** Sequences - seq.v *)

Arguments nth T x0 !s !n.

Lemma index_take (T : eqType) (a : T) n (s : seq T) : 
  a \in take n s -> index a (take n s) = index a s.
Proof. move => H. by rewrite -{2}[s](cat_take_drop n) index_cat H. Qed.

(* from mathcomp-1.13 *)
Lemma forall_cons {T : eqType} {P : T -> Prop} {a s} :
  {in a::s, forall x, P x} <-> P a /\ {in s, forall x, P x}.
Proof.
split=> [A|[A B]]; last by move => x /predU1P [-> //|]; apply: B.
by split=> [|b Hb]; apply: A; rewrite !inE ?eqxx ?Hb ?orbT.
Qed.

(* from mathcomp-1.13 *)
Lemma exists_cons {T : eqType} {P : T -> Prop} {a s} :
  (exists2 x, x \in a::s & P x) <-> P a \/ exists2 x, x \in s & P x.
Proof.
split=> [[x /predU1P[->|x_s] Px]|]; [by left| by right; exists x|].
by move=> [?|[x x_s ?]]; [exists a|exists x]; rewrite ?inE ?eqxx ?x_s ?orbT.
Qed.

Lemma orS (b1 b2 : bool) : b1 || b2 -> {b1} + {b2}.
Proof. by case: b1 => /= [_|H]; [left|right]. Qed.

Lemma forall_consT {T : eqType} {a : T} {s} {P : T -> Type} :
  (forall b, b \in a :: s -> P b) <-T-> (P a * (forall b, b \in s -> P b)).
Proof.
  split => [A|[A B] b]. 
  - by split => [|b b_s]; apply: A; rewrite inE ?b_s ?orbT ?eqxx.
  - rewrite inE. case/orS => [/eqP -> //|]. exact: B. 
Qed.

Lemma bigmax_seq_sup (T : eqType) (s:seq T) (P : pred T) F k m :
  k \in s -> P k -> m <= F k -> m <= \max_(i <- s | P i) F i.
Proof. move => A B C. by rewrite (big_rem k) //= B leq_max C. Qed.

Lemma max_mem n0 (s : seq nat) : n0 \in s -> \max_(i <- s) i \in s.
Proof. 
  case: s => // a s _. rewrite big_cons big_seq.
  elim/big_ind : _ => [|n m|n A]; first exact: mem_head.
  - rewrite -{5}[a]maxnn maxnACA => ? ?. rewrite {1}/maxn. by case: ifP.
  - rewrite /maxn. case: ifP; by rewrite ?mem_head // inE A orbT.
Qed.

(* reasoning about singletons *)
Lemma seq1P (T : eqType) (x y : T) : reflect (x = y) (x \in [:: y]).
Proof. rewrite inE. exact: eqP. Qed.

Lemma sub1P (T : eqType) x (p : pred T) : reflect {subset [:: x] <= p} (x \in p).
Proof. 
apply: (iffP idP) => [A y|]; by [rewrite inE => /eqP->|apply; exact: mem_head]. 
Qed.

(** Finite Types - fintype.v *)

Lemma sub_forall (T: finType) (p q : pred T) :
  subpred p q -> [forall x : T, p x] -> [forall x : T, q x].
Proof. move => sub /forallP H. apply/forallP => x. exact: sub. Qed.

Lemma sub_exists (T : finType) (P1 P2 : pred T) :
  subpred P1 P2 -> [exists x, P1 x] -> [exists x, P2 x].
Proof. move => H. case/existsP => x /H ?. apply/existsP. by exists x. Qed.

Lemma card_leq_inj (T T' : finType) (f : T -> T') : injective f -> #|T| <= #|T'|.
Proof. move => inj_f. by rewrite -(card_imset predT inj_f) max_card. Qed.

Lemma bij_card {X Y : finType} (f : X->Y): bijective f -> #|X| = #|Y|.
Proof.
  case => g /can_inj Hf /can_inj Hg. apply/eqP.
  by rewrite eqn_leq (card_leq_inj Hf) (card_leq_inj Hg).
Qed.

Lemma cardT_eq (T : finType) (p : pred T) : #|{: { x | p x}}| = #|T| -> p =1 predT.
Proof.
  (* backwards compatible fix for mathcomp PR #626 - mathcomp-1.12.0 *)
  move=> eq_pT; have [|g g1 g2 x] := @inj_card_bij [finType of (sig p)] T _ val_inj.
    by rewrite eq_pT.
  rewrite -(g2 x); exact: valP.
Qed.

(** Finite Ordinals *)

Lemma inord_max n : ord_max = inord n :> 'I_n.+1.
Proof. by rewrite -[ord_max]inord_val. Qed.

Lemma inord0 n : ord0 = inord 0 :> 'I_n.+1.
Proof. by rewrite -[ord0]inord_val. Qed.

Definition ord1 {n} := (@Ordinal (n.+2) 1 (erefl _)).

Lemma inord1 n : ord1 = inord 1 :> 'I_n.+2. 
Proof. apply: ord_inj => /=. by rewrite inordK. Qed.

(** Finite Sets - finset.v *)

Lemma card_set (T:finType) : #|{set T}| = 2^#|T|.
Proof. rewrite -!cardsT -powersetT. exact: card_powerset. Qed.

(** Miscellaneous *)

Local Open Scope quotient_scope.
Lemma epiK {T:choiceType} (e : equiv_rel T) x : e (repr (\pi_{eq_quot e} x)) x.
Proof. by rewrite -eqmodE reprK. Qed.

Lemma set_enum (T : finType) : [set x in enum T] = [set: T].
Proof. apply/setP => x. by rewrite !inE  mem_enum. Qed.

Lemma find_minn_bound (p : pred nat) m :
  {n | [/\ n < m, p n & forall i, i < n -> ~~ p i]} + {(forall i, i < m -> ~~ p i)}.
Proof.
  case: (boolP [exists n : 'I_m, p n]) => C ; [left|right].
  - have/find_ex_minn: exists n, (n < m) && p n.
      case/existsP : C => [[n Hn pn]] /=. exists n. by rewrite Hn.
    case => n /andP [lt_m pn] min_n. exists n. split => // i Hi.
    apply: contraTN (Hi) => pi. rewrite -leqNgt min_n // pi andbT.
    exact: ltn_trans lt_m.
  - move => i lt_m. move: C. by rewrite negb_exists => /forallP /(_ (Ordinal lt_m)).
Qed.

(** Relations *)

Section Functional.
  Variables (T T' : finType) (e : rel T) (e' : rel T') (f : T -> T').

  Definition terminal x := forall y, e x y = false.
  Definition functional := forall x y z, e x y -> e x z -> y = z.

  Lemma term_uniq x y z : functional ->
    terminal y -> terminal z -> connect e x y -> connect e x z -> y = z.
  Proof. 
    move => fun_e Ty Tz /connectP [p] p1 p2 /connectP [q]. 
    elim: p q x p1 p2 => [|a p IH] [|b q] x /=; first congruence.
    - move => _ <-. by rewrite Ty.
    - case/andP => xa _ _ _ H. by rewrite -H Tz in xa.
    - case/andP => xa p1 p2 /andP [xb] q1 q2. 
      move: (fun_e _ _ _ xa xb) => ?; subst b. exact: IH q2.
  Qed.

  Hypothesis f_inj : injective f.
  Hypothesis f_eq : forall x y, e x y = e' (f x) (f y).
  Hypothesis f_inv: forall x z, e' (f x) z -> exists y, z = f y. 

  Lemma connect_transfer x y : connect e x y = connect e' (f x) (f y).
  Proof using f_eq f_inj f_inv.
    apply/idP/idP.
    - case/connectP => s.
      elim: s x => //= [x _ -> |z s IH x]; first exact: connect0.
      case/andP => xz pth Hy. rewrite f_eq in xz.
      apply: connect_trans (connect1 xz) _. exact: IH.
    - case/connectP => s.
      elim: s x => //= [x _ /f_inj -> |z s IH x]; first exact: connect0.
      case/andP => xz pth Hy. case: (f_inv xz) => z' ?; subst. 
      rewrite -f_eq in xz. apply: connect_trans (connect1 xz) _. exact: IH.
  Qed.
End Functional.

Lemma functional_sub (T : finType) (e1 e2 : rel T) : 
  functional e2 -> subrel e1 e2 -> functional e1.
Proof. move => f_e2 sub x y z /sub E1 /sub E2. exact: f_e2 E1 E2. Qed.

(** ** Inverting surjective functions *)

Definition surjective aT {rT : eqType} (f : aT -> rT) := forall y, exists x, f x == y.

Lemma surjectiveE (rT aT : finType) (f : aT -> rT) : surjective f -> #|codom f| = #|rT|.
Proof.
  move => H. apply: eq_card => x. rewrite inE. apply/codomP.
  move: (H x) => [y /eqP]. eauto.
Qed.

Lemma surj_card_bij (T T' : finType) (f : T -> T') :
  surjective f -> #|T| = #|T'| -> bijective f.
Proof.
  move => S E. apply: inj_card_bij; last by rewrite E. 
  apply/injectiveP; apply/card_uniqP. rewrite size_map -cardT E. exact: surjectiveE.
Qed.

(* We define a general inverse of surjective functions from choiceType -> eqType.
   This function gives a canonical representative, thus the name "cr". *)
Definition cr {X : choiceType} {Y : eqType} {f : X -> Y} (Sf : surjective f) y : X :=
  xchoose (Sf y).

Lemma crK {X : choiceType} {Y : eqType} {f : X->Y} {Sf : surjective f} x: f (cr Sf x) = x.
Proof. by rewrite (eqP (xchooseP (Sf x))). Qed.





(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
From mathcomp Require Import all_ssreflect.
(* From RegLang Require Import misc. *)

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Languages in Type Theory 

This file mainly defines aliases for (decidable) languages. It also
shows that decidable languages are closed under the primitive regular
operations (e.g., concatenation and interation). This will allow us to
assign decidable languages to regular expressions. We allow for
infinite (but discrete) alphabets. *)
 
(** The definitions of [conc] and [star] as well as the proofs of
[starP] and [concP] are taken from from regexp.v in:

Thierry Coquand, Vincent Siles, A Decision Procedure for Regular
Expression Equivalence in Type Theory (DOI:
10.1007/978-3-642-25379-9_11). See also:
https://github.com/coq-community/regexp-Brzozowski *)

Section Basics.
  Variables char : eqType.
  Definition word := seq char.
  Definition lang := word -> Prop.
  Definition dlang := pred word.

  Canonical Structure word_eqType := [eqType of word].
  Identity Coercion pred_of_dlang : dlang >-> pred.
End Basics. 

Section HomDef.
  Variables (char char' : finType) (h : seq char -> seq char').

  Definition image (L : word char -> Prop) v := exists w, L w /\ h w = v.

  Lemma image_ext L1 L2  w :
    (forall v, L1 v <-> L2 v) -> (image L1 w <-> image L2 w).
  Proof. by move => H; split; move => [v] [] /H; exists v. Qed.

  Definition preimage (L : word char' -> Prop) v :=  L (h v).

  Definition homomorphism := forall w1 w2, h (w1 ++ w2) = h w1 ++ h w2.
  Hypothesis h_hom : homomorphism.
  Local Set Default Proof Using "h_hom".

  Lemma h0 : h [::] = [::].
  Proof.
    apply: size0nil. apply/eqP.
    by rewrite -(eqn_add2r (size (h [::]))) -size_cat -h_hom /=.
  Qed.

  Lemma h_seq w : h w = flatten [seq h [:: a] | a <- w].
  Proof. elim: w => [|a w IHw] /= ; by rewrite ?h0 // -cat1s h_hom IHw. Qed.

  Lemma h_flatten vv : h (flatten vv) = flatten (map h vv).
  Proof.
    elim: vv => //= [|v vv IHvv]; first exact: h0.
    by rewrite h_hom IHvv.
  Qed.

End HomDef.

(** ** Closure Properties for Decidable Languages *)

Section DecidableLanguages.

Variable char : eqType.
Implicit Types (x y z : char) (u v w : word char) (l : dlang char).

Definition void : dlang char := pred0.

Definition eps : dlang char := pred1 [::].

Definition dot : dlang char := [pred w | size w == 1].

Definition atom x : dlang char := pred1 [:: x].

Definition compl l : dlang char := predC l.

Definition prod l1 l2 : dlang char := [pred w in l1 | w \in l2].

Definition plus l1 l2 : dlang char := [pred w | (w \in l1) || (w \in l2)].

Definition residual x l : dlang char := [pred w | x :: w \in l].

(** For the concatenation of two decidable languages, we use finite
types. Note that we need to use [L1] and [L2] applicatively in order
for the termination check for [star] to succeed. *)

Definition conc l1 l2 : dlang char :=
  fun v => [exists i : 'I_(size v).+1, l1 (take i v) && l2 (drop i v)].

(** The iteration (Kleene star) operator is defined using resisdual
languages. Termination of star relies in the fact that conc applies
its second argument only to [drop i v] which is "structurally less
than or equal" to [v] *)

Definition star l : dlang char :=
  fix star v := if v is x :: v' then conc (residual x l) star v' else true.

Lemma in_dot u : (u \in dot) = (size u == 1).
Proof. by []. Qed.

Lemma in_compl l v : (v \in compl l) = (v \notin l).
Proof. by []. Qed.

Lemma compl_invol l : compl (compl l) =i l.
Proof. by move => w; rewrite inE /= /compl /= negbK. Qed.

Lemma in_prod l1 l2 v : (v \in prod l1 l2) = (v \in l1) && (v \in l2).
Proof. by rewrite inE. Qed.

Lemma plusP r s w :
  reflect (w \in r \/ w \in s) (w \in plus r s).
Proof. rewrite !inE. exact: orP. Qed.

Lemma in_residual x l u : (u \in residual x l) = (x :: u \in l).
Proof. by []. Qed.

Lemma concP {l1 l2 w} :
  reflect (exists w1 w2, w = w1 ++ w2 /\ w1 \in l1 /\ w2 \in l2) (w \in conc l1 l2).
Proof. apply: (iffP existsP) => [[n] /andP [H1 H2] | [w1] [w2] [e [H1 H2]]].
  - exists (take n w). exists (drop n w). by rewrite cat_take_drop -topredE.
  - have lt_w1: size w1 < (size w).+1 by rewrite e size_cat ltnS leq_addr.
    exists (Ordinal lt_w1); subst.
    rewrite take_size_cat // drop_size_cat //. exact/andP.
Qed.

Lemma conc_cat w1 w2 l1 l2 : w1 \in l1 -> w2 \in l2 -> w1 ++ w2 \in conc l1 l2.
Proof. move => H1 H2. apply/concP. exists w1. by exists w2. Qed.

Lemma conc_eq l1 l2 l3 l4 :
  l1 =i l2 -> l3 =i l4 -> conc l1 l3 =i conc l2 l4.
Proof.
  move => H1 H2 w. apply: eq_existsb => n. 
  by rewrite (_ : l1 =1 l2) // (_ : l3 =1 l4).
Qed.

Lemma starP : forall {l v},
  reflect (exists2 vv, all [predD l & eps] vv & v = flatten vv) (v \in star l).
Proof.
move=> l v;
  elim: {v}_.+1 {-2}v (ltnSn (size v)) => // n IHn [|x v] /= le_v_n.
  by left; exists [::].
apply: (iffP concP) => [[u] [v'] [def_v [Lxu starLv']] | [[|[|y u] vv] //=]].
  case/IHn: starLv' => [|vv lvv def_v'].
    by rewrite -ltnS (leq_trans _ le_v_n) // def_v size_cat !ltnS leq_addl.
  by exists ((x :: u) :: vv); [exact/andP | rewrite def_v def_v'].
case/andP=> lyu lvv [def_x def_v]; exists u. exists (flatten vv).
subst. split => //; split => //. apply/IHn; last by exists vv.
by rewrite -ltnS (leq_trans _ le_v_n) // size_cat !ltnS leq_addl.
Qed.

Lemma star_cat w1 w2 l : w1 \in l -> w2 \in (star l) -> w1 ++ w2 \in star l.
Proof.
  case: w1 => [|a w1] // H1 /starP [vv Ha Hf]. apply/starP.
  by exists ((a::w1) :: vv); rewrite ?Hf //= H1.
Qed.

Lemma starI l vv :
  (forall v, v \in vv -> v \in l) -> flatten vv \in star l.
Proof.
  elim: vv => /= [//| v vv IHvv /forall_cons [H1 H2]].
  exact: star_cat _ (IHvv _).
Qed.

Lemma star_eq l1 l2 : l1 =i l2 -> star l1 =i star l2.
Proof.
  move => H1 w. apply/starP/starP; move => [] vv H3 H4; exists vv => //;
  erewrite eq_all; try eexact H3; move => x /=; by rewrite ?H1 // -?H1.
Qed.

Lemma star_id l : star (star l) =i star l.
Proof.
  move => u. rewrite -!topredE /=. apply/starP/starP => [[vs h1 h2]|].
    elim: vs u h1 h2 => [|hd tl Ih] u h1 h2; first by exists [::].
    move: h1 => /= h1. case/andP: h1; case/andP => hhd1 hhd2 htl.
    case: (Ih (flatten tl)) => //= [xs x1 x2].
    case/starP: hhd2 => hds j1 j2.
    exists (hds ++ xs); first by rewrite all_cat; apply/andP.
    by rewrite h2 j2 /= x2 flatten_cat.
  move => [hs h1 h2]. exists hs => //. apply/allP => x x1.
  move/allP: h1 => h1. case/andP: (h1 x x1) => /= h3 h4.
  rewrite h3 /=. apply/starP. exists [:: x] => /=; first by rewrite h3 h4.
  by rewrite cats0.
Qed.

End DecidableLanguages.


(* Author: Christian Doczkal  *)
(* Distributed under the terms of CeCILL-B. *)

From Coq Require Import Basics Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Setoid Rewriting with Ssreflec's boolean inequalities.                      *)
(** Solution suggested by Georges Gonthier (ssreflect mailinglist @ 18.12.2016) *)

(** Preorder and Instances for bool *)

Inductive leb a b := Leb of (a ==> b).

Lemma leb_eq a b : leb a b <-> (a -> b). 
Proof. move: a b => [|] [|]; firstorder. Qed.

Instance: PreOrder leb.
Proof. split => [[|]|[|][|][|][?][?]]; try exact: Leb. Qed.

Instance: Proper (leb ==> leb ==> leb) andb.
Proof. move => [|] [|] [A] c d [B]; exact: Leb. Qed.

Instance: Proper (leb ==> leb ==> leb) orb.
Proof. move => [|] [|] [A] [|] d [B]; exact: Leb. Qed.

Instance: Proper (leb ==> impl) is_true.
Proof. move => a b []. exact: implyP. Qed.

(** Instances for le  *)

Instance: Proper (le --> le ++> leb) leq. 
Proof. move => n m /leP ? n' m' /leP ?. apply/leb_eq => ?. eauto using leq_trans. Qed.

Instance: Proper (le ==> le ==> le) addn. 
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_add. Qed.

Instance: Proper (le ==> le ==> le) muln. 
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_mul. Qed.

Instance: Proper (le ++> le --> le) subn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_sub. Qed.

Instance: Proper (le ==> le) S.
Proof. move => n m /leP ?. apply/leP. by rewrite ltnS. Qed.

Instance: RewriteRelation le := Build_RewriteRelation _.

(** Wrapper Lemma to trigger setoid rewrite *)
Definition leqRW m n  : m <= n -> le m n := leP.

(** Testing *)

Lemma T1 : forall x y, x <= y -> x + 1 <= y + 1.
Proof. move => x y h. by rewrite (leqRW h). Qed.

Lemma T2 : forall x y, x <= y -> (x + 1 <= y + 1) && true.
Proof. move => x y h. by rewrite (leqRW h) andbT. Qed.
