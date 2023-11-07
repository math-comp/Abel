From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Local Notation has_char0 L := ([char L] =i pred0).

Section Char0MorphismsIdomain.

Variable (R : idomainType).
Hypothesis charR0 : has_char0 R.

Implicit Type z : int.

Lemma char0_intr_eq0 (z : int) : ((z%:~R : R) == 0) = (z == 0).
Proof.
suff hPos (m : nat) : (m%:~R == 0 :> R) = (Posz m == 0).
  by case: z => [m | m] => //; rewrite NegzE rmorphN /= !oppr_eq0.
by rewrite [m%:~R]/(m%:R); move/charf0P: (charR0)->.
Qed.

Lemma char0_intr_inj : injective (fun i => i%:~R : R).
Proof.
move=> i j /eqP; rewrite -subr_eq0 -rmorphB /= char0_intr_eq0 subr_eq0.
by move/eqP.
Qed.

End Char0MorphismsIdomain.

Definition char0_ratr (F : fieldType) (charF0 : has_char0 F) := (@ratr F).

Lemma char0_ratrE (F : fieldType) (charF0 : has_char0 F) :
  char0_ratr charF0 = ratr.
Proof. by []. Qed.

Section Char0MorphismsField.

Variable (F : fieldType).
Hypothesis charF0 : has_char0 F.

Local Notation ratrF := (char0_ratr charF0).

Fact char0_ratr_is_additive : additive ratrF.
Proof.
rewrite /char0_ratr.
have injZtoQ: @injective rat int intr by apply: intr_inj.
have nz_den x: (denq x)%:~R != 0 :> F by rewrite char0_intr_eq0 // denq_eq0.
rewrite /ratr ?divr1 // => x y.
apply: (canLR (mulfK (nz_den _))); apply: (mulIf (nz_den x)).
rewrite mulrAC mulrBl divfK ?nz_den // mulrAC -!rmorphM /=.
apply: (mulIf (nz_den y)); rewrite mulrAC mulrBl divfK ?nz_den //.
rewrite -!(rmorphM, rmorphB); congr _%:~R; apply: injZtoQ.
rewrite !(rmorphM, rmorphB) [_ - _]lock /= -lock.
by rewrite !numqE (mulrAC y) -!mulrBl -mulrA mulrAC !mulrA.
Qed.

Fact char0_ratr_is_multiplicative : multiplicative ratrF.
Proof.
rewrite /char0_ratr.
have injZtoQ: @injective rat int intr by apply: intr_inj.
have nz_den x: (denq x)%:~R != 0 :> F by rewrite char0_intr_eq0 // denq_eq0.
split; rewrite /ratr ?divr1 // => x y.
rewrite mulrC mulrAC; apply: canLR (mulKf (nz_den _)) _; rewrite !mulrA.
do 2!apply: canRL (mulfK (nz_den _)) _; rewrite -!rmorphM; congr _%:~R.
apply: injZtoQ; rewrite !rmorphM [x * y]lock /= !numqE -lock.
by rewrite -!mulrA mulrA mulrCA -!mulrA (mulrCA y).
Qed.

HB.instance Definition _ := GRing.isAdditive.Build rat F ratrF
  char0_ratr_is_additive.
HB.instance Definition _ := GRing.isMultiplicative.Build rat F ratrF
  char0_ratr_is_multiplicative.

End Char0MorphismsField.

Section NumberFieldsProps.

Variable (L : fieldExtType rat).

Lemma char_ext : has_char0 L. (* this works more generally for `lalgType rat` *)
Proof. by move=> x; rewrite char_lalg Num.Theory.char_num. Qed.
Hint Resolve char_ext : core.

Lemma rat_extratr0 : ratr 0 = 0 :> L.
(* watch out: no // to discharge charL as it is in Prop :) *)
Proof. by rewrite -char0_ratrE raddf0. Qed.

Notation ratrL := (char0_ratr char_ext).

Lemma char0_ratrN : {morph ratrL : x / - x}. Proof. exact: raddfN. Qed.
Lemma char0_ratrD : {morph ratrL : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma char0_ratrB : {morph ratrL : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma char0_ratrMn n : {morph ratrL : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma char0_ratrMNn n : {morph ratrL : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma char0_ratr_sum I r (P : pred I) E :
  ratrL (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) ratrL (E i).
Proof. exact: raddf_sum. Qed.
 Lemma char0_ratrMsign n : {morph ratrL : x / (- 1) ^+ n * x}.
Proof. exact: raddfMsign. Qed.

Lemma char0_ratr1 : ratrL 1 = 1. Proof. by exact: rmorph1. Qed.
Lemma char0_ratrM : {morph ratrL : x y  / x * y}. Proof. by exact: rmorphM. Qed.

Lemma char0_ratr_prod I r (P : pred I) E :
  ratrL (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) ratrL (E i).
Proof. exact: rmorph_prod. Qed.

Lemma char0_ratrX n : {morph ratrL : x / x ^+ n}.
Proof. exact: rmorphX.  Qed.

Lemma char0_nat n : ratrL n%:R = n%:R. Proof. exact: ratr_nat. Qed.

Lemma char0_ratrN1 : ratrL (- 1) = (- 1). Proof. exact: rmorphN1. Qed.

Lemma char0_ratr_sign n : ratrL ((- 1) ^+ n) = (- 1) ^+ n.
Proof. by exact: rmorph_sign. Qed.

Lemma char0_ratr_inj : injective ratrL.
Proof.
suff inj0 z : ratrL z = 0 -> z = 0.
  move=> x y /eqP; rewrite -subr_eq0 -char0_ratrB => /eqP /inj0 /eqP.
  by rewrite subr_eq0 => /eqP.
rewrite /ratrL /ratr; move/eqP; rewrite mulf_eq0 invr_eq0 orbC.
have /negPf-> /= : (denq z)%:~R != 0 :> L by rewrite char0_intr_eq0 // denq_eq0.
by rewrite char0_intr_eq0 // numq_eq0 => /eqP.
Qed.

Lemma char0_rmorph_int z : ratrL z%:~R =  z%:~R. Proof. exact: rmorph_int. Qed.

(* Are these two necessary? *)
Lemma char0_ratr_eq_nat x n : (ratrL x == n%:R) = (x == n%:R).
Proof. apply: rmorph_eq_nat; exact: char0_ratr_inj. Qed.

Lemma char0_ratr_eq1 x : (ratrL x == 1) = (x == 1).
Proof. exact: char0_ratr_eq_nat 1%N. Qed.

End NumberFieldsProps.


(* Field extensions in characteristic 0 are always separable *)
Section FieldExtChar0.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (charL : has_char0 L).
Implicit Types (E F : {subfield L}) (p : {poly L}) (x : L).

(** Ok **)
Lemma root_make_separable p x : root p x = root (p %/ gcdp p p^`()) x.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite div0p root0.
have := dvdp_gcdl p p^`(); rewrite dvdp_eq => /eqP p_eq_pDgMg.
apply/idP/idP => [rpx|]; last first.
  move=> dx_eq0; rewrite p_eq_pDgMg.
  by rewrite /root hornerM mulf_eq0 (eqP dx_eq0) eqxx.
have [[|m] [q]] := multiplicity_XsubC p x; rewrite p_neq0/= => rNqx p_eq.
  by rewrite p_eq mulr1 (negPf rNqx) in rpx.
have q_neq0 : q != 0; first by apply: contra_eq_neq p_eq => ->; rewrite mul0r.
rewrite p_eq; set f := ('X - _).
have f_neq0 : f != 0 by rewrite polyXsubC_eq0.
rewrite -dvdp_XsubCl derivM deriv_exp/= derivXsubC mul1r.
rewrite -mulr_natl exprS !mulrA -mulrDl.
set r := (_ * f + _)%R.
have Nrx : ~~ root r x.
  rewrite /root !hornerE subrr mulr0 add0r mulf_neq0//.
  have -> : m.+1%:R = m.+1%:R%:P :> {poly L} by rewrite !raddfMn.
  rewrite hornerC natf_neq0/= (eq_pnat _ (eq_negn charL))/=.
  by apply/andP; split => //; apply/allP.
rewrite (eqp_dvdr _ (eqp_divr _ (gcdp_mul2r _ _ _))).
rewrite divp_pmul2r//; last 2 first.
- by rewrite ?expf_neq0 ?polyXsubC_eq0.
- by rewrite ?gcdp_eq0 negb_and ?mulf_neq0.
rewrite mulrC -divp_mulA ?dvdp_mulr//.
have := dvdp_gcdl (f * q) r; rewrite Gauss_dvdpr//.
by rewrite coprimep_XsubC root_gcd (negPf Nrx) andbF.
Qed.

Lemma char0_minPoly_separable x E : separable_poly (minPoly E x).
Proof.
have pE := minPolyOver E x; set p := minPoly E x.
suff /eqp_separable-> : p %= p %/ gcdp p p^`().
  by rewrite make_separable ?monic_neq0 ?monic_minPoly.
rewrite /eqp divp_dvd ?dvdp_gcdl// andbT.
rewrite minPoly_dvdp ?divp_polyOver ?gcdp_polyOver ?polyOver_deriv//.
by rewrite -root_make_separable// root_minPoly.
Qed.

Lemma char0_separable_element x E : separable_element E x.
Proof. exact: char0_minPoly_separable. Qed.

Lemma char0_separable E F : separable E F.
Proof. by apply/separableP => y _; apply: char0_separable_element. Qed.

Lemma char0_galois E F : (E <= F)%VS -> normalField E F -> galois E F.
Proof. by move=> sEF nEF; apply/and3P; split=> //; apply: char0_separable. Qed.

End FieldExtChar0.
