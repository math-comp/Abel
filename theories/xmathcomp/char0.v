From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* Field extensions in characteristic 0 are always separable *)
Section FieldExtChar0.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (charL : [char L] =i pred0).
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
