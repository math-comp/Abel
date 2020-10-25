From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.Theory.

(* port to mathcomp *)
(* Lemma mem_alg a : a%:A \in E. Proof. by rewrite rpredZ ?mem1v. Qed. *)

(* Lemma scale_Subvs (a : K) (x : L) :  *)
(*    Subvs (mem_alg a) *: (x : fieldOver E) = a *: x. *)
(* Proof. by rewrite -[LHS]scalerAl mul1r. Qed. *)

Section galmx.
Variable (K : fieldType) (L : splittingFieldType K) (E F : {subfield L}).
Hypothesis sub_EF : (E <= F)%VS.

Local Notation n := (\dim_E F).-1.+1.

Variables (e : n.-tuple (fieldOver E)).

Definition galrow (v : fieldOver E) := \row_i coord e i v.
Lemma galrow_is_linear : linear galrow.
Proof. by move=> x v1 v2; apply/rowP=> i; rewrite !mxE linearP. Qed.
Canonical galrow_linear := Linear galrow_is_linear.

Lemma coord_rowof i v : coord e i v = galrow v 0 i.
Proof. by rewrite !mxE. Qed.

Definition galvec (v : 'rV[subvs_of E]_n) : fieldOver E := \sum_i v 0 i *: e`_i.

Lemma galvec_delta i : galvec (delta_mx 0 i) = e`_i.
Proof.
rewrite /galvec (bigD1 i)//= mxE !eqxx scale1r big1 ?addr0// => j neq_ji.
by rewrite mxE (negPf neq_ji) andbF scale0r.
Qed.

Lemma galvec_is_linear : linear galvec.
Proof.
move=> x v1 v2; rewrite linear_sum -big_split/=.
by apply: eq_bigr => i _/=; rewrite !mxE scalerDl scalerA.
Qed.
Canonical galvec_linear := Linear galvec_is_linear.

Variable e_basis : basis_of (aspaceOver E F) e.

Lemma galrowK : {in F, cancel galrow galvec}.
Proof.
move=> v vF; rewrite [v in RHS](coord_basis e_basis) ?memvf//.
  by apply: eq_bigr => i; rewrite !mxE// => _.
by rewrite mem_aspaceOver.
Qed.

Lemma galvecK : cancel galvec galrow.
Proof.
move=> v; apply/rowP=> i; rewrite !(lfunE, mxE).
by rewrite coord_sum_free ?(basis_free e_basis).
Qed.

Lemma galrowE (i : 'I_n) : galrow e`_i = delta_mx 0 i.
Proof.
apply/rowP=> k; rewrite !mxE.
by rewrite eqxx coord_free ?(basis_free e_basis)// eq_sym.
Qed.

Lemma coord_galvec i v : coord e i (galvec v) = v 0 i.
Proof. by rewrite coord_rowof galvecK. Qed.

Lemma galrow_eq0 v : v \in F -> (galrow v == 0) = (v == 0).
Proof. by move=> vF; rewrite -(inj_eq (can_inj galvecK)) galrowK ?linear0. Qed.

Lemma galvec_in v : galvec v \in F.
Proof.
rewrite /galvec -(mem_aspaceOver sub_EF) memv_suml // => i _.
by rewrite memvZ// (basis_mem e_basis)// mem_nth// size_tuple.
Qed.

Lemma galvec_eq0 v : (galvec v == 0) = (v == 0).
Proof.
rewrite -(inj_in_eq (can_in_inj galrowK)) ?galvec_in// ?mem0v//.
by rewrite galvecK linear0.
Qed.

Definition galmx (h : gal_of F) := lin1_mx (galrow \o h \o galvec).

Lemma mul_galmx (h : gal_of F) M : h \in 'Gal(F / E)%g ->
 M *m galmx h = galrow (h (galvec M)).
Proof.
move=> Gh; rewrite /galmx; set g := (X in lin1_mx X).
suff g_is_linear : linear g by rewrite (mul_rV_lin1 (Linear g_is_linear)).
move=> k y z; rewrite /g/= -[RHS]linearP [in LHS]linearP rmorphD rmorphM/=.
by rewrite [h (vsval k)](fixed_gal _ Gh)// subvsP.
Qed.

Lemma galmx1 : galmx 1%g = 1%:M.
Proof. by apply/row_matrixP => i; rewrite !rowE mulmx1 mul_galmx// gal_id galvecK. Qed.

Lemma galmxM : {in 'Gal(F / E)%g &, forall g g',
  galmx (g * g')%g = (galmx g * galmx g')}.
Proof.
move=> g g' gG g'G; apply/row_matrixP => i; rewrite !rowE mulmxA.
by rewrite !mul_galmx ?groupM// galM ?galvec_in// galrowK// memv_gal ?galvec_in.
Qed.

Lemma galmxX g i : g \in 'Gal(F / E)%g -> galmx (g ^+ i)%g = galmx g ^+ i.
Proof.
move=> gG; elim: i => [|i IHi]; first by rewrite galmx1.
by rewrite expgS exprS galmxM ?groupX// IHi.
Qed.

Lemma galvecM v g : g \in 'Gal(F / E)%g -> galvec (v *m galmx g) = g (galvec v).
Proof. by move=> gG; rewrite mul_galmx// galrowK ?memv_gal ?galvec_in. Qed.

End galmx.
