From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.Theory.

Module galmx.
Section galmx.
Variable (K : fieldType) (L : splittingFieldType K) (E F : {subfield L}).
Hypothesis sub_EF : (E <= F)%VS.

Local Notation n := (\dim_E F).-1.+1.

Variables (e : n.-tuple (fieldOver E)).

Definition rowmxof (v : fieldOver E) := \row_i coord e i v.
Lemma rowmxof_is_linear : linear rowmxof.
Proof. by move=> x v1 v2; apply/rowP=> i; rewrite !mxE linearP. Qed.
Canonical rowmxof_linear := Linear rowmxof_is_linear.

Lemma coord_rowof i v : coord e i v = rowmxof v 0 i.
Proof. by rewrite !mxE. Qed.

Definition vecof (v : 'rV[subvs_of E]_n) : fieldOver E := \sum_i v 0 i *: e`_i.

Lemma vecof_delta i : vecof (delta_mx 0 i) = e`_i.
Proof.
rewrite /vecof (bigD1 i)//= mxE !eqxx scale1r big1 ?addr0// => j neq_ji.
by rewrite mxE (negPf neq_ji) andbF scale0r.
Qed.

Lemma vecof_is_linear : linear vecof.
Proof.
move=> x v1 v2; rewrite linear_sum -big_split/=.
by apply: eq_bigr => i _/=; rewrite !mxE scalerDl scalerA.
Qed.
Canonical vecof_linear := Linear vecof_is_linear.

Variable e_basis : basis_of (aspaceOver E F) e.

Lemma rowmxofK : {in F, cancel rowmxof vecof}.
Proof.
move=> v vF; rewrite [v in RHS](coord_basis e_basis) ?memvf//.
  by apply: eq_bigr => i; rewrite !mxE// => _.
by rewrite mem_aspaceOver.
Qed.

Lemma vecofK : cancel vecof rowmxof.
Proof.
move=> v; apply/rowP=> i; rewrite !(lfunE, mxE).
by rewrite coord_sum_free ?(basis_free e_basis).
Qed.

Lemma rowmxofE (i : 'I_n) : rowmxof e`_i = delta_mx 0 i.
Proof.
apply/rowP=> k; rewrite !mxE.
by rewrite eqxx coord_free ?(basis_free e_basis)// eq_sym.
Qed.

Lemma coord_vecof i v : coord e i (vecof v) = v 0 i.
Proof. by rewrite coord_rowof vecofK. Qed.

Lemma rowmxof_eq0 v : v \in F -> (rowmxof v == 0) = (v == 0).
Proof. by move=> vF; rewrite -(inj_eq (can_inj vecofK)) rowmxofK ?linear0. Qed.

Lemma vecof_in v : vecof v \in F.
Proof.
rewrite /vecof -(mem_aspaceOver sub_EF) memv_suml // => i _.
by rewrite memvZ// (basis_mem e_basis)// mem_nth// size_tuple.
Qed.

Lemma vecof_eq0 v : (vecof v == 0) = (v == 0).
Proof.
rewrite -(inj_in_eq (can_in_inj rowmxofK)) ?vecof_in// ?mem0v//.
by rewrite vecofK linear0.
Qed.

Definition mxof (h : gal_of F) := lin1_mx (rowmxof \o h \o vecof).

Lemma mul_mxof (h : gal_of F) M : h \in 'Gal(F / E)%g -> M *m mxof h = rowmxof (h (vecof M)).
Proof.
move=> Gh; rewrite /mxof; set g := (X in lin1_mx X).
suff g_is_linear : linear g by rewrite (mul_rV_lin1 (Linear g_is_linear)).
move=> k y z; rewrite /g/= -[RHS]linearP [in LHS]linearP rmorphD rmorphM/=.
by rewrite [h (vsval k)](fixed_gal _ Gh)// subvsP.
Qed.

(* rename and port to mathcomp *)
(* Lemma aE a : a%:A \in E. Proof. by rewrite rpredZ ?mem1v. Qed. *)

(* Lemma SubvsZ (a : K) (x : L) :  Subvs (aE a) *: (x : fieldOver E) = a *: x. *)
(* Proof. by rewrite -[LHS]scalerAl mul1r. Qed. *)

Lemma mxof1 : mxof 1%g = 1%:M.
Proof. by apply/row_matrixP => i; rewrite !rowE mulmx1 mul_mxof// gal_id vecofK. Qed.

Lemma mxofM : {in 'Gal(F / E)%g &, forall g g', mxof (g * g')%g = (mxof g * mxof g')}.
Proof.
move=> g g' gG g'G; apply/row_matrixP => i; rewrite !rowE mulmxA.
by rewrite !mul_mxof ?groupM// galM ?vecof_in// rowmxofK// memv_gal ?vecof_in.
Qed.

Lemma mxofX g i : g \in 'Gal(F / E)%g -> mxof (g ^+ i)%g = mxof g ^+ i.
Proof.
move=> gG; elim: i => [|i IHi]; first by rewrite mxof1.
by rewrite expgS exprS mxofM ?groupX// IHi.
Qed.

Lemma vecofM v g : g \in 'Gal(F / E)%g -> vecof (v *m mxof g) = g (vecof v).
Proof. by move=> gG; rewrite mul_mxof// rowmxofK ?memv_gal ?vecof_in. Qed.

End galmx.
End galmx.
