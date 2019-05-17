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
Lemma rowmxof_linear : linear rowmxof.
Proof. by move=> x v1 v2; apply/rowP=> i; rewrite !mxE linearP. Qed.
Canonical rowmxof_is_linear := Linear rowmxof_linear.

Lemma coord_rowof i v : coord e i v = rowmxof v 0 i.
Proof. by rewrite !mxE. Qed.

Definition vecof (v : 'rV[subvs_of E]_n) : fieldOver E := \sum_i v 0 i *: e`_i.

Lemma vecof_delta i : vecof (delta_mx 0 i) = e`_i.
Proof.
rewrite /vecof (bigD1 i)//= mxE !eqxx scale1r big1 ?addr0// => j neq_ji.
by rewrite mxE (negPf neq_ji) andbF scale0r.
Qed.

Lemma vecof_linear : linear vecof.
Proof.
move=> x v1 v2; rewrite linear_sum -big_split/=.
by apply: eq_bigr => i _/=; rewrite !mxE scalerDl scalerA.
Qed.
Canonical vecof_is_linear := Linear vecof_linear.

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
Definition galmx (M : 'M_n) :=
  gal F (insubd (\1%AF) (linfun (fun u : L => vecof (rowmxof u *m M)))).

Lemma mxofK : cancel mxof galmx.
Admitted.

Lemma galmxK : cancel galmx mxof.
Admitted.

Lemma mxof1 : mxof 1%g = 1%:M.
Proof.
Admitted.

Lemma mxofM g g' : mxof (g * g')%g = (mxof g * mxof g').
Proof.
apply/matrixP=> i j; rewrite !mxE galM ?vecof_in//.
Admitted.

Lemma mxofX g i : mxof (g ^+ i)%g = mxof g ^+ i.
Proof.
Admitted.

Lemma galmx1 : galmx 1%:M = 1%g.
Proof.
Admitted.

Lemma galmxM M M' : galmx (M * M') = (galmx M * galmx M')%g.
Proof. by apply: (can_inj mxofK); rewrite mxofM 3!galmxK. Qed.

Lemma galmxX M i : galmx (M ^+ i) = (galmx M ^+ i)%g.
Proof.
Admitted.

End galmx.
End galmx.
