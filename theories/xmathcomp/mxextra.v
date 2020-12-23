From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.Theory.

Lemma mulmxP (K : fieldType) (m n : nat) (A B : 'M[K]_(m, n)) :
  reflect (forall u : 'rV__, u *m A = u *m B) (A == B).
Proof.
apply: (iffP eqP) => [-> //|eqAB].
apply: (@row_full_inj _ _ _ _ 1%:M); first by rewrite row_full_unit unitmx1.
by apply/row_matrixP => i; rewrite !row_mul eqAB.
Qed.

Section lfunP.
Variable (F : fieldType).
Context {uT vT : vectType F}.
Local Notation m := (\dim {:uT}).
Local Notation n := (\dim {:vT}).

Lemma span_lfunP (U : seq uT) (phi psi : 'Hom(uT,vT)) :
  {in <<U>>%VS, phi =1 psi} <-> {in U, phi =1 psi}.
Proof.
split=> eq_phi_psi u uU; first by rewrite eq_phi_psi ?memv_span.
rewrite [u](@coord_span _ _ _ (in_tuple U))// !linear_sum/=.
by apply: eq_bigr=> i _; rewrite !linearZ/= eq_phi_psi// ?mem_nth.
Qed.

Lemma fullv_lfunP (U : seq uT) (phi psi : 'Hom(uT,vT)) : <<U>>%VS = fullv ->
  phi = psi <-> {in U, phi =1 psi}.
Proof.
by move=> Uf; split=> [->//|/span_lfunP]; rewrite Uf=> /(_ _ (memvf _))-/lfunP.
Qed.
End lfunP.

Module passmx.
Section passmx.
Variable (F : fieldType).

Section vecmx.
Context {vT : vectType F}.
Local Notation n := (\dim {:vT}).

Variables (e : n.-tuple vT).

Definition rowmxof (v : vT) := \row_i coord e i v.
Lemma rowmxof_linear : linear rowmxof.
Proof. by move=> x v1 v2; apply/rowP=> i; rewrite !mxE linearP. Qed.
Canonical rowmxof_is_linear := Linear rowmxof_linear.

Lemma coord_rowof i v : coord e i v = rowmxof v 0 i.
Proof. by rewrite !mxE. Qed.

Definition vecof (v : 'rV_n) := \sum_i v 0 i *: e`_i.

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

Variable e_basis : basis_of {:vT} e.

Lemma rowmxofK : cancel rowmxof vecof.
Proof.
move=> v; rewrite [v in RHS](coord_basis e_basis) ?memvf//.
by apply: eq_bigr => i; rewrite !mxE.
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

Lemma rowmxof_eq0 v : (rowmxof v == 0) = (v == 0).
Proof. by rewrite -(inj_eq (can_inj vecofK)) rowmxofK linear0. Qed.

Lemma vecof_eq0 v : (vecof v == 0) = (v == 0).
Proof. by rewrite -(inj_eq (can_inj rowmxofK)) vecofK linear0. Qed.

End vecmx.

Section hommx.
Context {uT vT : vectType F}.
Local Notation m := (\dim {:uT}).
Local Notation n := (\dim {:vT}).

Variables (e : m.-tuple uT) (f : n.-tuple vT).

Definition mxof (h : 'Hom(uT, vT)) := lin1_mx (rowmxof f \o h \o vecof e).

Lemma mxof_linear : linear mxof.
Proof.
move=> x h1 h2; apply/matrixP=> i j; do !rewrite ?lfunE/= ?mxE.
by rewrite linearP.
Qed.
Canonical mxof_is_linear := Linear mxof_linear.

Definition funmx (M : 'M[F]_(m, n)) u := vecof f (rowmxof e u *m M).

Lemma funmx_is_linear M : linear (funmx M).
Proof.
by rewrite /funmx => x u v; rewrite linearP mulmxDl -scalemxAl linearP.
Qed.
Canonical funmx_linear M := Linear (funmx_is_linear M).

Definition hommx M : 'Hom(uT, vT) := linfun (funmx M).

Lemma hommx_linear : linear hommx.
Proof.
rewrite /hommx; move=> x A B; apply/lfunP=> u; do !rewrite lfunE/=.
by rewrite /funmx mulmxDr -scalemxAr linearP.
Qed.
Canonical hommx_is_linear := Linear hommx_linear.

Hypothesis e_basis: basis_of {:uT} e.
Hypothesis f_basis: basis_of {:vT} f.

Lemma mxofK : cancel mxof hommx.
Proof.
by move=> h; apply/lfunP=> u; rewrite lfunE/= /funmx mul_rV_lin1/= !rowmxofK.
Qed.

Lemma hommxK : cancel hommx mxof.
Proof.
move=> M; apply/matrixP => i j; rewrite !mxE/= lfunE/=.
by rewrite /funmx vecofK// -rowE coord_vecof// mxE.
Qed.

Lemma mul_mxof phi u : u *m mxof phi = rowmxof f (phi (vecof e u)).
Proof. by rewrite mul_rV_lin1/=. Qed.

Lemma hommxE M u : hommx M u = vecof f (rowmxof e u *m M).
Proof. by rewrite -[M in RHS]hommxK mul_mxof !rowmxofK//. Qed.

Lemma rowmxof_mul M u : rowmxof e u *m M = rowmxof f (hommx M u).
Proof. by rewrite hommxE vecofK. Qed.

Lemma hom_vecof (phi : 'Hom(uT, vT)) u :
   phi (vecof e u) = vecof f (u *m mxof phi).
Proof. by rewrite mul_mxof rowmxofK. Qed.

Lemma rowmxof_app (phi : 'Hom(uT, vT)) u :
  rowmxof f (phi u) = rowmxof e u *m mxof phi.
Proof. by rewrite mul_mxof !rowmxofK. Qed.

Lemma vecof_mul M u : vecof f (u *m M) = hommx M (vecof e u).
Proof. by rewrite hommxE vecofK. Qed.

Lemma mxof_eq0 phi : (mxof phi == 0) = (phi == 0).
Proof. by rewrite -(inj_eq (can_inj hommxK)) mxofK linear0. Qed.

Lemma hommx_eq0 M : (hommx M == 0) = (M == 0).
Proof. by rewrite -(inj_eq (can_inj mxofK)) hommxK linear0. Qed.

End hommx.

Section hommx_comp.

Context {uT vT wT : vectType F}.
Local Notation m := (\dim {:uT}).
Local Notation n := (\dim {:vT}).
Local Notation p := (\dim {:wT}).

Variables (e : m.-tuple uT) (f : n.-tuple vT) (g : p.-tuple wT).
Hypothesis e_basis: basis_of {:uT} e.
Hypothesis f_basis: basis_of {:vT} f.
Hypothesis g_basis: basis_of {:wT} g.

Lemma mxof_comp (phi : 'Hom(uT, vT)) (psi : 'Hom(vT, wT)) :
  mxof e g (psi \o phi)%VF = mxof e f phi *m mxof f g psi.
Proof.
apply/matrixP => i k; rewrite !(mxE, comp_lfunE, lfunE) /=.
rewrite [phi _](coord_basis f_basis) ?memvf// 2!linear_sum/=.
by apply: eq_bigr => j _ /=; rewrite !mxE !linearZ/= !vecof_delta.
Qed.

Lemma hommx_mul (A : 'M_(m,n)) (B : 'M_(n, p)) :
  hommx e g (A *m B) = (hommx f g B \o hommx e f A)%VF.
Proof.
by apply: (can_inj (mxofK e_basis g_basis)); rewrite mxof_comp !hommxK.
Qed.

End hommx_comp.

Section vsms.

Context {vT : vectType F}.
Local Notation n := (\dim {:vT}).

Variables (e : n.-tuple vT).

Definition msof (V : {vspace vT}) : 'M_n := mxof e e (projv V).
(* alternative *)
(* (\sum_(v <- vbasis V) <<rowmxof e v>>)%MS. *)

Definition vsof (M : 'M[F]_n) := limg (hommx e e M).
(* alternative *)
(* <<[seq vecof e (row i M) | i : 'I_n]>>%VS. *)


Lemma mxof1 : free e -> mxof e e \1 = 1%:M.
Proof.
by move=> eF; apply/matrixP=> i j; rewrite !mxE vecof_delta lfunE coord_free.
Qed.

Hypothesis e_basis: basis_of {:vT} e.

Lemma hommx1 : hommx e e 1%:M = \1%VF.
Proof. by rewrite -mxof1 ?(basis_free e_basis)// mxofK. Qed.

Lemma msofK : cancel msof vsof.
Proof. by rewrite /msof /vsof; move=> V; rewrite mxofK// limg_proj. Qed.

Lemma mem_vecof u (V : {vspace vT}) : (vecof e u \in V) = (u <= msof V)%MS.
Proof.
apply/idP/submxP=> [|[v ->{u}]]; last by rewrite -hom_vecof// memv_proj.
rewrite -[V in X in X -> _]msofK => /memv_imgP[v _].
by move=> /(canRL (vecofK _)) ->//; rewrite -rowmxof_mul//; eexists.
Qed.

Lemma rowmxof_sub u M : (rowmxof e u <= M)%MS = (u \in vsof M).
Proof.
apply/submxP/memv_imgP => [[v /(canRL (rowmxofK _)) ->//]|[v _ ->]]{u}.
  by exists (vecof e v); rewrite ?memvf// -vecof_mul.
by exists (rowmxof e v); rewrite -rowmxof_mul.
Qed.

Lemma vsof_sub M V : (vsof M <= V)%VS = (M <= msof V)%MS.
Proof.
apply/subvP/rV_subP => [MsubV _/submxP[u ->]|VsubM _/memv_imgP[u _ ->]].
  by rewrite -mem_vecof MsubV// -rowmxof_sub vecofK// submxMl.
by rewrite -[V]msofK -rowmxof_sub VsubM// -rowmxof_mul// submxMl.
Qed.

Lemma msof_sub V M : (msof V <= M)%MS = (V <= vsof M)%VS.
Proof.
apply/rV_subP/subvP => [VsubM v vV|MsubV _/submxP[u ->]].
  by rewrite -rowmxof_sub VsubM// -mem_vecof rowmxofK.
by rewrite mul_mxof rowmxof_sub MsubV// memv_proj.
Qed.

Lemma vsofK M : (msof (vsof M) == M)%MS.
Proof. by rewrite msof_sub -vsof_sub subvv. Qed.

Lemma sub_msof : {mono msof : V V' / (V <= V')%VS >-> (V <= V')%MS}.
Proof. by move=> V V'; rewrite msof_sub msofK. Qed.

Lemma sub_vsof : {mono vsof : M M' / (M <= M')%MS >-> (M <= M')%VS}.
Proof. by move=> M M'; rewrite vsof_sub (eqmxP (vsofK _)). Qed.

Lemma msof0 : msof 0 = 0.
Proof.
apply/eqP; rewrite -submx0; apply/rV_subP => v.
by rewrite -mem_vecof memv0 vecof_eq0// => /eqP->; rewrite sub0mx.
Qed.

Lemma vsof0 : vsof 0 = 0%VS.
Proof. by apply/vspaceP=> v; rewrite memv0 -rowmxof_sub submx0 rowmxof_eq0. Qed.

Lemma msof_eq0 V : (msof V == 0) = (V == 0%VS).
Proof. by rewrite -(inj_eq (can_inj msofK)) msof0. Qed.

Lemma vsof_eq0 M : (vsof M == 0%VS) = (M == 0).
Proof.
rewrite (sameP eqP eqmx0P) -!(eqmxP (vsofK M)) (sameP eqmx0P eqP) -msof0.
by rewrite (inj_eq (can_inj msofK)).
Qed.

End vsms.

Section eigen.

Context {uT : vectType F}.

Definition leigenspace (phi : 'End(uT)) a := lker (phi - a *: \1%VF).
Definition leigenvalue phi a := leigenspace phi a != 0%VS.

Local Notation m := (\dim {:uT}).
Variables (e : m.-tuple uT).
Hypothesis e_basis: basis_of {:uT} e.
Let e_free := basis_free e_basis.

Lemma lker_ker phi : lker phi = vsof e (kermx (mxof e e phi)).
Proof.
apply/vspaceP => v; rewrite memv_ker -rowmxof_sub// (sameP sub_kermxP eqP).
by rewrite -rowmxof_app// rowmxof_eq0.
Qed.

Lemma limgE phi : limg phi = vsof e (mxof e e phi).
Proof.
apply/vspaceP => v; rewrite -rowmxof_sub//.
apply/memv_imgP/submxP => [[u _ ->]|[u /(canRL (rowmxofK _)) ->//]].
  by exists (rowmxof e u); rewrite -rowmxof_app.
by exists (vecof e u); rewrite ?memvf// -hom_vecof.
Qed.

Lemma leigenspaceE f a :
   leigenspace f a = vsof e (eigenspace (mxof e e f) a).
Proof.
by rewrite /leigenspace /eigenspace lker_ker linearB linearZ/= mxof1// scalemx1.
Qed.

End eigen.
End passmx.
End passmx.
