From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

CoInductive unsplit_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | UnsplitLo (j : 'I_m) of i = lshift _ j : unsplit_spec i (inl _ j) true
  | UnsplitHi (k : 'I_n) of i = rshift _ k : unsplit_spec i (inr _ k) false.

Lemma unsplitP m n (i : 'I_(m + n)) : unsplit_spec i (split i) (i < m)%N.
Proof. by case: splitP=> j eq_j; constructor; apply/val_inj. Qed.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation stable V f := (V%MS *m f%R <= V%MS)%MS.

Lemma mul_mx_rowfree_eq0 (K : fieldType) (m n p: nat)
                         (W : 'M[K]_(m,n)) (V : 'M[K]_(n,p)) :
  row_free V -> (W *m V == 0) = (W == 0).
Proof. by move=> free; rewrite -!mxrank_eq0 mxrankMfree ?mxrank_eq0. Qed.

Lemma sub_sums_genmxP (F : fieldType) (I : finType) (P : pred I) (m n : nat)
  (A : 'M[F]_(m, n)) (B_ : I -> 'M_(m, n)) :
  reflect (exists u_ : I -> 'M_m, A = \sum_(i | P i) u_ i *m B_ i)
    (A <= \sum_(i | P i) <<B_ i>>)%MS.
Proof.
apply: (iffP idP) => [/sub_sumsmxP [u_ A_def]|[u_ ->]]; last first.
  by rewrite summx_sub_sums // => i _; rewrite genmxE submxMl.
suff /all_tag[v_ v_eq] :  forall i, {v | u_ i *m  <<B_ i>>%MS = v *m B_ i}.
  by exists v_; rewrite A_def (eq_bigr _ (fun _ _ => v_eq _)).
by move=> i; apply/sig_eqW/submxP; rewrite (submx_trans (submxMl _ _)) ?genmxE.
Qed.

Lemma mulmxP (K : fieldType) (m n : nat) (A B : 'M[K]_(m, n)) :
  reflect (forall u : 'rV__, u *m A = u *m B) (A == B).
Proof.
apply: (iffP eqP) => [-> //|eqAB].
apply: (@row_full_inj _ _ _ _ 1%:M); first by rewrite row_full_unit unitmx1.
by apply/row_matrixP => i; rewrite !row_mul eqAB.
Qed.

Section Restriction.

Variable K : fieldType.
Variable m : nat.
Variables (V : 'M[K]_m).

Implicit Types f : 'M[K]_m.

Definition restrict f : 'M_(\rank V) := row_base V *m f *m (pinvmx (row_base V)).

Lemma stable_row_base f : (stable (row_base V) f) = (stable V f).
Proof.
rewrite eq_row_base.
by apply/idP/idP=> /(submx_trans _) ->; rewrite ?submxMr ?eq_row_base.
Qed.

Lemma eigenspace_restrict f : (V *m f <= V)%MS ->
  forall n a (W : 'M_(n, \rank V)),
  (W <= eigenspace (restrict f) a)%MS =
  (W *m row_base V <= eigenspace f a)%MS.
Proof.
move=> f_stabV n a W; apply/eigenspaceP/eigenspaceP; rewrite scalemxAl.
  by move<-; rewrite -mulmxA -[X in _ = X]mulmxA mulmxKpV ?stable_row_base.
move/(congr1 (mulmx^~ (pinvmx (row_base V)))).
rewrite -2!mulmxA [_ *m (f *m _)]mulmxA => ->.
by apply: (row_free_inj (row_base_free V)); rewrite mulmxKpV ?submxMl.
Qed.

Lemma eigenvalue_restrict  f : stable V f ->
  {subset eigenvalue (restrict f) <= eigenvalue f}.
Proof.
move=> f_stabV a /eigenvalueP [x /eigenspaceP]; rewrite eigenspace_restrict //.
move=> /eigenspaceP Hf x_neq0; apply/eigenvalueP.
exists (x *m row_base V); rewrite ?mul_mx_rowfree_eq0 ?row_base_free //.
Qed.

Lemma restrictM : {in [pred f | stable V f] &, {morph restrict : f g / f *m g}}.
Proof.
move=> f g; rewrite !inE => Vf Vg /=.
by rewrite /restrict 2!mulmxA mulmxA mulmxKpV ?stable_row_base.
Qed.

End Restriction.

Section Stability.

Variable (F : fieldType).
Variable (n' : nat). Let n := n'.+1.
Implicit Types (f g : 'M[F]_n).

Lemma comm_stable (f g : 'M[F]_n) : GRing.comm f g -> stable f g.
Proof. by move=> comm_fg; rewrite [_ *m _]comm_fg mulmx_sub. Qed.

Lemma comm_stable_ker (f g : 'M[F]_n) :
  GRing.comm f g -> stable (kermx f) g.
Proof.
move=> comm_fg; apply/sub_kermxP.
by rewrite -mulmxA -[g *m _]comm_fg mulmxA mulmx_ker mul0mx.
Qed.

Lemma commrC (f : 'M[F]_n) (a : F) : GRing.comm f a%:M.
Proof. by rewrite /GRing.comm [_ * _]mul_mx_scalar [_ * _]mul_scalar_mx. Qed.

Lemma commr_poly (R : ringType) (a b : R) (p : {poly R}) :
      GRing.comm a b -> comm_coef p a -> GRing.comm a p.[b].
Proof.
move=> comm_ab. elim/poly_ind: p => [|p c]; rewrite !hornerE.
  move=> _; exact: commr0.
rewrite !hornerE_comm => comm_apb comm_coef_pXca.
apply/commrD; last first.
  by have := comm_coef_pXca 0%N; rewrite coefD coefMX add0r coefC eqxx.
apply/commrM => //; apply/comm_apb => i.
by have := comm_coef_pXca i.+1; rewrite coefD coefMX coefC /= addr0.
Qed.

Lemma commr_mxpoly (f g : 'M[F]_n) (p : {poly F}) : GRing.comm f g ->
  GRing.comm f (horner_mx g p).
Proof.
move=> comm_fg; apply: commr_poly => // i.
by rewrite coef_map /=; apply/commr_sym/commrC.
Qed.

Lemma comm_stable_eigenspace (f g : 'M[F]_n) a : GRing.comm f g ->
  stable (eigenspace f a) g.
Proof.
move=> comm_fg; rewrite comm_stable_ker //.
by apply/commr_sym/commrD=> //; apply/commrN/commrC.
Qed.

End Stability.

Section Diag.
Variable (F : fieldType).
Variable (n' : nat). Let n := n'.+1.
Implicit Types (f g p : 'M[F]_n) (fs : seq 'M[F]_n) (d : 'rV[F]_n).

Definition all_comm fs :=
  all (pred1 true) [seq f * g == g * f | f <- fs, g <- fs].

Lemma all_commP fs :
  reflect {in fs &, forall f g, GRing.comm f g} (all_comm fs).
Proof.
by rewrite /GRing.comm; apply: (iffP all_allpairsP);
   move => /(_ _ _ _ _)/eqP/eqP comm_xy x y fx fy /=; rewrite comm_xy ?eqxx.
Qed.

Lemma all_comm1 f : all_comm [:: f]. Proof. by rewrite /all_comm/= ?eqxx. Qed.

Lemma all_comm2P f g : reflect (GRing.comm f g) (all_comm [:: f; g]).
Proof. by apply: (iffP and4P) => [[_/eqP/eqP//]|->]; rewrite ?eqxx. Qed.

Lemma all_comm_cons f fs :
  all_comm (f :: fs) = all [pred g | f * g == g * f] fs && all_comm fs.
Proof. Admitted.

Definition diagonalisable f :=
  exists2 r, uniq r & mxminpoly f %| \prod_(x <- r) ('X - x%:P).

Definition codiagonalisable (fs : seq 'M[F]_n) :=
  all_comm fs /\ forall f, f \in fs -> diagonalisable f.

Lemma codiagonalisable1 f : codiagonalisable [:: f] <-> diagonalisable f.
Proof.
rewrite /codiagonalisable all_comm1/=; split => [[_]|df].
  by apply; rewrite mem_head.
by split=> [//|f']; rewrite in_cons in_nil orbF => /eqP->.
Qed.

Lemma codiagonalisable2P f g :
  [/\ GRing.comm f g, diagonalisable f & diagonalisable g] <->
          (codiagonalisable [:: f; g]).
Admitted.

Lemma codiagonalisable_cons f fs :
  codiagonalisable (f :: fs) <->
  [/\ all [pred g | f * g == g * f] fs, diagonalisable f & codiagonalisable fs].
Admitted.

Lemma codiagonalisable0 : codiagonalisable [::]. Proof. by []. Qed.

Definition sim p f g := p * f == g * p.

Lemma simP {p f g} : reflect (f = p^-1 * g * p) (sim p f g).
Admitted.

Definition sim_diag_ p f :=
  [forall i, forall j, (i != j) ==> ((p * f * p^-1) i j == 0)].

Lemma sim_diagP p f : p \is a GRing.unit ->
  reflect (exists d, sim p f (diag_mx d)) (sim_diag_ p f).
Admitted.

Lemma codiagonalisableP fs : codiagonalisable fs <->
  exists2 p, p \is a GRing.unit & all (sim_diag_ p) fs.
Proof. Admitted.


Lemma diagonalisableP f :
  diagonalisable f <-> exists2 p, p \is a GRing.unit & sim_diag_ p f.
Proof.
Admitted.

(* Lemma diagonalisable_eigenvalueP f : *)
(*   diagonalisable f <-> exists2 r, uniq r & (\sum_(x <- r) eigenspace f x = 1)%MS. *)
(* Admitted. *)

End Diag.
