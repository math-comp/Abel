From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sig_big_dep (R : Type) (idx : R) (op : Monoid.com_law idx)
      (I : finType) (J : I -> finType)
    (P : pred I) (Q : forall {i}, pred (J i)) (F : forall {i}, J i -> R) :
  \big[op/idx]_(i | P i) \big[op/idx]_(j : J i | Q j) F j =
  \big[op/idx]_(p : {i & J i} | P (tag p) && Q (tagged p)) F (tagged p).
Proof.
symmetry; rewrite [LHS]big_mkcond [RHS]big_mkcond.
rewrite (perm_big [seq Tagged J j | i <- index_enum I, j <- index_enum (J i)]).
  rewrite big_allpairs_dep; symmetry; apply: eq_bigr => i _.
  rewrite (@big_morph _ _ (fun x => if _ then x else _) idx op);
    do ?by move=> *; case: {+}P => //; rewrite Monoid.mulm1.
  rewrite [LHS]big_mkcond; apply: eq_bigr => j _ /=.
  by rewrite andbC; case: ifP => Qij.
apply: uniq_perm; rewrite ?index_enum_uniq//.
  rewrite allpairs_uniq_dep//; do ?by [move=> *; rewrite index_enum_uniq].
  by move=> [i1 j1] [i2 j2] _ _/=.
move=> [i j]; rewrite mem_index_enum /=; symmetry.
by apply/allpairsPdep; exists i, j.
Qed.

Section All11.

Definition all11 (T : Type) (r : rel T) xs := all id [seq r x y | x <- xs, y <- xs].

Lemma all11_map (T T' : Type) (f : T' -> T) (r : rel T) xs :
  all11 r (map f xs) = all11 (relpre f r) xs.
Proof. by rewrite /all11 allpairs_mapl allpairs_mapr. Qed.

Lemma all11P {T : eqType} {r : rel T} {xs : seq T} :
  reflect {in xs &, forall x y, r x y} (all11 r xs).
Proof. exact: all_allpairsP. Qed.

Variable (T : nonPropType) (r : rel T).
Implicit Types (xs : seq T) (x y z : T).
Hypothesis (rxx : reflexive r) (rsym : symmetric r).

Lemma all111 x : all11 r [:: x]. Proof. by rewrite /all11/= rxx. Qed.

Lemma all112 x y : all11 r [:: x; y] = r x y.
Proof. by rewrite /all11/= !rxx [r y x]rsym !(andbT, andbb). Qed.

Lemma all11_cons x xs : all11 r (x :: xs) = all (r x) xs && all11 r xs.
Proof.
pose f := nth x xs; have -> : xs = [seq f i | i <- iota 0 (size xs)].
  apply: (@eq_from_nth _ x); first by rewrite size_map size_iota.
  by move=> i i_lt; rewrite (nth_map 0) ?size_iota// nth_iota.
have -> : x = f (size xs).+1 by rewrite /f nth_default.
move: (size xs) (iota 0 _) => k s; rewrite -map_cons !all11_map all_map.
rewrite /all11/= ?rxx/= all_cat all_map; have [xxs/=|//] := boolP (all _ s).
rewrite -[flatten _]/[seq relpre f r z y | z <- s, y <- k.+1 :: s].
apply/all_allpairsP/all_allpairsP => xxsP y z yxs; rewrite ?inE.
  by move=> zxs; apply: xxsP; rewrite ?inE ?zxs ?orbT.
by move=> /predU1P[->|/xxsP/(_ yxs)//]; rewrite rsym//; apply: (allP xxs).
Qed.

End All11.

CoInductive unsplit_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | UnsplitLo (j : 'I_m) of i = lshift _ j : unsplit_spec i (inl _ j) true
  | UnsplitHi (k : 'I_n) of i = rshift _ k : unsplit_spec i (inr _ k) false.

Lemma unsplitP m n (i : 'I_(m + n)) : unsplit_spec i (split i) (i < m)%N.
Proof. by case: splitP=> j eq_j; constructor; apply/val_inj. Qed.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation stable V f := (V%MS *m f%R <= V%MS)%MS.

Lemma mul_mx_rowfree_eq0 (F : fieldType) (m n p: nat)
                         (W : 'M[F]_(m,n)) (V : 'M[F]_(n,p)) :
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

Lemma mulmxP (F : fieldType) (m n : nat) (A B : 'M[F]_(m, n)) :
  reflect (forall u : 'rV__, u *m A = u *m B) (A == B).
Proof.
apply: (iffP eqP) => [-> //|eqAB].
apply: (@row_full_inj _ _ _ _ 1%:M); first by rewrite row_full_unit unitmx1.
by apply/row_matrixP => i; rewrite !row_mul eqAB.
Qed.

Lemma horner_mx_diag (F : fieldType) (n : nat) (d : 'rV[F]_n.+1) (p : {poly F}) :
  horner_mx (diag_mx d) p = diag_mx (map_mx (horner p) d).
Proof.
apply/matrixP => i j; rewrite !mxE.
elim/poly_ind: p => [|p c ihp]; first by rewrite rmorph0 horner0 mxE mul0rn.
rewrite !hornerE mulrnDl rmorphD rmorphM /= horner_mx_X horner_mx_C !mxE.
rewrite (bigD1 j)//= ihp mxE ?eqxx mulr1n -mulrnAl big1 ?addr0//.
  by case: (altP (i =P j)) => [->|]; rewrite /= !(mulr1n, addr0, mul0r).
by move=> k /negPf nkF; rewrite mxE nkF mulr0.
Qed.

Lemma row_diag_mx  (F : fieldType) (n : nat) (d : 'rV[F]_n) i :
  row i (diag_mx d) = d 0 i *: delta_mx 0 i.
Proof. by apply/rowP => j; rewrite !mxE eqxx eq_sym mulr_natr. Qed.

Lemma mxminpoly_minP (F : fieldType) (n' : nat) (A : 'M_n'.+1) (p : {poly F}):
  reflect (horner_mx A p = 0) (mxminpoly A %| p).
Proof.
apply: (iffP idP); last exact: mxminpoly_min.
by move=> /dvdpP[q ->]; rewrite rmorphM/= mx_root_minpoly mulr0.
Qed.

Section Stability.
Variable (F : fieldType).

Lemma eqmx_stable m m' n (V : 'M[F]_(m,n)) (V' : 'M[F]_(m', n)) (f : 'M[F]_n) :
  (V :=: V')%MS -> stable V f = stable V' f.
Proof. by move=> eqVV'; rewrite (eqmxMr _ eqVV') eqVV'. Qed.

Section Preservation.

Variables (m n : nat) (V : 'M[F]_(m, n)) (f g : 'M[F]_n).

Lemma stable_row_base : (stable (row_base V) f) = (stable V f).
Proof. by apply: eqmx_stable; apply: eq_row_base. Qed.

(* equip stableM as a rpred + special cases when n not manifest positive *)
Lemma stableM : stable V f -> stable V g -> stable V (f *m g).
Proof.
by move=> f_stab g_stab; rewrite (submx_trans _ g_stab)// mulmxA submxMr.
Qed.

Lemma stableD : stable V f -> stable V g -> stable V (f + g).
Proof. by move=> f_stab g_stab; rewrite mulmxDr addmx_sub. Qed.

Lemma stableN : stable V (- f) = stable V f.
Proof. by rewrite mulmxN eqmx_opp. Qed.

Lemma stableC x : stable V x%:M.
Proof. by rewrite mul_mx_scalar scalemx_sub. Qed.

Lemma stable0 : stable V 0. Proof. by rewrite mulmx0 sub0mx. Qed.

End Preservation.

Lemma stable_unit (n : nat) (V f : 'M[F]_n) : V \in unitmx -> stable V f.
Proof. by move=> Vunit; rewrite submx_full ?row_full_unit. Qed.

Lemma stable_sum (n : nat) (I : finType) (V_ : I -> 'M[F]_n) (f : 'M[F]_n) :
  (forall i, stable (V_ i) f) -> stable (\sum_i V_ i)%MS f.
Proof.
by move=> fV; rewrite sumsmxMr; apply/sumsmx_subP => i; rewrite (sumsmx_sup i).
Qed.

Section Commutation.

Variable (n' : nat).
Let n := n'.+1.
Implicit Types (f g : 'M[F]_n).

Lemma comm_stable (f g : 'M[F]_n) : GRing.comm f g -> stable f g.
Proof. by move=> comm_fg; rewrite [_ *m _]comm_fg mulmx_sub. Qed.

Lemma comm_stable_ker (f g : 'M[F]_n) :
  GRing.comm f g -> stable (kermx f) g.
Proof.
move=> comm_fg; apply/sub_kermxP.
by rewrite -mulmxA -[g *m _]comm_fg mulmxA mulmx_ker mul0mx.
Qed.

Lemma commmxC (f : 'M[F]_n) (a : F) : GRing.comm f a%:M.
Proof. by rewrite /GRing.comm [_ * _]mul_mx_scalar [_ * _]mul_scalar_mx. Qed.
Hint Resolve commmxC : core.

Lemma commCmx (f : 'M[F]_n) (a : F) : GRing.comm a%:M f.
Proof. exact/commr_sym/commmxC. Qed.
Hint Resolve commCmx : core.

Lemma commr_poly (R : ringType) (a b : R) (p : {poly R}) :
      GRing.comm a b -> comm_coef p a -> GRing.comm a p.[b].
Proof.
move=> cab cpa; rewrite horner_coef; apply: commr_sum => i _.
by apply: commrM => //; apply: commrX.
Qed.

Lemma commr_mxpoly (f g : 'M[F]_n) (p : {poly F}) : GRing.comm f g ->
  GRing.comm f (horner_mx g p).
Proof. by move=> cfg; apply: commr_poly => // i; rewrite coef_map commCmx. Qed.

Lemma comm_stable_eigenspace (f g : 'M[F]_n) a : GRing.comm f g ->
  stable (eigenspace f a) g.
Proof. by move=> cfg; rewrite comm_stable_ker//; apply/commr_sym/commrB. Qed.

End Commutation.

End Stability.

Section pinvmx.
Variable F : fieldType.

Lemma pinvmxE n (A : 'M[F]_n) : unitmx A -> pinvmx A = invmx A.
Proof.
move=> A_unit; apply: (@row_free_inj _ _ _ _ A); rewrite ?row_free_unit//.
by rewrite -[pinvmx _]mul1mx mulmxKpV ?sub1mx ?row_full_unit// mulVmx.
Qed.

Lemma mulmxVp m n (A : 'M[F]_(m, n)) : row_free A -> A *m pinvmx A = 1%:M.
Proof.
move=> fA; rewrite -[X in X *m _]mulmx_ebase !mulmxA mulmxK ?row_ebase_unit//.
rewrite -[X in X *m _]mulmxA mul_pid_mx !minnn (minn_idPr _) ?rank_leq_col//.
by rewrite (eqP fA) pid_mx_1 mulmx1 mulmxV ?col_ebase_unit.
Qed.

Lemma mulVpmx m n (A : 'M[F]_(m, n)) : row_full A -> pinvmx A *m A = 1%:M.
Proof. by move=> fA; rewrite -[pinvmx _]mul1mx mulmxKpV// sub1mx. Qed.

Lemma mulmxKp p m n (B : 'M[F]_(m, n)) : row_free B ->
  cancel ((@mulmx _ p _ _)^~ B) (mulmx^~ (pinvmx B)).
Proof. by move=> ? A; rewrite -mulmxA mulmxVp ?mulmx1. Qed.

Lemma pinvmx_free m n (A : 'M[F]_(m, n)) : row_full A -> row_free (pinvmx A).
Proof. by move=> /mulVpmx pAA1; apply/row_freeP; exists A. Qed.

Lemma pinvmx_full m n (A : 'M[F]_(m, n)) : row_free A -> row_full (pinvmx A).
Proof. by move=> /mulmxVp ApA1; apply/row_fullP; exists A. Qed.

End pinvmx.

Section KernelLemma.

Variable K : fieldType.

(* convertible to kermx (horner_mx g p) when n = n.+1 *)
Definition kermxpoly n (g : 'M_n) (p : {poly K}) : 'M_n :=
  kermx ((if n is n.+1 then horner_mx^~ p : 'M_n.+1 -> 'M_n.+1 else \0) g).

Lemma horner_mxC (n' : nat) (g : 'M_n'.+1) (p : {poly K}) :
  GRing.comm (horner_mx g p) (horner_mx g p).
Proof. exact/commr_mxpoly/commr_sym/commr_mxpoly. Qed.

Lemma kermxpolyC n (g : 'M_n) c : c != 0 -> kermxpoly g c%:P = 0.
Proof.
move=> c_neq0; case: n => [|n] in g *; first by rewrite thinmx0.
apply/eqP; rewrite /kermxpoly horner_mx_C kermx_eq0 row_free_unit.
by rewrite -scalemx1 scaler_unit ?unitmx1// unitfE.
Qed.

Lemma kermxpoly1 n (g : 'M_n) : kermxpoly g 1 = 0.
Proof. by rewrite kermxpolyC ?oner_eq0. Qed.

Lemma kermxpolyX n (g : 'M_n) : kermxpoly g 'X = kermx g.
Proof.
case: n => [|n] in g *; first by rewrite !thinmx0.
by rewrite /kermxpoly horner_mx_X.
Qed.

Lemma kermxpoly_min n (g : 'M_n.+1) p :
  mxminpoly g %| p -> (kermxpoly g p :=: 1)%MS.
Proof.
move=> /dvdpP[q ->]; apply/eqmxP; rewrite /kermxpoly.
rewrite rmorphM/= mx_root_minpoly mulr0 submx1.
by apply/sub_kermxP; rewrite mulmx0.
Qed.

Lemma mxdirect_kermxpoly n (g : 'M_n) (p q : {poly K}) :
  coprimep p q -> (kermxpoly g p :&: kermxpoly g q = 0)%MS.
Proof.
case: n => [|n] in g *; first by rewrite thinmx0 ?cap0mx ?submx_refl.
move=> /Bezout_eq1_coprimepP [[/= u v]]; rewrite mulrC [v * _]mulrC => cpq.
apply/eqP/rowV0P => x.
rewrite sub_capmx => /andP[/sub_kermxP xgp0 /sub_kermxP xgq0].
move: cpq => /(congr1 (mulmx x \o horner_mx g))/=.
rewrite !(rmorphM, rmorphD, rmorph1, mulmx1, mulmxDr, mulmxA).
by rewrite xgp0 xgq0 !mul0mx add0r.
Qed.

Lemma kermxpolyM n (g : 'M_n) (p q : {poly K}) : coprimep p q ->
  (kermxpoly g (p * q) :=: kermxpoly g p + kermxpoly g q)%MS.
Proof.
case: n => [|n] in g *; first by rewrite !thinmx0.
move=> /Bezout_eq1_coprimepP [[/= u v]]; rewrite mulrC [v * _]mulrC => cpq.
apply/eqmxP/andP; split; last first.
  apply/sub_kermxP/eqmx0P; rewrite !addsmxMr [in X in (_ + X)%MS]mulrC.
  by rewrite !rmorphM/= !mulmxA !mulmx_ker !mul0mx !addsmx0 submx_refl.
move: cpq => /(congr1 (horner_mx g))/=; rewrite rmorph1 rmorphD/=.
rewrite -[X in (X <= _)%MS]mulr1 => <-; rewrite mulrDr mulrC addrC.
rewrite addmx_sub_adds//; apply/sub_kermxP; rewrite mulmxE -mulrA -rmorphM.
  by rewrite mulrAC [q * p]mulrC rmorphM/= mulrA -!mulmxE mulmx_ker mul0mx.
rewrite -[_ * _ * q]mulrA [u * _]mulrC.
by rewrite rmorphM mulrA -!mulmxE mulmx_ker mul0mx.
Qed.

Lemma kermxpoly_prod n (g : 'M_n)
    (I : finType) (P : {pred I}) (p_ : I -> {poly K}) :
  {in P &, forall i j, j != i -> coprimep (p_ i) (p_ j)} ->
  (kermxpoly g (\prod_(i | P i) p_ i) :=: \sum_(i | P i) kermxpoly g (p_ i))%MS.
Proof.
move=> p_coprime; elim: index_enum (index_enum_uniq I).
  by rewrite !big_nil ?kermxpoly1 ?submx_refl//.
move=> j js ihjs /= /andP[jNjs js_uniq]; apply/eqmxP.
rewrite !big_cons; case: ifP => [Pj|PNj]; rewrite ?ihjs ?submx_refl//.
suff cjjs: coprimep (p_ j) (\prod_(i <- js | P i) p_ i).
  by rewrite !kermxpolyM// !(adds_eqmx (eqmx_refl _) (ihjs _)) ?submx_refl.
rewrite (@big_morph _ _ _ true andb) ?big_all_cond ?coprimep1//; last first.
  by move=> p q; rewrite coprimepMr.
apply/allP => i i_js; apply/implyP => Pi; apply: p_coprime => //.
by apply: contraNneq jNjs => <-.
Qed.

Lemma mxdirect_sum_kermx n (g : 'M_n)
    (I : finType) (P : {pred I}) (p_ : I -> {poly K}) :
  {in P &, forall i j, j != i -> coprimep (p_ i) (p_ j)} ->
  mxdirect (\sum_(i | P i) kermxpoly g (p_ i))%MS.
Proof.
move=> p_coprime; apply/mxdirect_sumsP => i Pi; apply/eqmx0P.
have cpNi : {in [pred j | P j && (j != i)] &,
    forall j k : I, k != j -> coprimep (p_ j) (p_ k)}.
  by move=> j k /andP[Pj _] /andP[Pk _]; apply: p_coprime.
rewrite -!(cap_eqmx (eqmx_refl _) (kermxpoly_prod g _))//.
rewrite mxdirect_kermxpoly ?submx_refl//.
rewrite (@big_morph _ _ _ true andb) ?big_all_cond ?coprimep1//; last first.
  by move=> p q; rewrite coprimepMr.
by apply/allP => j _; apply/implyP => /andP[Pj neq_ji]; apply: p_coprime.
Qed.

Lemma eigenspace_poly n a (f : 'M_n) :
  eigenspace f a = kermxpoly f ('X - a%:P).
Proof.
case: n => [|m] in a f *; first by rewrite !thinmx0.
by congr (kermx _); rewrite rmorphB /= ?horner_mx_X ?horner_mx_C.
Qed.

Definition eigenpoly n (g : 'M_n) : pred {poly K} :=
  (fun p => kermxpoly g p != 0).

Lemma eigenpolyP n (g : 'M_n) (p : {poly K}) :
  reflect (exists2 v : 'rV_n, (v <= kermxpoly g p)%MS & v != 0) (eigenpoly g p).
Proof. exact: rowV0Pn. Qed.

Lemma horner_mx_stable m n p (V : 'M[K]_(n.+1, m.+1)) (f : 'M_m.+1) :
   stable V f -> stable V (horner_mx f p).
Proof.
move=> V_fstab; elim/poly_ind: p => [|p c]; first by rewrite rmorph0 stable0.
move=> fp_stable; rewrite rmorphD rmorphM/= horner_mx_X horner_mx_C.
by rewrite stableD ?stableM ?fp_stable ?stableC.
Qed.

Lemma eigenvalue_poly n a (f : 'M_n) :
  eigenvalue f a = eigenpoly f ('X - a%:P).
Proof. by rewrite /eigenpoly /eigenvalue eigenspace_poly. Qed.

End KernelLemma.

Section Restrict.
Context {F : fieldType}.

Definition conjmx (m n : nat)
 (V : 'M_(m, n)) (f : 'M[F]_n) : 'M_m :=  V *m f *m pinvmx V.
Notation restrict V := (conjmx (row_base V)).

Lemma stable_comp (m n p : nat) (V : 'M[F]_(m, n)) (W : 'M_(n, p)) (f : 'M_p) :
  stable W f -> stable V (conjmx W f) -> stable (V *m W) f.
Proof. by move=> Wf /(submxMr W); rewrite -mulmxA mulmxKpV// mulmxA. Qed.


Lemma conjmxM (m n : nat) (V : 'M[F]_(m, n)) : {in [pred f | stable V f] &,
   {morph conjmx V : f g / f *m g}}.
Proof.
move=> f g; rewrite !inE => Vf Vg /=.
by rewrite /conjmx 2!mulmxA mulmxA mulmxKpV ?stable_row_base.
Qed.

Lemma conjMmx (m n p : nat) (V : 'M[F]_(m, n)) (W : 'M_(n, p)) (f : 'M_p) :
  row_free (V *m W) -> stable W f -> stable V (conjmx W f) ->
  conjmx (V *m W) f = conjmx V (conjmx W f).
Proof.
move=> rfVW Wf VWf; apply: (row_free_inj rfVW); rewrite mulmxKpV ?stable_comp//.
by rewrite mulmxA mulmxKpV// -[RHS]mulmxA mulmxKpV ?mulmxA.
Qed.

Lemma conjuMmx (m n : nat) (V : 'M[F]_m) (W : 'M_(m, n)) (f : 'M_n) :
  V \in unitmx -> row_free W -> stable W f ->
  conjmx (V *m W) f = conjmx V (conjmx W f).
Proof.
move=> Vu rfW Wf; rewrite conjMmx ?stable_unit//.
by rewrite /row_free mxrankMfree// -/(row_free V) row_free_unit.
Qed.

Lemma conjMumx (m n : nat) (V : 'M[F]_(m, n)) (W f : 'M_n) :
  W \in unitmx -> row_free V -> stable V (conjmx W f) ->
  conjmx (V *m W) f = conjmx V (conjmx W f).
Proof.
move=> Wu rfW Wf; rewrite conjMmx ?stable_unit//.
by rewrite /row_free mxrankMfree ?row_free_unit.
Qed.

Lemma conjuMumx (n : nat) (V W f : 'M[F]_n) :
  V \in unitmx -> W \in unitmx ->
  conjmx (V *m W) f = conjmx V (conjmx W f).
Proof. by move=> Vu Wu; rewrite conjuMmx ?stable_unit ?row_free_unit. Qed.

Lemma conjmx_scalar (m n : nat) (V : 'M[F]_(m, n)) (a : F) :
  row_free V -> conjmx V a%:M = a%:M.
Proof. by move=> rfV; rewrite /conjmx scalar_mxC mulmxKp. Qed.

Lemma row_base0 (m n : nat) (O := 0 : 'M[F]_(m, n)) : row_base O = 0.
Proof. by apply/eqmx0P; rewrite !eq_row_base !sub0mx. Qed.

Lemma conj0mx (m n : nat) (O := 0 : 'M[F]_(m, n)) f : conjmx O f = 0.
Proof. by rewrite /conjmx !mul0mx. Qed.

Lemma conjmx0 (m n : nat) (V : 'M[F]_(m, n)) : conjmx V 0 = 0.
Proof. by rewrite /conjmx mulmx0 mul0mx. Qed.

Lemma conjumx (n : nat) (V : 'M_n) (f : 'M[F]_n) : V \in unitmx ->
  conjmx V f = V *m f *m invmx V.
Proof. by move=> uV; rewrite /conjmx pinvmxE. Qed.

Lemma conj1mx (n : nat) (f : 'M[F]_n) : conjmx 1%:M f = f.
Proof. by rewrite conjumx ?unitmx1// invmx1 mulmx1 mul1mx. Qed.

Lemma conjVmx (n : nat) (V : 'M_n) (f : 'M[F]_n) : V \in unitmx ->
  conjmx (invmx V) f = invmx V *m f *m V.
Proof. by move=> Vunit; rewrite conjumx ?invmxK ?unitmx_inv. Qed.

Lemma conjmxK (n : nat) (V f : 'M[F]_n) :
  V \in unitmx -> conjmx (invmx V) (conjmx V f) = f.
Proof. by move=> Vu; rewrite -conjuMumx ?unitmx_inv// mulVmx ?conj1mx. Qed.

Lemma conjmxVK (n : nat) (V f : 'M[F]_n) :
  V \in unitmx -> conjmx V (conjmx (invmx V) f) = f.
Proof. by move=> Vu; rewrite -conjuMumx ?unitmx_inv// mulmxV ?conj1mx. Qed.

Lemma horner_mx_conj m n p (B : 'M[F]_(n.+1, m.+1)) (f : 'M_m.+1) :
   row_free B -> stable B f ->
   horner_mx (conjmx B f) p = conjmx B (horner_mx f p).
Proof.
move=> B_free B_stab; rewrite/conjmx; elim/poly_ind: p => [|p c].
  by rewrite !rmorph0 mulmx0 mul0mx.
rewrite !(rmorphD, rmorphM)/= !(horner_mx_X, horner_mx_C) => ->.
rewrite [_ * _]mulmxA [_ *m (B *m _)]mulmxA mulmxKpV ?horner_mx_stable//.
apply: (row_free_inj B_free); rewrite [_ *m B]mulmxDl.
pose stableE := (stableD, stableM, stableC, horner_mx_stable).
by rewrite !mulmxKpV -?[B *m _ *m _]mulmxA ?stableE// mulmxDr -scalar_mxC.
Qed.

Lemma horner_mx_uconj n p (B : 'M[F]_(n.+1)) (f : 'M_n.+1) :
   B \is a GRing.unit ->
   horner_mx (B *m f *m invmx B) p = B *m horner_mx f p *m invmx B.
Proof.
move=> B_unit; rewrite -!conjumx//.
by rewrite horner_mx_conj ?row_free_unit ?stable_unit.
Qed.

Lemma horner_mx_uconjC n p (B : 'M[F]_(n.+1)) (f : 'M_n.+1) :
   B \is a GRing.unit ->
   horner_mx (invmx B *m f *m B) p = invmx B *m horner_mx f p *m B.
Proof.
move=> B_unit; rewrite -[X in _ *m X](invmxK B).
by rewrite horner_mx_uconj ?invmxK ?unitmx_inv.
Qed.

Lemma mxminpoly_conj m n (V : 'M[F]_(m.+1, n.+1)) (f : 'M_n.+1) :
  row_free V -> stable V f -> mxminpoly (conjmx V f) %| mxminpoly f.
Proof.
by move=> *; rewrite mxminpoly_min// horner_mx_conj// mx_root_minpoly conjmx0.
Qed.

Lemma mxminpoly_uconj n (V : 'M[F]_(n.+1)) (f : 'M_n.+1) :
  V \in unitmx -> mxminpoly (conjmx V f) = mxminpoly f.
Proof.
have simp := (row_free_unit, stable_unit, unitmx_inv, unitmx1).
move=> Vu; apply/eqP; rewrite -eqp_monic ?mxminpoly_monic// /eqp.
apply/andP; split; first by rewrite mxminpoly_conj ?simp.
by rewrite -[f in X in X %| _](conjmxK _ Vu) mxminpoly_conj ?simp.
Qed.

Section fixed_stable_space.

Variables (m n : nat).

Implicit Types (V : 'M[F]_(m, n)) (f : 'M[F]_n).
Implicit Types (a : F) (p : {poly F}).

Section Sub.
Variable (k : nat).
Implicit Types (W : 'M[F]_(k, m)).

Lemma sub_kermxpoly_conjmx V f p W : stable V f -> row_free V ->
  (W <= kermxpoly (conjmx V f) p)%MS = (W *m V <= kermxpoly f p)%MS.
Proof.
case: n m => [|n'] [|m']// in V f W * => fV rfV; rewrite ?thinmx0//.
   by rewrite mul0mx !sub0mx.
apply/sub_kermxP/sub_kermxP; rewrite horner_mx_conj//; last first.
  by move=> /(congr1 (mulmxr (pinvmx V)))/=; rewrite mul0mx !mulmxA.
move=> /(congr1 (mulmxr V))/=; rewrite ![W *m _]mulmxA ?mul0mx mulmxKpV//.
by rewrite -mulmxA mulmx_sub// horner_mx_stable//.
Qed.

Lemma sub_eigenspace_conjmx V f a W : stable V f -> row_free V ->
  (W <= eigenspace (conjmx V f) a)%MS = (W *m V <= eigenspace f a)%MS.
Proof. by move=> fV rfV; rewrite !eigenspace_poly sub_kermxpoly_conjmx. Qed.
End Sub.

Lemma eigenpoly_conjmx V f : stable V f -> row_free V ->
  {subset eigenpoly (conjmx V f) <= eigenpoly f}.
Proof.
move=> fV rfV a /eigenpolyP [x]; rewrite sub_kermxpoly_conjmx//.
move=> xV_le_fa x_neq0; apply/eigenpolyP.
by exists (x *m V); rewrite ?mul_mx_rowfree_eq0.
Qed.

Lemma eigenvalue_conjmx V f : stable V f -> row_free V ->
  {subset eigenvalue (conjmx V f) <= eigenvalue f}.
Proof.
by move=> fV rfV a; rewrite ![_ \in _]eigenvalue_poly; apply: eigenpoly_conjmx.
Qed.

Lemma conjmx_eigenvalue a V f : (V <= eigenspace f a)%MS -> row_free V ->
 conjmx V f = a%:M.
Proof.
by move=> /eigenspaceP Vfa rfV; rewrite /conjmx Vfa -mul_scalar_mx mulmxKp.
Qed.

End fixed_stable_space.
End Restrict.
Notation restrict V := (conjmx (row_base V)).

Section SimDiag.
Context {F : fieldType}.

Definition is_diag_mx m n (A : 'M[F]_(m, n)) :=
  [forall i : 'I__, forall j : 'I__, (i != j :> nat) ==> (A i j == 0)].

Lemma is_diag_mxP m n (A : 'M[F]_(m, n)) :
  reflect (forall i j : 'I__, i != j :> nat -> A i j = 0) (is_diag_mx A).
Proof. by apply: (iffP 'forall_'forall_implyP) => /(_ _ _ _)/eqP. Qed.

Lemma diag_mxP n (A : 'M[F]_n) :
  reflect (exists d : 'rV_n, A = diag_mx d) (is_diag_mx A).
Proof.
apply: (iffP (is_diag_mxP _)) => [Adiag|[d ->] i j neq_ij]; last first.
  by rewrite !mxE -val_eqE (negPf neq_ij).
exists (\row_i A i i); apply/matrixP => i j; rewrite !mxE.
by case: (altP (i =P j)) => [->|/Adiag->].
Qed.

Lemma is_diag_mx_diag n (r : 'rV[F]_n) : is_diag_mx (diag_mx r).
Proof. by apply/diag_mxP; eexists. Qed.

Lemma is_diag_mx_scalar n (a : F) : is_diag_mx (a%:M : 'M_n).
Proof. by rewrite -diag_const_mx is_diag_mx_diag. Qed.

Definition sim m n (P : 'M[F]_(m, n)) A B := conjmx P A == B.

Lemma simPp m n {P : 'M[F]_(m, n)} {A B} :
  stable P A -> sim P A B -> P *m A = B *m P.
Proof. by move=> stablePA /eqP <-; rewrite mulmxKpV. Qed.

Lemma simW m n {P : 'M[F]_(m, n)} {A B} : row_free P ->
  P *m A = B *m P -> sim P A B.
Proof. by rewrite /sim /conjmx => fP ->; rewrite mulmxKp. Qed.

Section Sim.

Context {n : nat}.
Implicit Types (f g p : 'M[F]_n) (fs : seq 'M[F]_n) (d : 'rV[F]_n).

Lemma simP {p f g} : p \in unitmx ->
  reflect (p *m f = g *m p) (sim p f g).
Proof.
move=> p_unit; apply: (iffP idP); first exact/simPp/stable_unit.
by apply: simW; rewrite row_free_unit.
Qed.

Lemma simRL {p f g} : p \in unitmx ->
  reflect (g = p *m f *m invmx p) (sim p f g).
Proof. by move=> ?; apply: (iffP eqP); rewrite conjumx. Qed.

Lemma simLR {p f g} : p \in unitmx ->
  reflect (f = conjmx (invmx p) g) (sim p f g).
Proof.
by move=> pu; rewrite conjVmx//; apply: (iffP (simRL pu)) => ->;
   rewrite !mulmxA ?(mulmxK, mulmxKV, mulVmx, mulmxV, mul1mx, mulmx1).
Qed.

End Sim.

Lemma sim_mxminpoly {n} {p f g : 'M_n.+1} : p \in unitmx ->
  sim p f g -> mxminpoly f = mxminpoly g.
Proof. by move=> pu /eqP<-; rewrite mxminpoly_uconj. Qed.

Fact sim_diag_key : unit. Proof. exact: tt. Qed.
Notation sim_diag_def :=
  (fun m n (P : 'M[F]_(m, n)) A => is_diag_mx (conjmx P A)).
Definition sim_diag := locked_with sim_diag_key sim_diag_def.

Lemma sim_diagE : sim_diag = sim_diag_def.
Proof. by rewrite /sim_diag unlock. Qed.

Lemma sim_diag_row_base m n (P : 'M[F]_(m, n)) (A : 'M_n) :
  sim_diag (row_base P) A = is_diag_mx (restrict P A).
Proof. by rewrite sim_diagE. Qed.

Lemma sim_diagPp m n (P : 'M[F]_(m, n)) A :
  reflect (forall i j : 'I__, i != j :> nat -> conjmx P A i j = 0)
          (sim_diag P A).
Proof. by rewrite sim_diagE; exact: (iffP (is_diag_mxP _)). Qed.

Lemma sim_diagP n (P : 'M[F]_n) A : P \in unitmx ->
  reflect (forall i j : 'I__, i != j :> nat -> (P *m A *m invmx P) i j = 0)
          (sim_diag P A).
Proof. by move=> Pu; apply: (iffP (sim_diagPp _ _)); rewrite conjumx. Qed.

Lemma sim_diagPex {m} {n} {P : 'M[F]_(m, n)} {A} :
  reflect (exists D, sim P A (diag_mx D)) (sim_diag P A).
Proof.
by rewrite sim_diagE; apply: (iffP (diag_mxP _)) => -[D]/eqP; exists D.
Qed.

Lemma sim_diagLR n {P : 'M[F]_n} {A} : P \in unitmx ->
  reflect (exists D, A = conjmx (invmx P) (diag_mx D)) (sim_diag P A).
Proof.
by move=> Punit; apply: (iffP sim_diagPex) => -[D /(simLR Punit)]; exists D.
Qed.

Lemma mxminpoly_diag {n} {d : 'rV[F]_n.+1}
    (u := undup [seq d 0 i | i <- enum 'I_n.+1]) :
  mxminpoly (diag_mx d) = \prod_(r <- u) ('X - r%:P).
Proof.
apply/eqP; rewrite -eqp_monic ?mxminpoly_monic ?monic_prod_XsubC// /eqp.
rewrite mxminpoly_min/=; last first.
  rewrite horner_mx_diag (_ : diag_mx (map_mx _ d) = 0) ?mulmx0 ?mul0mx//.
  apply/matrixP => i j; rewrite !mxE horner_prod.
  case: (altP (i =P j)) => [->|neq_ij//]; rewrite mulr1n.
  under eq_bigr => k _ do rewrite hornerXsubC.
  case: (@path.splitP _ u (d 0 j)); first by rewrite mem_undup map_f ?mem_enum.
  by move=> *; rewrite -cats1 !big_cat/= big_cons big_nil subrr !(mul0r,mulr0).
have [] := @uniq_roots_prod_XsubC _ (mxminpoly (diag_mx d)) u; last 2 first.
- by rewrite uniq_rootsE undup_uniq.
- by move=> q ->; rewrite dvdp_mull.
apply/allP => x; rewrite mem_undup => /mapP[i _ ->].
rewrite -eigenvalue_root_min; apply/eigenvalueP.
exists (delta_mx 0 i); first by rewrite -rowE row_diag_mx.
by apply/negP => /eqP/matrixP/(_ 0 i)/eqP; rewrite !mxE !eqxx oner_eq0.
Qed.

Lemma sim_diag_mxminpoly {n} {p f : 'M_n.+1}
  (rs := undup [seq conjmx p f i i | i <- enum 'I_n.+1]) :
  p \in unitmx -> sim_diag p f ->
  mxminpoly f = \prod_(r <- rs) ('X - r%:P).
Proof.
rewrite /rs => pu /(sim_diagLR pu)[d {f rs}->].
rewrite mxminpoly_uconj ?unitmx_inv// mxminpoly_diag.
by rewrite (@eq_map _ _ _ (d 0))// => i; rewrite conjmxVK// mxE eqxx.
Qed.

End SimDiag.

Lemma min_subindex_subproof n (p_ : 'I_n -> nat) (j : 'I_(\sum_i p_ i)) :
  {i0 : 'I_n | i0 = 0%N :> nat}.
Proof.
elim: n => [|n IHn] in p_ j *; last by exists ord0.
by rewrite big_ord0 in j *; exists j; case: j.
Qed.

Definition min_subindex n (p_ : 'I_n -> nat) (j : 'I_(\sum_i p_ i)) :=
  projT1 (min_subindex_subproof j).

Lemma min_subindex_eq0 n (p_ : 'I_n -> nat) (j : 'I_(\sum_i p_ i)) :
  min_subindex j = 0%N :> nat.
Proof. exact: (projT2 (min_subindex_subproof j)). Qed.

Definition subindex_start n (p_ : 'I_n -> nat) (i0 : 'I_n) :=
  (\sum_(i : 'I_n | i < i0) p_ i)%N.

Definition subindex n (p_ : 'I_n -> nat) (j : 'I_(\sum_i p_ i)) : 'I_n :=
  [arg max_(i0 > min_subindex j | (subindex_start p_ i0 <= j)%N) i0].

Lemma suboffset_subproof n (p_ : 'I_n -> nat) (j : 'I_(\sum_i p_ i)) :
  (j - subindex_start p_ (subindex j) < p_(subindex j))%N.
Proof.
rewrite /subindex; case: arg_maxnP => /= [|i0 j_ge i0_ge].
  by rewrite /subindex_start min_subindex_eq0 big1.
rewrite ltn_subLR// /subindex_start {j_ge}.
apply: (@leq_trans (\sum_(i < n | i <= i0) p_ i)%N); last first.
  by rewrite (bigD1 i0) 1?addnC//; under eq_bigl do rewrite andbC -ltn_neqAle.
have := (ltn_ord i0); rewrite leq_eqVlt => /predU1P[eq_n|lt_n].
  do [move: (val i0) eq_n => {}i0; case: {n}_ /] in p_ j i0_ge *.
  by under [X in (_ < X)%N]eq_bigl do rewrite leq_ord.
under [X in (_ < X)%N]eq_bigl do rewrite -ltnS; rewrite ltnNge; apply/negP.
by move=> /(i0_ge (Ordinal lt_n))/=; rewrite ltnn.
Qed.

Definition suboffset n (p_ : 'I_n -> nat)
    (j : 'I_(\sum_i p_ i)) : 'I_(p_(subindex j)) :=
  Ordinal (suboffset_subproof j).

Lemma superindex_subproof n (p_ : 'I_n -> nat) (i0 : 'I_n) (k : 'I_(p_ i0)) :
  (k + subindex_start p_ i0 < \sum_(i < n) p_ i)%N.
Proof.
rewrite [X in (_ < X)%N](bigD1 i0)//= -addSn leq_add//.
rewrite big_mkcond /subindex_start/= big_mkcond/= leq_sum// => i _.
by rewrite -val_eqE; case: ltngtP.
Qed.

Definition superindex n (p_ : 'I_n -> nat) (i0 : 'I_n) (k : 'I_(p_ i0)) :
  'I_(\sum_(i < n) p_ i) := Ordinal (superindex_subproof k).

Lemma suboffsetK  n (p_ : 'I_n -> nat) (j : 'I_(\sum_i p_ i)) :
  superindex (suboffset j) = j.
Proof.
apply: val_inj; rewrite /= subnK /subindex//; case: arg_maxnP => //=.
by rewrite /subindex_start min_subindex_eq0 big1.
Qed.

Lemma superindexK1 n (p_ : 'I_n -> nat) (i0 : 'I_n) (k : 'I_(p_ i0)) :
  subindex (superindex k) = i0.
Proof.
apply: val_inj; rewrite /subindex /superindex /= /subindex_start.
case: arg_maxnP => //=; first by rewrite min_subindex_eq0 big1.
move=> i exi maxi; apply/eqP; rewrite eqn_leq maxi ?leq_addl ?andbT//.
apply: contraTT exi; rewrite -!ltnNge => lt_i0i; rewrite -addSn.
rewrite [X in (_ <= X)%N](bigD1 i0)//= leq_add => //.
rewrite big_mkcond [X in (_ <= X)%N]big_mkcond leq_sum// => j _.
rewrite -val_eqE andbC; case: ltngtP => //= lt_ji0.
by rewrite (leq_trans lt_ji0)// ltnW.
Qed.

Lemma superindexK n (p_ : 'I_n -> nat) (i0 : 'I_n) (k : 'I_(p_ i0)) :
  suboffset (superindex k) = cast_ord (congr1 p_ (esym (superindexK1 k))) k.
Proof. by apply: val_inj => /=; rewrite superindexK1 addnK. Qed.

Definition subio {n} {p_ : 'I_n -> nat} (j : 'I_(\sum_i p_ i)) :
  {i & 'I_(p_ i)} := Tagged _ (suboffset j).
Definition superio {n} {p_ : 'I_n -> nat} (x : {i & 'I_(p_ i)}) :
  'I_(\sum_i p_ i) := superindex (tagged x).
Lemma superio_bij {n} {p_ : 'I_n -> nat} :
  {on [pred _ | true], bijective (@superio n p_)}.
Proof.
exists subio => [[i j] _|i _]; rewrite /superio /subio/= ?suboffsetK//.
by rewrite superindexK/=; case: _ / esym => /=; rewrite cast_ord_id.
Qed.
Hint Resolve superio_bij : core.

Definition col_block_mx (F : fieldType) m n (p_ : 'I_n -> nat)
  (B_ : forall i, 'M[F]_(p_ i, m)) : 'M_(\sum_i p_ i, m) :=
  \matrix_(j, k) B_ (subindex j) (suboffset j) k.

Definition row_block_mx (F : fieldType) m n (p_ : 'I_n -> nat)
  (B_ : forall i, 'M[F]_(m, p_ i)) : 'M_(m, \sum_i p_ i) :=
  \matrix_(j, k) B_ (subindex k) j (suboffset k).

Definition diag_block_mx (F : fieldType) n (p_ : 'I_n -> nat)
  (B_ : forall i, 'M[F]_(p_ i)) : 'M_(\sum_i p_ i) :=
  \matrix_(j, k)
   if subindex j =P subindex k isn't ReflectT e then 0
   else B_ (subindex k) (cast_ord (congr1 p_ e) (suboffset j)) (suboffset k).


Lemma mulmx_row_col_block (F : fieldType) p m n (p_ : 'I_n -> nat)
  (R_ : forall i, 'M[F]_(p, p_ i)) (C_ : forall i, 'M[F]_(p_ i, m)) :
  row_block_mx R_ *m col_block_mx C_ = \sum_i R_ i *m C_ i.
Proof.
apply/matrixP => i j; rewrite !mxE !summxE (reindex _ superio_bij)/=.
under [in RHS]eq_bigr do rewrite !mxE; rewrite sig_big_dep /superio/=.
apply: eq_bigr => -[/= k l] _.
by rewrite !mxE !superindexK/=; case: _ / esym; rewrite cast_ord_id.
Qed.

Lemma row_diag_block (F : fieldType) n (p_ : 'I_n -> nat)
    (B_ : forall i, 'M[F]_(p_ i)) k :
  row k (diag_block_mx B_) =
  row (suboffset k) (row_block_mx
    (fun i => if subindex k =P i is ReflectT e
              then castmx (esym (congr1 p_ e), erefl) (B_ i) else 0)).
Proof.
apply/rowP => j; rewrite !mxE; case: eqP => e; rewrite ?mxE ?castmxE//=.
by rewrite !cast_ord_id esymK.
Qed.

Lemma row_col_block (F : fieldType) (m n : nat) (p_ : 'I_n -> nat)
  (B_ : forall i, 'M[F]_(p_ i, m)) k :
  row k (col_block_mx B_) = row (suboffset k) (B_ (subindex k)).
Proof. by apply/rowP => l; rewrite !mxE. Qed.

Lemma mulmx_col_diag_block (F : fieldType) m n (p_ : 'I_n -> nat)
  (C_ : forall i, 'M[F]_(p_ i, m))  (D_ : forall i, 'M[F]_(p_ i)) :
  diag_block_mx D_ *m col_block_mx C_ = col_block_mx (fun i => D_ i *m C_ i).
Proof.
apply/row_matrixP => i.
rewrite row_mul row_diag_block row_col_block -row_mul mulmx_row_col_block.
congr (row _ _); rewrite (bigD1 (subindex i))//=; case: eqP => //= e.
rewrite -[e](eq_irrelevance erefl)/= castmx_id big1 ?addr0// => j.
by case: eqP => Ne; rewrite ?mul0mx// => jNsi; rewrite Ne eqxx in jNsi.
Qed.

Lemma eqmx_col_block  (F : fieldType) (m n : nat) (p_ : 'I_n -> nat)
  (V_ : forall i, 'M[F]_(p_ i, m)) : (col_block_mx V_ :=: \sum_i <<V_ i>>)%MS.
Proof.
apply/eqmxP/andP; split.
  apply/row_subP => i; rewrite row_col_block.
  by rewrite (sumsmx_sup (subindex i))// genmxE row_sub.
apply/sumsmx_subP => i0 _; rewrite genmxE; apply/row_subP => j.
apply: (eq_row_sub (superindex j)); apply/rowP => k.
by rewrite 2!mxE [in RHS]mxE superindexK; case: _ / esym; rewrite cast_ord_id.
Qed.

Lemma sim_diag_sum (F : fieldType) (m n : nat) (p_ : 'I_n -> nat)
      (V_ : forall i, 'M[F]_(p_ i, m)) (f : 'M[F]_m) :
    mxdirect (\sum_i <<V_ i>>) ->
    (forall i, stable (V_ i) f) ->
    (forall i, row_free (V_ i)) ->
  sim_diag (col_block_mx V_) f = [forall i, sim_diag (V_ i) f].
Proof.
move=> Vd Vf rfV; have aVf : stable (col_block_mx V_) f.
  rewrite (eqmx_stable _ (eqmx_col_block _)) stable_sum//.
  by move=> i; rewrite (eqmx_stable _ (genmxE _)).
apply/sim_diagPex/'forall_sim_diagPex => /=
    [[D /(simPp aVf) VMf] i|/(_ _)/sigW Dof].
  exists (\row_i D 0 (superindex i)); apply/eqP.
  apply: (canLR (mulmxKp _)); rewrite ?row_base_free//.
  apply/row_matrixP => j; rewrite row_mul.
  have /(congr1 (row (superindex j))) := VMf.
  rewrite [row (superindex _) _]row_mul row_col_block ?superindexK/=.
  rewrite !row_mul !row_diag_mx !mxE -!scalemxAl -!rowE.
  rewrite row_col_block ?superindexK//.
  by case: _ / esym => /=; rewrite cast_ord_id.
exists (row_block_mx (fun i : 'I_n => projT1 (Dof i))); apply/simW.
   rewrite -row_leq_rank eqmx_col_block (mxdirectP Vd)/=.
   by under [X in (_ <= X)%N]eq_bigr do rewrite genmxE (eqP (rfV _)).
apply/row_matrixP => i; rewrite !row_mul row_diag_mx -scalemxAl -rowE.
rewrite row_col_block !mxE -!row_mul.
case: Dof => /= k /(simPp); rewrite Vf => /(_ isT) ->.
by rewrite row_mul row_diag_mx -scalemxAl -rowE.
Qed.

Section Diag.
Variable (F : fieldType).

Definition diagonalisable n (A : 'M[F]_n) :=
  exists2 P, P \in unitmx & sim_diag P A.

Definition codiagonalisable n (As : seq 'M[F]_n) :=
  exists2 P, P \in unitmx & all (sim_diag P) As.

Lemma codiagonalisable1 n (A : 'M[F]_n) :
  codiagonalisable [:: A] <-> diagonalisable A.
Proof. by split=> -[P Punit PA]; exists P; move: PA; rewrite //= andbT. Qed.

(* the side condition on m looksartificial *)
Definition codiagonalisablePfull n (A : seq 'M[F]_n) :
  codiagonalisable A <-> exists2 m, (m <= n)%N &
    exists2 P : 'M_(m, n), row_full P & all (sim_diag P) A.
Proof.
split => [[P Punit SPA]|[m le_mn [P Pfull SPA]]].
  by exists n => //; exists P; rewrite ?row_full_unit.
have e : n = m by apply/eqP; rewrite eqn_leq le_mn -(eqP Pfull) rank_leq_row.
by case: _ / e in P Pfull SPA; exists P; rewrite // -row_full_unit.
Qed.

Lemma codiagonalisable_on (m n : nat) (V_ : 'I_n -> 'M[F]_m) (As : seq 'M[F]_m) :
  (\sum_i V_ i :=: 1%:M)%MS -> mxdirect (\sum_i V_ i) ->
  (forall i, all (fun A => stable (V_ i) A) As) ->
  (forall i, codiagonalisable (map (restrict (V_ i)) As)) -> codiagonalisable As.
Proof.
move=> V1 Vdirect /(_ _)/allP AV /(_ _) /sig2W/= Pof.
pose P_ i := projT1 (Pof i).
have P_unit i : P_ i \in unitmx by rewrite /P_; case: {+}Pof.
have P_diag i A : A \in As -> sim_diag (P_ i *m row_base (V_ i)) A.
  move=> AAs; rewrite /P_; case: {+}Pof => /= P Punit.
  rewrite all_map => /allP/(_ A AAs); rewrite sim_diagE/=.
  by rewrite conjuMmx ?row_base_free ?stable_row_base ?AV.
pose P := (col_block_mx (fun i => P_ i *m row_base (V_ i))).
have P_full i : row_full (P_ i) by rewrite row_full_unit.
have PrV i : (P_ i *m row_base (V_ i) :=: V_ i)%MS.
  exact/(eqmx_trans _ (eq_row_base _))/eqmxMfull.
apply/codiagonalisablePfull; eexists _; last exists P; rewrite /=.
- by rewrite -(mxdirectP Vdirect)//= V1 rank_leq_col.
- rewrite -sub1mx eqmx_col_block.
  by under eq_bigr do rewrite (eq_genmx (PrV _)); rewrite -genmx_sums genmxE V1.
apply/allP => A AAs; rewrite sim_diag_sum.
- by apply/forallP => i; apply: P_diag.
- rewrite mxdirectE/=.
  under eq_bigr do rewrite (eq_genmx (PrV _)); rewrite -genmx_sums genmxE V1.
  by under eq_bigr do rewrite genmxE PrV; rewrite  -(mxdirectP Vdirect)//= V1.
- by move=> i; rewrite (eqmx_stable _ (PrV _)) ?AV.
- by move=> i; rewrite /row_free eqmxMfull ?eq_row_base ?row_full_unit.
Qed.

Section codiag.
Variable (n : nat).
Implicit Types (f g p : 'M[F]_n) (fs : seq 'M[F]_n) (d : 'rV[F]_n).

Definition commmx f g := f *m g == g *m f.

Notation all_comm := (all11 commmx).

Lemma all_commP fs :
  reflect {in fs &, forall f g, f *m g = g *m f} (all_comm fs).
Proof. by apply: (iffP all11P) => fsP ? ? ? ?; apply/eqP/fsP. Qed.

Lemma all_comm1 f : all_comm [:: f]. Proof. by rewrite /commmx all111. Qed.

Lemma all_comm2P f g : reflect (f *m g = g *m f) (all_comm [:: f; g]).
Proof.
by rewrite /commmx; apply: (iffP and4P) => [[_/eqP//]|->]; rewrite ?eqxx.
Qed.

Lemma all_comm_cons f fs :
  all_comm (f :: fs) = all (commmx f) fs && all_comm fs.
Proof. by rewrite /commmx [LHS]all11_cons. Qed.

End codiag.
Arguments commmx {n}.
Notation all_comm := (all11 commmx).

Lemma diagonalisable_diag {n} (d : 'rV_n) : diagonalisable (diag_mx d).
Proof.
by exists 1%:M; rewrite ?unitmx1// sim_diagE conj1mx is_diag_mx_diag.
Qed.
Hint Resolve diagonalisable_diag : core.

Lemma diagonalisable_scalar {n} (a : F) : diagonalisable (a%:M : 'M_n).
Proof. by rewrite -diag_const_mx. Qed.
Hint Resolve diagonalisable_scalar : core.

Lemma diagonalisable0 {n} : diagonalisable (0 : 'M[F]_n).
Proof.
by rewrite (_ : 0 = 0%:M)//; apply/matrixP => i j; rewrite !mxE// mul0rn.
Qed.
Hint Resolve diagonalisable0 : core.

Lemma diagonalisablePeigen {n} {f : 'M[F]_n} :
  diagonalisable f <->
  exists2 rs, uniq rs & (\sum_(r <- rs) eigenspace f r :=: 1%:M)%MS.
Proof.
split=> [df|[rs urs rsP]].
  suff [rs rsP] : exists rs, (\sum_(r <- rs) eigenspace f r :=: 1%:M)%MS.
    exists (undup rs); rewrite ?undup_uniq//; apply: eqmx_trans rsP.
    elim: rs => //= r rs IHrs; rewrite big_cons.
    case: ifPn => in_rs; rewrite ?big_cons; last exact: adds_eqmx.
    apply/(eqmx_trans IHrs)/eqmx_sym/addsmx_idPr.
    have rrs : (index r rs < size rs)%N by rewrite index_mem.
    rewrite (big_nth 0) big_mkord (sumsmx_sup (Ordinal rrs)) ?nth_index//.
  move: df => [P Punit /(sim_diagLR Punit)[d ->]].
  exists [seq d 0 i | i <- enum 'I_n]; rewrite big_image/=.
  apply: (@eqmx_trans _ _ _ _ _ _ P); apply/eqmxP;
    rewrite ?sub1mx ?submx1 ?row_full_unit//.
  rewrite submx_full ?row_full_unit//=.
  apply/row_subP => i; rewrite rowE (sumsmx_sup i)//.
  apply/eigenspaceP; rewrite conjVmx// !mulmxA mulmxK//.
  by rewrite -rowE row_diag_mx scalemxAl.
have mxdirect_eigenspaces : mxdirect (\sum_(i < size rs) eigenspace f rs`_i).
  apply: mxdirect_sum_eigenspace => i j _ _ rsij; apply/val_inj.
  by apply: uniqP rsij; rewrite ?inE.
rewrite (big_nth 0) big_mkord in rsP; rewrite -codiagonalisable1.
apply/(codiagonalisable_on _ mxdirect_eigenspaces) => // i/=.
  case: n => [|n] in f {mxdirect_eigenspaces} rsP *.
    by rewrite thinmx0 sub0mx.
  by rewrite comm_stable_eigenspace.
rewrite codiagonalisable1.
by rewrite (@conjmx_eigenvalue _ _ _ rs`_i) ?eq_row_base ?row_base_free.
Qed.

Lemma diagonalisableP n' (n := n'.+1) (f : 'M[F]_n) :
  diagonalisable f <->
  exists2 rs, uniq rs & mxminpoly f %| \prod_(x <- rs) ('X - x%:P).
Proof.
split=> [[P Punit /sim_diagPex[d /(simLR Punit)->]]|].
  rewrite mxminpoly_uconj ?unitmx_inv// mxminpoly_diag.
  by eexists; [|by []]; rewrite undup_uniq.
rewrite diagonalisablePeigen => -[rs rsu rsP].
exists rs; rewrite // !(big_nth 0) !big_mkord in rsP *.
rewrite (eq_bigr _ (fun _ _ => eigenspace_poly _ _)).
apply: (eqmx_trans (eqmx_sym (kermxpoly_prod _ _)) (kermxpoly_min _)) => //.
by move=> i j _ _; rewrite coprimep_XsubC root_XsubC nth_uniq.
Qed.

Lemma diagonalisable_conj_diag m n (V : 'M[F]_(m, n)) (d : 'rV[F]_n) :
  stable V (diag_mx d) -> row_free V -> diagonalisable (conjmx V (diag_mx d)).
Proof.
case: m n => [|m] [|n]// in V d * => Vd rdV; rewrite ?thinmx0//=.
apply/diagonalisableP; pose u := undup [seq d 0 i | i <- enum 'I_n.+1].
exists u; first by rewrite undup_uniq.
by rewrite (dvdp_trans (mxminpoly_conj _ _))// mxminpoly_diag.
Qed.

Lemma codiagonalisableP n (fs : seq 'M[F]_n) :
  (all_comm fs) /\ (forall f, f \in fs -> diagonalisable f)
  <-> codiagonalisable fs.
Proof.
split => [cdfs|[P Punit /allP fsD]]/=; last first.
  split; last by exists P; rewrite // fsD.
  apply/all_commP => f g ffs gfs; move=> /(_ _ _)/sim_diagPex/sigW in fsD.
  have [[df /simLR->//] [dg /simLR->//]] := (fsD _ ffs, fsD _ gfs).
  by rewrite -!conjmxM 1?diag_mxC// inE stable_unit ?unitmx_inv.
have [k] := ubnP (size fs); elim: k => [|k IHk]//= in n fs cdfs *.
case: fs cdfs => [|f fs]//=; first by exists 1%:M; rewrite ?unitmx1.
rewrite ltnS all_comm_cons => -[/andP[/allP/(_ _ _)/eqP ffsC fsC dffs]] fsk.
have /diagonalisablePeigen [rs urs rs1] := dffs _ (mem_head _ _).
rewrite (big_nth 0) big_mkord in rs1.
have efg (i : 'I_(size rs)) g : g \in f :: fs -> stable (eigenspace f rs`_i) g.
   case: n => [|n'] in g f fs ffsC fsC {dffs rs1 fsk} * => g_ffs.
      by rewrite thinmx0 sub0mx.
  rewrite comm_stable_eigenspace//.
  by move: g_ffs; rewrite !inE => /predU1P [->//|/ffsC].
apply/(@codiagonalisable_on _ _ _ _ rs1) => [|i|i /=].
- apply: mxdirect_sum_eigenspace => i j _ _ rsij; apply/val_inj.
  by apply: uniqP rsij; rewrite ?inE.
- by apply/allP => g g_ffs; rewrite efg.
rewrite (@conjmx_eigenvalue _ _ _ rs`_i) ?eq_row_base ?row_base_free//.
set gs := map _ _; suff [P Punit Pgs] : codiagonalisable gs.
  exists P; rewrite /= ?Pgs ?andbT// sim_diagE.
  by rewrite conjmx_scalar ?is_diag_mx_scalar// row_free_unit.
apply: IHk; rewrite ?size_map/= ?ltnS//; split.
  apply/all_commP => _ _ /mapP[/= g gfs ->] /mapP[/= h hfs ->].
  rewrite -!conjmxM ?inE ?stable_row_base ?efg ?inE ?gfs ?hfs ?orbT//.
  by rewrite (all_commP _ fsC).
move=> _ /mapP[/= g gfs ->].
have: stable (row_base (eigenspace f rs`_i)) g.
  by rewrite stable_row_base efg// inE gfs orbT.
have := dffs g; rewrite inE gfs orbT => /(_ isT) [P Punit].
move=> /sim_diagPex[D /(simLR Punit)->] sePD.
have rfeP : row_free (row_base (eigenspace f rs`_i) *m invmx P).
  by rewrite /row_free mxrankMfree ?row_free_unit ?unitmx_inv// eq_row_base.
rewrite -conjMumx ?unitmx_inv ?row_base_free//.
apply/diagonalisable_conj_diag => //.
by rewrite stable_comp// stable_unit ?unitmx_inv.
Qed.

End Diag.
