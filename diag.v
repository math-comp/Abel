From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section All11.

Definition all11 (T : Type) (r : rel T) xs := all id [seq r x y | x <- xs, y <- xs].

Lemma all11_map (T T' : Type) (f : T' -> T) (r : rel T) xs :
  all11 r (map f xs) = all11 (relpre f r) xs.
Proof. by rewrite /all11 allpairs_mapl allpairs_mapr. Qed.

Lemma all11P {T : eqType} {r : rel T} {xs} :
  reflect {in xs &, forall x y, r x y} (all11 r xs).
Proof. exact: all_allpairsP. Qed.

Variable (T : Type) (r : rel T).
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

Lemma horner_mx_diag (K : fieldType) (n : nat) (d : 'rV[K]_n.+1) (p : {poly K}) :
  horner_mx (diag_mx d) p = diag_mx (map_mx (horner p) d).
Proof.
apply/matrixP => i j; rewrite !mxE.
elim/poly_ind: p => [|p c ihp]; first by rewrite rmorph0 horner0 mxE mul0rn.
rewrite !hornerE mulrnDl rmorphD rmorphM /= horner_mx_X horner_mx_C !mxE.
rewrite (bigD1 j)//= ihp mxE ?eqxx mulr1n -mulrnAl big1 ?addr0//.
  by case: (altP (i =P j)) => [->|]; rewrite /= !(mulr1n, addr0, mul0r).
by move=> k /negPf nkF; rewrite mxE nkF mulr0.
Qed.

Section Stability.
Variable (F : fieldType).

Lemma eqmx_stable m m' n (V : 'M[F]_(m,n)) (V' : 'M[F]_(m', n)) (f : 'M[F]_n) :
  (V :=: V')%MS -> stable V f = stable V' f.
Proof. by move=> eqVV'; rewrite (eqmxMr _ eqVV') eqVV'. Qed.

Section Preservation.

Variables (m m' n : nat) (V : 'M[F]_(m, n)) (f g : 'M[F]_n).

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
Hint Resolve commmxC.

Lemma commCmx (f : 'M[F]_n) (a : F) : GRing.comm a%:M f.
Proof. exact/commr_sym/commmxC. Qed.
Hint Resolve commCmx.

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
  (kermxpoly g (\prod_(i | P i) p_ i) == \sum_(i | P i) kermxpoly g (p_ i))%MS.
Proof.
move=> p_coprime; elim: index_enum (index_enum_uniq I).
  by rewrite !big_nil ?kermxpoly1 ?submx_refl//.
move=> j js /(_ _)/eqmxP ihjs /= /andP[jNjs js_uniq].
rewrite !big_cons; case: ifP => [Pj|PNj]; rewrite ?ihjs ?submx_refl//.
suff cjjs: coprimep (p_ j) (\prod_(i <- js | P i) p_ i).
  by rewrite !kermxpolyM// !(adds_eqmx (eqmx_refl _) (ihjs _)) ?submx_refl.
rewrite (@big_morph _ _ _ true andb) ?big_all_cond ?coprimep1//; last first.
  by move=> p q; rewrite coprimep_mulr.
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
rewrite -!(cap_eqmx (eqmx_refl _) (eqmxP (kermxpoly_prod g _)))//.
rewrite mxdirect_kermxpoly ?submx_refl//.
rewrite (@big_morph _ _ _ true andb) ?big_all_cond ?coprimep1//; last first.
  by move=> p q; rewrite coprimep_mulr.
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

Lemma horner_mx_pconj m n p (B : 'M[K]_(n.+1, m.+1)) (f : 'M_m.+1) :
   row_free B -> stable B f ->
   horner_mx (B *m f *m pinvmx B) p = B *m horner_mx f p *m pinvmx B.
Proof.
move=> B_free B_stab; elim/poly_ind: p => [|p c].
  by rewrite !rmorph0 mulmx0 mul0mx.
rewrite !(rmorphD, rmorphM)/= !(horner_mx_X, horner_mx_C) => ->.
rewrite [_ * _]mulmxA [_ *m (B *m _)]mulmxA mulmxKpV ?horner_mx_stable//.
apply: (row_free_inj B_free); rewrite [_ *m B]mulmxDl.
pose stableE := (stableD, stableM, stableC, horner_mx_stable).
by rewrite !mulmxKpV -?[B *m _ *m _]mulmxA ?stableE// mulmxDr -scalar_mxC.
Qed.

Lemma horner_mx_conj n p (B : 'M[K]_(n.+1)) (f : 'M_n.+1) :
   B \is a GRing.unit ->
   horner_mx (B *m f *m invmx B) p = B *m horner_mx f p *m invmx B.
Proof.
move=> B_unit; elim/poly_ind: p => [|p c].
  by rewrite !rmorph0 mulmx0 mul0mx.
rewrite !(rmorphD, rmorphM)/= !(horner_mx_X, horner_mx_C) => ->.
rewrite [_ * _]mulmxA [_ *m (B *m _)]mulmxA mulmxKV ?horner_mx_stable//.
apply: (canRL (mulmxK B_unit)); rewrite [_ *m B]mulmxDl.
pose stableE := (stableD, stableM, stableC, horner_mx_stable).
by rewrite !mulmxKV -?[B *m _ *m _]mulmxA ?stableE// mulmxDr -scalar_mxC.
Qed.

Lemma horner_mx_conjC n p (B : 'M[K]_(n.+1)) (f : 'M_n.+1) :
   B \is a GRing.unit ->
   horner_mx (invmx B *m f *m B) p = invmx B *m horner_mx f p *m B.
Proof.
move=> B_unit; rewrite -[X in _ *m X](invmxK B).
by rewrite horner_mx_conj ?invmxK ?unitmx_inv.
Qed.

Lemma eigenvalue_poly n a (f : 'M_n) :
  eigenvalue f a = eigenpoly f ('X - a%:P).
Proof. by rewrite /eigenpoly /eigenvalue eigenspace_poly. Qed.

End KernelLemma.

Section Restrict.
Variable (F : fieldType).

Definition restrict (n : nat) (V f : 'M[F]_n) : 'M_(\rank V) :=
  row_base V *m f *m (pinvmx (row_base V)).

Lemma restrictM (n : nat) (V : 'M[F]_n) : {in [pred f | stable V f] &,
   {morph restrict V : f g / f *m g}}.
Proof.
move=> f g; rewrite !inE => Vf Vg /=.
by rewrite /restrict 2!mulmxA mulmxA mulmxKpV ?stable_row_base.
Qed.

Variables (n : nat) (V : 'M[F]_n).

Implicit Types f : 'M[F]_n.

Lemma kermxpoly_restrict f m p (W : 'M_(m, \rank V)) : stable V f ->
  (W <= kermxpoly (restrict V f) p)%MS =
  (W *m row_base V <= kermxpoly f p)%MS.
Proof.
case: n V => [|n'] V' in f W *; first by move=> *; rewrite !thinmx0.
move=> fV; rewrite /restrict; have [] := (eq_row_base V', row_base_free V').
move: (\rank V') W (row_base V') => [|k] W B eq_B free_B.
  by move=> *; rewrite !thinmx0 ?mul0mx !sub0mx.
have fB : stable B f by rewrite (eqmx_stable _ eq_B).
apply/sub_kermxP/sub_kermxP; rewrite horner_mx_pconj//; last first.
  by move=> /(congr1 (mulmxr (pinvmx B)))/=; rewrite mul0mx -!mulmxA.
move=> /(congr1 (mulmxr B))/=; rewrite ![W *m _]mulmxA ?mul0mx mulmxKpV//.
by rewrite -mulmxA mulmx_sub// horner_mx_stable// eq_B (eqmxMr _ eq_B).
Qed.

Lemma eigenspace_restrict f m a (W : 'M_(m, \rank V)) : (V *m f <= V)%MS ->
  (W <= eigenspace (restrict V f) a)%MS =
  (W *m row_base V <= eigenspace f a)%MS.
Proof. by move=> fV; rewrite !eigenspace_poly kermxpoly_restrict. Qed.

Lemma eigenpoly_restrict f : stable V f ->
  {subset eigenpoly (restrict V f) <= eigenpoly f}.
Proof.
move=> fV a /eigenpolyP [x]; rewrite kermxpoly_restrict//.
move=> xV_le_fa x_neq0; apply/eigenpolyP.
by exists (x *m row_base V); rewrite ?mul_mx_rowfree_eq0 ?row_base_free.
Qed.

Lemma eigenvalue_restrict f : stable V f ->
  {subset eigenvalue (restrict V f) <= eigenvalue f}.
Proof.
by move=> fV a; rewrite -!topredE/= !eigenvalue_poly; exact: eigenpoly_restrict.
Qed.

End Restrict.

Section SimDiag.
Variable (F : fieldType).
Variable (n : nat).
Implicit Types (f g p : 'M[F]_n) (fs : seq 'M[F]_n) (d : 'rV[F]_n).

Definition sim p f g := p *m f == g *m p.

Lemma simP {p f g} : unitmx p ->
  reflect (f = invmx p *m g *m p) (sim p f g).
Proof.
move=> p_unit; rewrite -mulmxA; apply: (iffP eqP).
  by move=> /(canRL (mulKmx p_unit)).
by move=> /(canLR (mulKVmx p_unit)).
Qed.

Definition sim_diag p f :=
  [forall i, forall j, (i != j) ==> ((p *m f *m invmx p) i j == 0)].

Lemma sim_diagP p f : unitmx p ->
  reflect (exists d, sim p f (diag_mx d)) (sim_diag p f).
Proof.
move=> p_unit; apply: (iffP 'forall_'forall_implyP); last first.
  move=> [d /simP->]// i j /negPf ijF.
  by rewrite mulmxA mulmxK ?mulKVmx ?mxE ?ijF.
move=> /(_ _ _ _)/eqP fd; exists (\row_i (p *m f *m invmx p) i i); apply/eqP.
apply: (canRL (mulmxKV p_unit)); apply/matrixP => i j.
by rewrite 2![in RHS]mxE; case: (altP (i =P j)) => [->//|/fd->].
Qed.

End SimDiag.

(* Wrong *)
Lemma sim_diag_sum (F : fieldType) (n : nat) (f : 'M[F]_n)
      (I : finType) (V_ : I -> 'M_n) (V := (\sum_i V_ i)%MS) :
  (forall i, stable (V_ i) f) -> mxdirect V ->
  sim_diag V f = [forall i, sim_diag (restrict (V_ i) (V_ i)) (restrict (V_ i) f)].
Admitted.

Section Diag.
Variable (F : fieldType).
Variable (n' : nat). Let n := n'.+1.
Implicit Types (f g p : 'M[F]_n) (fs : seq 'M[F]_n) (d : 'rV[F]_n).

Definition all_comm fs := all11 (fun f g => f * g == g * f) fs.

Lemma all_commP fs :
  reflect {in fs &, forall f g, GRing.comm f g} (all_comm fs).
Proof. by apply: (iffP all11P) => fsP ? ? ? ?; apply/eqP/fsP. Qed.

Lemma all_comm1 f : all_comm [:: f]. Proof. exact: all111. Qed.

Lemma all_comm2P f g : reflect (GRing.comm f g) (all_comm [:: f; g]).
Proof. by apply: (iffP and4P) => [[_/eqP//]|->]; rewrite ?eqxx. Qed.

Lemma all_comm_cons f fs :
  all_comm (f :: fs) = all [pred g | f * g == g * f] fs && all_comm fs.
Proof. by rewrite [LHS]all11_cons. Qed.

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
Proof.
split=> [[/all_comm2P fg df dg]|[/all_comm2P fg dfg]].
  by split => [|h]; [exact: fg | rewrite !inE => /orP[]/eqP->].
by split; [exact: fg| | ]; apply: dfg; rewrite !inE ?eqxx ?orbT.
Qed.

(* Irrelevant *)
Lemma unitmx_restrict m (V : 'M[F]_m) : unitmx (restrict V V).
Admitted.
Hint Resolve unitmx_restrict.

Lemma diagonalisableP f :
  diagonalisable f <-> exists2 p, p \is a GRing.unit & sim_diag p f.
Proof.
split => [|[p p_unit /sim_diagP[//|d /(simP p_unit) f_eq]]]; last first.
  pose u := undup [seq d 0 i | i <- enum 'I_n].
  exists u; first by rewrite undup_uniq.
  apply: mxminpoly_min; rewrite f_eq horner_mx_conjC// horner_mx_diag/=.
  rewrite (_ : diag_mx (map_mx _ d) = 0) ?mulmx0 ?mul0mx//.
  apply/matrixP => i j; rewrite !mxE horner_prod.
  case: (altP (i =P j)) => [->|neq_ij//]; rewrite mulr1n.
  under eq_bigr => k _ do rewrite hornerXsubC.
  case: (@path.splitP _ u (d 0 j)); first by rewrite mem_undup map_f ?mem_enum.
  by move=> ? ?; rewrite -cats1 !big_cat/= big_cons big_nil subrr !(mul0r,mulr0).
move=> [rs rs_uniq frs].
exists (\sum_(i < size rs) eigenspace f rs`_i)%MS.
  under eq_bigr => i _ do rewrite eigenspace_poly.
  rewrite -row_full_unit -sub1mx -(eqmxP (kermxpoly_prod _ _)) ?kermxpoly_min//.
    by rewrite (big_nth 0) big_mkord in frs.
  by move=> i j _ _; rewrite coprimep_XsubC root_XsubC nth_uniq.
rewrite sim_diag_sum; last 2 first.
- by move=> i; rewrite comm_stable_eigenspace.
- rewrite mxdirect_sum_eigenspace// => i j _ _ rsij.
  by apply/val_inj; apply: uniqP rsij; rewrite ?inE.
apply/forallP => i; apply/sim_diagP => //.
exists (const_mx rs`_i); apply/simP => //.
rewrite diag_const_mx.
(* fail *)
Admitted.

Lemma codiagonalisable_cons f fs :
  codiagonalisable (f :: fs) <->
  [/\ all [pred g | f * g == g * f] fs, diagonalisable f & codiagonalisable fs].
Proof.
rewrite /codiagonalisable all_comm_cons; split => [[/andP[cffs cfs dffs]]|].
  by do ![split] => // [|g gfs]; apply: dffs; rewrite ?inE ?gfs ?eqxx ?orbT.
move=> [cffs df [cfs dfs]]; split; first by apply/andP; split.
by move=> g; rewrite inE => /predU1P[->//|/dfs].
Qed.

Lemma codiagonalisable0 : codiagonalisable [::]. Proof. by []. Qed.

Lemma codiagonalisableP fs : codiagonalisable fs <->
  exists2 p, p \is a GRing.unit & all (sim_diag p) fs.
Proof. Admitted.

End Diag.
