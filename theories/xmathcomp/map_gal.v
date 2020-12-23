From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field.
From mathcomp Require Import various char0.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

Section Prodv.
Import AEnd_FinGroup.

Variables (F0 : fieldType) (L : splittingFieldType F0).

Lemma galois_subW (E F : {subfield L}) : galois E F -> (E <= F)%VS.
Proof. by case/andP. Qed.

Lemma galois_normalW (E F : {subfield L}) : galois E F -> (normalField E F)%VS.
Proof. by case/and3P. Qed.

Lemma galois_separableW (E F : {subfield L}) : galois E F -> (separable E F)%VS.
Proof. by case/and3P. Qed.

Lemma normalField_refl (E : {subfield L}) : normalField E E.
Proof.
apply/forallP => /= u; apply/implyP; rewrite in_set.
by move=> /andP[/andP[_ /fixedSpace_limg->]].
Qed.
Hint Resolve normalField_refl : core.

Lemma galois_refl (E : {subfield L}) : galois E E.
Proof. by rewrite /galois subvv separable_refl normalField_refl. Qed.

Program Canonical prodv_aspace_law :=
  @Monoid.Law {subfield L} 1%AS (@prodv_aspace _ _) _ _ _.
Next Obligation. by move=> *; apply/val_inj/prodvA. Qed.
Next Obligation. by move=> *; apply/val_inj/prod1v. Qed.
Next Obligation. by move=> *; apply/val_inj/prodv1. Qed.

Program Canonical prodv_aspace_com_law :=
  @Monoid.ComLaw {subfield L} 1%AS prodv_aspace_law _.
Next Obligation. by move=> *; apply/val_inj/prodvC. Qed.

Lemma big_prodv_eq_aspace I (r : seq I) (P : {pred I}) (F : I -> {aspace L}) :
  (\big[@prodv _ _/1%VS]_(i <- r | P i) F i) =
  (\big[@prodv_aspace _ _/1%AS]_(i <- r | P i) F i).
Proof. by elim/big_rec2: _ => // i U V _ ->. Qed.

Lemma separable_prodvr (k K F : {subfield L}) : (k <= K)%VS -> (k <= F)%VS ->
  separable k K -> separable F (K * F).
Proof.
move=> kK kF sepkK; rewrite (eq_adjoin_separable_generator sepkK kK).
rewrite prodv_Fadjoinl/= (prodv_idPr _)//.
by rewrite -adjoin_separable_eq (separable_elementS kF)// separable_generatorP.
Qed.

Lemma normal_prodvr (k K F : {subfield L}) : (k <= K)%VS -> (k <= F)%VS ->
  normalField k K -> normalField F (K * F).
Proof.
move=> kK kF /(splitting_normalField kK) [p pk [rs p_eq krs]].
apply/splitting_normalField; rewrite ?field_subvMl//; exists p.
  by apply: polyOverS pk => x; apply: subvP.
exists rs => //; apply/eqP; rewrite eqEsubv; apply/andP; split.
  apply/Fadjoin_seqP; rewrite field_subvMl; split => //= r rrs.
  by apply: (subvP (field_subvMr _ _)); rewrite -krs seqv_sub_adjoin.
apply/prodvP => x y xK yF; rewrite rpredM//; last first.
  by rewrite (subvP (subv_adjoin_seq _ _))//.
by rewrite -krs in xK; apply: subvP xK; apply: adjoin_seqSl.
Qed.

Lemma galois_prodvr (k K F : {subfield L}) : (k <= F)%VS ->
  galois k K -> galois F (K * F).
Proof.
move=> kF /and3P[kK sep norm]; rewrite /galois field_subvMl/=.
by rewrite (separable_prodvr kK kF)// (normal_prodvr kK kF).
Qed.

(** N/A **)
Lemma capv_galois (k K F : {subfield L}) : (k <= F)%VS ->
  galois k K -> galois (K :&: F) K.
Proof.
move=> kF /splitting_galoisField [p [pk p_sep [rs p_eq krs]]].
have k_subKF: (k <= K :&: F)%VS.
  apply/subvP => x xk.
  by rewrite memv_cap (subvP kF)// -krs (subvP (subv_adjoin_seq _ _)).
apply/splitting_galoisField; exists p; split => //.
  by apply: polyOverS pk; apply/subvP.
exists rs => //; apply/eqP; rewrite -krs eqEsubv andbC adjoin_seqSl//=.
by apply/Fadjoin_seqP; split; [rewrite /= krs capvSl|apply: seqv_sub_adjoin].
Qed.

Lemma kAutEnormal (K E : {subfield L}) (f : 'End(L)) :
  (K <= E)%VS -> normalField K E -> kAut K E f = kHom K E f.
Proof.
move=> KE normalKE; rewrite kAutE; have [f_hom|]//= := boolP (kHom _ _ _).
apply/subvP => _/memv_imgP[x Ex ->].
have := kHom_to_gal _ normalKE f_hom; rewrite subvv KE => -[//|g gK ->//].
by rewrite memv_gal.
Qed.

Lemma fixedField_sub  (K E : {subfield L}) (A : {set gal_of E}) :
  galois K E -> (('Gal(E / K))%g \subset A) -> (fixedField A <= K)%VS.
Proof. by move=> /galois_fixedField{2}<- subA; apply: fixedFieldS. Qed.

Lemma galois_sub  (K E : {subfield L}) (A : {group gal_of E}) :
  galois K E -> (('Gal(E / K))%g \subset A) = (fixedField A <= K)%VS.
Proof.
move=> galKE; apply/idP/idP; first exact: fixedField_sub.
move=> /galS-/(_ E)/=/subset_trans->//.
by apply/subsetP => u; rewrite gal_fixedField.
Qed.

Lemma galois_eq  (K E : {subfield L}) (A : {group gal_of E}) :
  galois K E -> ('Gal(E / K)%g == A) = (fixedField A == K)%VS.
Proof.
move=> galKE; have KE := galois_subW galKE.
by rewrite eqEsubset eqEsubv galois_sub// galois_connection.
Qed.

Lemma galois_misom (k K F : {subfield L})
  (H := 'Gal((K * F) / F)%g) (H' := 'Gal (K / (K :&: F))%g) :
  galois k K -> (k <= F)%VS -> misom H H' (normalField_cast K).
Proof.
move=> gal_kK kF; have kK := galois_subW gal_kK.
have normal_kK := galois_normalW gal_kK.
have KF u : u \in H -> (u @: K <= K)%VS.
  move=> Hu; suff : kHom k K u by rewrite -kAutEnormal// kAutE => /andP[].
  by apply/kAHomP => x kx; rewrite (fixed_gal _ Hu) ?field_subvMl ?(subvP kF).
have r_H_morphic : morphic H (normalField_cast K).
  apply/morphicP => u v uH vH; apply/eqP/gal_eqP => x Kx.
  rewrite galM// [LHS]galK ?KF ?groupM//.
  rewrite 2?galK ?KF//; last by apply/(subvP (KF u uH)); rewrite memv_img.
  by rewrite galM//; apply: subvP Kx; apply: field_subvMr.
apply/misomP; exists r_H_morphic; apply/isomP; split.
  apply/subsetP => /= u ker_u; have Hu := dom_ker ker_u.
  apply/set1gP/eqP/gal_eqP => _ /memv_mulP[n [xs [ys [xsP ysP ->]]]].
  rewrite rmorph_sum/= gal_id; apply: eq_bigr => i _; rewrite rmorphM/=.
  have [xiK yiK] := (allP xsP _ (mem_tnth i _), allP ysP _ (mem_tnth i _)).
  have /eqP/gal_eqP/(_ _ xiK) := mker ker_u.
  rewrite /normalField_cast galK ?KF// => ->; rewrite gal_id.
  by rewrite (fixed_gal _ Hu)// field_subvMl.
apply/eqP; rewrite eq_sym galois_eq ?(capv_galois kF gal_kK)//.
rewrite eqEsubv; apply/andP; split; apply/subvP => x; last first.
  rewrite memv_cap => /andP[Kx Fx].
  apply/fixedFieldP => // _ /morphimP[/= v Hv _ ->].
  rewrite morphmE /normalField_cast galK// ?KF//.
  by rewrite (fixed_gal _ Hv)// field_subvMl.
move=> /mem_fixedFieldP[Kx xP]; rewrite memv_cap Kx/=.
rewrite -(galois_fixedField (galois_prodvr kF gal_kK)).
apply/fixedFieldP; first by rewrite -[x]mulr1 memv_mul// rpred1.
move=> u Hu; have := xP (normalField_cast _ u).
by rewrite /normalField_cast galK ?KF//; apply; apply/morphimP; exists u.
Qed.

Lemma galois_isog (k K F : {subfield L})
  (H := 'Gal((K * F) / F)%g) (H' := 'Gal (K / (K :&: F))%g) :
  galois k K -> (k <= F)%VS -> H \isog H'.
Proof. by move=> galkK /(galois_misom galkK) /misom_isog. Qed.

Lemma subv_big_prodv_seq I r (P : {pred I}) (k : {subfield L})
  (K : I -> {subfield L}) :
  (forall i, P i -> (k <= K i)%VS) ->
  ~~ nilp [seq i <- r | P i] ->
  (k <= \big[@prodv _ _/1]_(i <- r | P i) K i)%VS.
Proof.
move=> normkK; elim: r => [|i r IHr]; rewrite !(big_nil, big_cons)//=.
case: ifP IHr => //= Pi; rewrite -big_filter.
have [->|_ IHr]//= := altP nilP; first by rewrite big_nil prodv1 normkK.
by rewrite -[X in (X <= _)%VS]prodv_id prodvS ?IHr ?normkK.
Qed.

Lemma subv_big_prodv (I : finType) (D : {pred I}) (k : {subfield L})
  (K : I -> {subfield L}) :
  (#|D| > 0)%N -> (forall i, D i -> k <= K i)%VS ->
  (k <= \big[@prodv _ _/1]_(i in D) K i)%VS.
Proof.
move=> D_gt0 DK; apply: subv_big_prodv_seq => //.
by rewrite /nilp size_filter -sum1_count sum1_card -lt0n.
Qed.

Lemma normal_prodv (k K1 K2 : {subfield L}) :
  normalField k K1 -> normalField k K2 -> normalField k (K1 * K2).
Proof.
move=> /'forall_implyP/(_ _ _)/eqP endK1  /'forall_implyP/(_ _ _)/eqP endK2.
by apply/'forall_implyP => s s_end; rewrite aimgM endK1// endK2.
Qed.

Lemma normal_big_prodv I r (P : {pred I}) (k : {subfield L})
    (K : I -> {subfield L}) :
    (forall i, P i -> normalField k (K i)) ->
  normalField k (\big[@prodv _ _/1%VS]_(i <- r | P i) K i).
Proof.
move=> normkK; elim: r => [|i r IHr]; rewrite !(big_nil, big_cons).
  apply/normalFieldP => a a1; exists [:: a]; rewrite /= ?a1//.
  rewrite big_cons big_nil mulr1; apply: minPoly_XsubC.
  by apply: subvP a1; rewrite sub1v.
rewrite big_prodv_eq_aspace in IHr *; case: ifP => // Pi.
by rewrite normal_prodv// normkK.
Qed.

Lemma separable_prodv (k K1 K2 : {subfield L}) : (k <= K1)%VS -> (k <= K2)%VS ->
  separable k K1 -> separable k K2 -> separable k (K1 * K2).
Proof.
move=> kK1 kK2 sepK1 sepK2; apply: separable_trans sepK1 _ => /=.
by rewrite prodvC (separable_prodvr kK2).
Qed.

Lemma separable_big_prodv_seq I r (P : {pred I}) (k : {subfield L})
  (K : I -> {subfield L}) :
  (forall i, P i -> (k <= K i)%VS) ->
  (forall i, P i -> separable k (K i)) ->
  ~~ nilp [seq i <- r | P i] ->
  separable k (\big[@prodv _ _/1%VS]_(i <- r | P i) K i).
Proof.
move=> kK sepkK; elim: r => [|i r]; rewrite !(big_nil, big_cons)//=.
case: ifP => // Pi; rewrite -big_filter/=; have /(_ r) := subv_big_prodv_seq kK.
have [->|_]//= := altP nilP; first by rewrite big_nil prodv1 sepkK.
move=> subkK sepkbK.
by rewrite big_prodv_eq_aspace separable_prodv ?kK ?sepkK//
          -big_prodv_eq_aspace ?sepkbK// big_filter ?subkK//.
Qed.

Lemma separable_big_prodv (I : finType) (D : {pred I}) (k : {subfield L})
  (K : I -> {subfield L}) :
    (#|D| > 0)%N ->
    (forall i, D i -> k <= K i)%VS ->
    (forall i, D i -> separable k (K i)) ->
  separable k (\big[@prodv _ _/1%VS]_(i in D) K i).
Proof.
move=> D_gt0 DK sepkK; apply: separable_big_prodv_seq => //.
by rewrite /nilp size_filter -sum1_count sum1_card -lt0n.
Qed.

Lemma galois_prodv (k K1 K2 : {subfield L}) :
  galois k K1 -> galois k K2 -> galois k (K1 * K2).
Proof.
rewrite /galois => /and3P[kK1 sepK1 normK1] /and3P[kK2 sepK2 normK2].
by rewrite -[X in (X <= _)%VS]prodv_id prodvS//= separable_prodv// normal_prodv.
Qed.

Lemma galois_big_prodv_seq I r (P : {pred I}) (k : {subfield L})
  (K : I -> {subfield L}) :
  (forall i, P i -> galois k (K i)) ->
  ~~ nilp [seq i <- r | P i] ->
  galois k (\big[@prodv _ _/1%VS]_(i <- r | P i) K i).
Proof.
move=> galkK brP; pose gW := (galois_subW, galois_normalW, galois_separableW).
pose bpv := (subv_big_prodv_seq, separable_big_prodv_seq, normal_big_prodv).
by rewrite /galois !bpv// => i Pi; rewrite gW ?galkK.
Qed.

Lemma galois_big_prodv (I : finType) (D : {pred I}) (k : {subfield L})
    (K : I -> {subfield L}) :
    (#|D| > 0)%N -> (forall i, D i -> galois k (K i)) ->
  galois k (\big[@prodv _ _/1%VS]_(i in D) K i).
Proof.
move=> D_gt0 galkK; apply: galois_big_prodv_seq => //.
by rewrite /nilp size_filter -sum1_count sum1_card -lt0n.
Qed.

Definition gal_big_prodv_cast_subdef {n} {K : 'I_n -> {subfield L}}
   (s : gal_of (\big[@prodv_aspace _ _/1%AS]_(i < n) K i)) :
    {dffun forall i, gal_of (K i)} :=
  [ffun i => normalField_cast (K i) s].

Lemma gal_big_prodv_cast_morphic n (k : {subfield L}) (K : 'I_n -> {subfield L}) :
  (forall i, galois k (K i)) ->
  morphic 'Gal((\big[@prodv_aspace _ _/1%AS]_(i < n) K i)%VS / k)
          gal_big_prodv_cast_subdef.
Proof.
rewrite /gal_big_prodv_cast_subdef => galK.
apply/'forall_implyP => -[s t]; rewrite inE => /andP[sG tG].
apply/eqP/ffunP => i; rewrite !ffunE/=.
have n_gt0 : (n > 0)%N by case: {+}n i => -[].
rewrite (@normalField_castM _ _ _ k) ?galois_normalW//.
by rewrite [(k <= _)%VS]galois_subW//= (bigD1 i)//= field_subvMr.
Qed.

Definition gal_big_prodv_cast n (k : {subfield L}) (K : 'I_n -> {subfield L})
  (galK : forall i, galois k (K i)) :=
  [morphism of morphm (gal_big_prodv_cast_morphic galK)].

Lemma gal_big_prodv_cast_inj n (k : {subfield L}) (K : 'I_n -> {subfield L})
  (galK : forall i, galois k (K i)) :
  ('injm (gal_big_prodv_cast galK))%g.
Proof.
apply/subsetP => /= s s_ker; rewrite inE; apply/gal_eqP => x xK.
suff: x \in fixedField [set s].
  by move=> /mem_fixedFieldP [_ /(_ s)]; rewrite inE gal_id; apply.
apply/subvP: x xK; rewrite /= -[X in (X <= _)%VS]big_prodv_eq_aspace.
apply/big_prod_subfieldP => u uK /=; rewrite rpred_prod// => i _.
apply/fixedFieldP; first by rewrite (bigD1 i)// -[u i]mulr1 memv_mul ?rpred1 ?uK.
move=> s'; rewrite inE => /eqP->{s'}; have /mker := s_ker.
rewrite /gal_big_prodv_cast/= morphmE /gal_big_prodv_cast_subdef.
move=> /ffunP-/(_ i); rewrite !ffunE.
move=> /eqP/gal_eqP/(_ _ (uK _ _))-/(_ isT); rewrite gal_id.
rewrite (@normalField_cast_eq _ _ _ k) ?uK ?galois_normalW ?(dom_ker s_ker)//=.
by rewrite [(k <= _)%VS]galois_subW//= (bigD1 i)//= field_subvMr.
Qed.

Lemma img_gal_big_prodv_cast_sub n (k : {subfield L}) (K : 'I_n -> {subfield L})
  (galK : forall i, galois k (K i))
  (E := (\big[@prodv_aspace _ _/1%AS]_(i < n) K i)%AS)
  (G := 'Gal(E / k)%g):
  (gal_big_prodv_cast galK @* G \subset setXn (fun i => 'Gal(K i / k)))%g.
Proof.
case: n => [|n] in K galK E G *.
  rewrite setX0; apply/subsetP => /= x _; rewrite !inE.
  by apply/eqP/ffunP => -[].
apply/subsetP => /= x; rewrite !inE morphimEdom => /imsetP[s sG ->]/=.
apply/forallP => i/=; rewrite morphmE/= ffunE/=.
rewrite -(@normalField_img _ _ E)// ?galois_normalW//.
- by rewrite (galois_subW (galK _))//= /E (bigD1 i)//= field_subvMr.
- by move=> ? ?/=; rewrite mem_morphim//.
- by rewrite /E/= -big_prodv_eq_aspace galois_big_prodv//= card_ord.
Qed.

End Prodv.

Lemma dvdp_minpoly_Xn_subn (F0 : fieldType) (L : fieldExtType F0)
  (E : {subfield L}) (n : nat) (x : L) :
  (x ^+ n)%R \in E -> minPoly E x %| ('X^n - (x ^+ n)%:P).
Proof.
move=> xnE; have [->|n_gt0] := posnP n; first by rewrite !expr0 subrr dvdp0.
by rewrite minPoly_dvdp /root ?poly_XnsubC_over// !hornerE hornerXn subrr.
Qed.

Lemma lker0_img_cap (K : fieldType) (aT rT : vectType K) (f : 'Hom(aT, rT))
    (U V : {vspace aT}) : lker f == 0%VS ->
  (f @: (U :&: V) = f @: U :&: f @: V)%VS.
Proof.
move=> kf0; apply/eqP; rewrite eqEsubv limg_cap/=; apply/subvP => x.
rewrite memv_cap => /andP[/memv_imgP[u uU ->]] /memv_imgP[v vV].
by move=> /(lker0P kf0) eq_uv; rewrite memv_img// memv_cap uU eq_uv vV.
Qed.

Lemma aimg_cap (K : fieldType) (aT rT : fieldExtType K) (f : 'AHom(aT, rT))
    (U V : {vspace aT}) : (f @: (U :&: V) = f @: U :&: f @: V)%VS.
Proof. exact/lker0_img_cap/AHom_lker0. Qed.

Section map_hom.
Variables (F0 : fieldType) (L L' : splittingFieldType F0).
Variable (iota : 'Hom(L, L')).

Definition map_hom (f : 'End(L)) := (iota \o f \o iota^-1)%VF.

Lemma map_hom_is_linear : linear map_hom.
Proof.
move=> /= k a b; apply/lfunP => x; rewrite /map_hom.
by rewrite !(comp_lfunE, add_lfunE, scale_lfunE) linearP.
Qed.
Canonical map_hom_linear := Linear map_hom_is_linear.

Lemma lker0_map_homC (f : 'End(L)) : lker iota == 0%VS ->
  (map_hom f \o iota = iota \o f)%VF.
Proof. by move=> kiota0; apply/lfunP => x; rewrite !comp_lfunE lker0_lfunK. Qed.

Lemma lker0_map_homE (f : 'End(L)) (x : L) : lker iota == 0%VS ->
  map_hom f (iota x) = iota (f x).
Proof. by rewrite !comp_lfunE => /lker0_lfunK->. Qed.

End map_hom.

Section map_ahom.
Variables (F0 : fieldType) (L L' : splittingFieldType F0).
Variable (iota : 'AHom(L, L')).

Lemma map_hom_algE (f : 'End(L)) (x : L) :
  map_hom iota f (iota x) = iota (f x).
Proof. by rewrite lker0_map_homE// AHom_lker0. Qed.

Lemma map_hom_algC (f : 'End(L)) : (map_hom iota f \o iota = iota \o f)%VF.
Proof. by rewrite lker0_map_homC// AHom_lker0. Qed.

Definition ahom_inj := (lker0P (AHom_lker0 iota)).

Lemma map_ahom_in (f : 'End(L)) (E : {vspace L}) :
  ahom_in (iota @: E) (map_hom iota f) = ahom_in E f.
Proof.
apply/ahom_inP/ahom_inP => -[mfM mf1]; last first.
  split; last by rewrite -(rmorph1 [rmorphism of iota]) map_hom_algE mf1.
  move=> _ _ /memv_imgP[u uE ->] /memv_imgP[v vE ->].
  by rewrite !(map_hom_algE, =^~rmorphM)/= mfM.
split=> [x y xE yE|]; last first.
  have : map_hom iota f (iota 1) = iota 1 by rewrite rmorph1.
  by rewrite map_hom_algE => /ahom_inj.
have := mfM _ _ (memv_img iota xE) (memv_img iota yE).
by rewrite !(map_hom_algE, =^~rmorphM)/= => /ahom_inj.
Qed.

Lemma map_ahom_subproof (f : 'AEnd(L)) :
   {g : 'AEnd(L') | (g \o iota)%VF = (iota \o f)%VF }.
Proof.
have : kHom 1%VS (iota @: {: L})%VS (map_hom iota f).
  by rewrite k1HomE map_ahom_in ahomWin.
move=> /kHom_to_AEnd[g gP]; exists g.
apply/lfunP => x; rewrite !comp_lfunE/=.
by rewrite -map_hom_algE gP ?memv_img// memvf.
Qed.

Import AEnd_FinGroup.

Definition map_ahom (f : 'AEnd(L)) := projT1 (map_ahom_subproof f).

Lemma map_ahomC (f : 'AEnd(L)) :
   (map_ahom f \o iota)%VF = (iota \o f)%VF.
Proof. by rewrite /map_ahom; case: map_ahom_subproof. Qed.

Lemma map_ahomE (f : 'AEnd(L)) x : map_ahom f (iota x) = iota (f x).
Proof. by rewrite -!comp_lfunE map_ahomC. Qed.

Lemma limg_map_ahom (f : 'AEnd(L))  (E : {vspace L}) :
  (map_ahom f @: (iota @: E))%VS = (iota @: (f @: E))%VS.
Proof. by rewrite -limg_comp map_ahomC limg_comp. Qed.

End map_ahom.

Arguments ahom_inj {F0 L L'}.

Section gal_kAEnd.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Import AEnd_FinGroup.

Lemma kAEndSl (k K F : {subfield L}) : (k <= K)%VS -> (kAEnd K F \subset kAEnd k F).
Proof. by move=> EK; apply/subsetP => x; rewrite !inE; apply: kAutS. Qed.

Lemma ker_gal (E : {subfield L}) : ('ker (gal E))%g = kAEndf E.
Proof.
apply/setP => g; rewrite !inE kAut1E/= !kAutE subvf andbT subfield_closed.
apply/andP/idP => [[gE /gal_eqP galg1]|/kAHomP g_id].
  by apply/kAHomP => x xE; have := galg1 _ xE; rewrite gal_id galK// => ->.
have gE : (g @: E <= E)%VS by apply/subvP => _/memv_imgP[x ? ->]; rewrite g_id.
by split=> //; apply/gal_eqP => x xE; rewrite gal_id galK// g_id.
Qed.

Lemma kAEnd_split (K E : {subfield L}) : kAEnd K E = kAEnd 1 E :&: kAEndf K.
Proof.
apply/setP => f; rewrite !inE kAut1E !kAutE subvf andbT andbC.
by case fE : (f @: E <= E)%VS => //=; apply/kAHomP/kAHomP.
Qed.

Lemma gal_kAEndf (K E : {subfield L}) : (K <= E)%VS ->
   (gal E @* kAEndf K)%g = (gal E @* kAEnd K E)%g :> {set _}.
Proof.
move=> KE; rewrite kAEnd_split morphimIG ?ker_gal ?kAEndSl// (setIidPr _)//=.
by rewrite (subset_trans (morphim_sub _ _))//= morphimS// subfield_closed.
Qed.

End gal_kAEnd.

Section map_gal.
Variables (F0 : fieldType) (L L' : splittingFieldType F0).
Variable (iota : 'AHom(L, L')).
Variables (E : {subfield L}).
Let iota_ker0 := AHom_lker0 iota.

Definition map_gal (g : gal_of E) :=
  gal (iota @: E) (projT1 (map_ahom_subproof iota g)).

Lemma map_galE (g : gal_of E) :
  {in E, forall x, map_gal g (iota x) = iota (g x)}.
Proof.
rewrite /map_gal; case: map_ahom_subproof => g' g'E /=.
move=> x xE /=; rewrite galK ?memv_img ?memvf//=.
  by rewrite -!comp_lfunE g'E//.
by rewrite -limg_comp g'E limg_comp limg_gal.
Qed.

Definition map_gal_is_morphism : {in setT &,
   {morph map_gal : x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move=> /= f g _ _; apply/eqP/gal_eqP => _/memv_imgP[x xE ->].
rewrite galM ?memv_img// 3?map_galE// ?galM//.
by suff: f x \in (f @: E)%VS; by [rewrite memv_img|rewrite limg_gal].
Qed.
Canonical map_gal_morphism := Morphism map_gal_is_morphism.

Import AEnd_FinGroup.
Lemma map_galK :
  {in kAEnd 1 E, map_gal \o gal E =1 gal (iota @: E) \o map_ahom iota }.
Proof.
move=> s; rewrite inE kAut1E => sE.
apply/eqP/gal_eqP => _/memv_imgP[x xE ->]/=.
rewrite map_galE// !galK ?memv_img ?map_ahomE//.
by rewrite -limg_comp map_ahomC limg_comp limgS.
Qed.

Lemma map_gal_inj : ('injm map_gal)%g.
Proof.
apply/injmP => /= f g _ _ eq_fg; apply/eqP/gal_eqP => x xE.
have /eqP/gal_eqP/(_ _ (memv_img iota xE)) := eq_fg.
by rewrite !map_galE// => /ahom_inj.
Qed.

Lemma img_map_gal (K : {subfield L}) :
   (map_gal @* 'Gal(E / K))%g = 'Gal(iota @: E / iota @: K)%g.
Proof.
wlog subKE : K / (K <= E)%VS => [hwlog|].
  by rewrite gal_cap hwlog ?capvSr// aimg_cap -gal_cap.
rewrite /'Gal(_ / _)%g -aimg_cap !genGid/= (capv_idPl _)//.
rewrite -!gal_kAEndf ?limgS// -morphim_comp/=.
apply/setP => u; apply/imsetP/imsetP => /= [[f faut ->]|[f' f'aut ->]] {u}.
  have := faut; rewrite !inE !kAut1E !kAutE/= !subfield_closed !subvf !andbT.
  move=> /andP[fE /kAHomP fK].
  exists (map_ahom iota f).
    rewrite !inE !kAut1E !kAutE/= !subvf !andbT limg_map_ahom limgS//=.
    by apply/kAHomP => _/memv_imgP[x xK ->]; rewrite map_ahomE ?fK.
  apply/eqP/gal_eqP => _/memv_imgP[x xK ->].
  by rewrite map_galE// !galK ?memv_img ?limg_map_ahom ?map_ahomE// limg_ker0//.
have := f'aut; rewrite !inE !kAut1E !kAutE/= !subvf !andbT.
have -> : agenv (iota @: E) = (iota @: E)%VS by rewrite subfield_closed.
move=> /andP[f'E /kAHomP f'K].
have f'iota x : x \in E -> f' (iota x) \in limg iota.
  move=> xE; have: f' (iota x) \in (f' @: (iota @: E))%VS.
    by rewrite -comp_lfunE -!limg_comp memv_img.
  by apply: subvP; rewrite (subv_trans f'E)// limgS ?subvf//.
have /kHom_to_AEnd[f eqf] : kHom K E (iota^-1 \o f' \o iota)%VF.
  apply/kHomP; split => //=; last first.
    by move=> x xK; rewrite !comp_lfunE f'K ?lker0_lfunK ?memv_img.
  move=> x y xE yE; rewrite !comp_lfunE.
  apply: (ahom_inj iota); rewrite [in RHS]rmorphM/=.
  by rewrite !limg_lfunVK ?f'iota ?rpredM// !rmorphM.
have fE : (f @: E <= E)%VS.
  apply/subvP => _/memv_imgP[x xK ->]/=; rewrite -eqf// !comp_lfunE.
  have: f' (iota x) \in (iota @: E)%VS.
    by rewrite (subvP f'E)// -limg_comp -comp_lfunE memv_img.
  by move=> /memv_imgP[y yE ->]; rewrite lker0_lfunK.
exists f; rewrite ?inE ?kAut1E ?kAutE/= ?subfield_closed ?subvf ?andbT ?fE.
  apply/kAHomP => x xK; rewrite -eqf ?(subvP subKE)// !comp_lfunE.
  by rewrite f'K ?memv_img// lker0_lfunK.
apply/eqP/gal_eqP => _/memv_imgP[x xE ->]; rewrite map_galE//.
by rewrite !galK ?memv_img// -eqf//= !comp_lfunE limg_lfunVK// f'iota.
Qed.

Lemma reflexiveW T (r : rel T) : reflexive r -> forall x y, x = y -> r x y.
Proof. by move=> ? ? ? ->. Qed.

Lemma galois_aimg (K : {subfield L}) :
   galois (iota @: K) (iota @: E) = galois K E.
Proof.
apply/splitting_galoisField/splitting_galoisField => -[p [pK sep [rs peq Krs]]].
  have /polyOverP/(_ _)/memv_imgP/sig2_eqW-/all_sig2[f fK pf] := pK.
  pose q := \poly_(i < size p) f i.
  have pE : p = map_poly iota q :> {poly _}.
    rewrite -[p]coefK /q !poly_def rmorph_sum/=.
    by under [RHS]eq_bigr do rewrite map_polyZ/= map_polyXn -pf.
  exists q; split; first exact/polyOver_poly.
    by have := sep; rewrite pE separable_map.
  have := @seqv_sub_adjoin _ _ (iota @: K) rs; rewrite Krs => rsE.
  pose rs' := map iota^-1%VF rs.
  have iotaVK : {in rs, forall r, iota (iota^-1%VF r) = r}.
    move=> r /rsE rE; rewrite limg_lfunVK//.
    by apply: subvP rE; rewrite limgS ?subvf.
  exists (map iota^-1%VF rs).
    rewrite big_map -(eqp_map [rmorphism of iota])/= -pE rmorph_prod/=.
    rewrite (eqp_trans peq)// (reflexiveW (@eqpxx _))//.
    rewrite big_seq_cond [RHS]big_seq_cond.
    apply: eq_bigr => r; rewrite andbT => rrs.
    by rewrite rmorphB/= map_polyX map_polyC/= iotaVK.
  apply/eqP; rewrite -(eq_limg_ker0 _ _ iota_ker0).
  rewrite aimg_adjoin_seq -map_comp.
  by have /eq_in_map-> := iotaVK; rewrite map_id Krs.
exists (map_poly iota p); rewrite separable_map sep; split=> //.
  by apply/polyOverP => i; rewrite coef_map/= ?memv_img// (polyOverP pK).
exists (map iota rs); last by rewrite /= -aimg_adjoin_seq Krs.
rewrite big_map; have := peq; rewrite -(eqp_map [rmorphism of iota]).
move=> /eqp_trans->//=; rewrite (big_morph _ (rmorphM _) (rmorph1 _))/=.
by under eq_bigr do rewrite rmorphB/= map_polyX map_polyC/=; rewrite eqpxx.
Qed.

End map_gal.

Lemma sub_aimgP (F0 : fieldType) (L L' : splittingFieldType F0)
  (iota : 'AHom(L, L')) (F : {subfield L'}) :
  reflect (exists E : {subfield L}, (iota @: E)%VS = F) (F <= iota @: fullv)%VS.
Proof.
apply: (iffP idP) => [Fiota|[E <-]]; last by rewrite limgS ?subvf.
suff F_is_aspace : is_aspace (iota @^-1: F)%VS.
  by exists (ASpace F_is_aspace); apply/eqP; rewrite eqEsubv/= lpreimK ?subvv.
apply/andP => /=; split.
  by apply/has_algid1; rewrite -memv_preim rmorph1 rpred1.
by apply/prodvP => u v; rewrite -!memv_preim => uF vF; rewrite rmorphM rpredM.
Qed.

Import AEnd_FinGroup.

Section minGalois.
Variable (F0 : fieldType) (L : splittingFieldType F0).

Definition minGalois (U V : {vspace L}) :=
  (\big[@prodv _ _/1]_(s in kAEndf U) (s @: (U * V)))%VS.

Definition minGalois_is_aspace (E F : {subfield L}) : is_aspace (minGalois E F).
Proof.
by rewrite /minGalois big_prodv_eq_aspace; case: (\big[_/_]_(_ in _) _).
Qed.
Canonical minGalois_aspace (E F : {subfield L}) :=
  ASpace (minGalois_is_aspace E F).

Let prodv_sub_minGalois (E F : {subfield L}) : (E * F <= minGalois E F)%VS.
Proof.
rewrite /minGalois (bigD1 \1%AF) ?group1//= lim1g.
by rewrite big_prodv_eq_aspace field_subvMr.
Qed.

Lemma sub_minGalois (E F : {subfield L}) : (F <= minGalois E F)%VS.
Proof. exact: subv_trans (field_subvMl _ _) (prodv_sub_minGalois _ _). Qed.
Hint Resolve sub_minGalois : core.

(* replace by separability *)
Hypothesis charL : [char L] =i pred0.

Lemma minGalois_galois (E F : {subfield L}) : galois E (minGalois E F).
Proof.
apply: char0_galois => //=.
  exact: subv_trans (field_subvMr _ _) (prodv_sub_minGalois _ _).
apply/'forall_implyP => /= s s_end; apply/eqP.
rewrite /minGalois (big_morph _ (aimgM _) (aimg1 _)).
under eq_bigr => s' do rewrite -limg_comp.
under eq_bigr => s' do have -> : (s \o s')%VF = 'R%act s' s by [].
have /(reindex_astabs 'R _) : s \in ('N(kAEndf E | 'R))%g by rewrite astabsR/=.
by move/(_ _ _ _ (fun i => i @: (E * F))%AS); rewrite !big_prodv_eq_aspace => <-.
Qed.
Hint Resolve minGalois_galois : core.

Lemma minGalois_min (E F K' : {subfield L}) : (F <= K')%VS -> galois E K' ->
  (minGalois E F <= K')%VS.
Proof.
move=> FK' /and3P[EK' sepEK' /'forall_implyP/(_ _ _)/eqP/= sK'].
apply/big_prod_subfieldP => /= u uEF; rewrite rpred_prod// => s s_end.
by apply/subvP: (uEF s s_end); rewrite -(sK' _ s_end) limgS// prodv_sub.
Qed.

Lemma minGalois_id (E F : {subfield L}) : galois E F -> minGalois E F = F.
Proof.
by move=> gEF; apply/eqP; rewrite eqEsubv/= sub_minGalois minGalois_min.
Qed.

Definition solvable_ext (E F : {vspace L}) :=
  solvable 'Gal(minGalois E F / E).

Lemma solvable_extP (E F : {subfield L}) :
  reflect (exists K : {subfield L},
            [&& (F <= K)%VS, galois E K & solvable 'Gal(K / E)])
          (solvable_ext E F).
Proof.
apply: (iffP idP) => [|[K /and3P[FK galEK solEK]]].
  by exists [aspace of minGalois E F]; rewrite minGalois_galois// sub_minGalois.
have MsubK := minGalois_min FK galEK; rewrite /solvable_ext.
have /and3P [EsubM _ EnormM] := (minGalois_galois E F).
by rewrite -(isog_sol (normalField_isog galEK _ _)) ?EsubM// quotient_sol.
Qed.

Lemma solvable_prodv (k E F : {subfield L}) :
  (k <= F)%VS -> solvable_ext k E -> solvable_ext F (E * F)%AS.
Proof.
move=> kF solkE; apply/solvable_extP => //.
exists ([aspace of minGalois k E] * F)%AS.
rewrite (@galois_prodvr _ _ k) ?minGalois_galois ?prodvSl ?sub_minGalois//=.
rewrite (isog_sol (galois_isog (minGalois_galois _ _) _))//.
rewrite (solvableS _ solkE)// galS// subv_cap.
by rewrite kF galois_subW ?minGalois_galois.
Qed.

Import AEnd_FinGroup.

Lemma solvable_ext_trans (F k E : {subfield L}) : (k <= F <= E)%VS ->
  solvable_ext k F -> solvable_ext F E -> solvable_ext k E.
Proof.
move=> /andP[kF FE] solkF solFE.
have /solvable_extP [/= l /and3P[EKl galKl subl]] :=
  solvable_prodv (sub_minGalois k F) solFE.
apply/solvable_extP; exists [aspace of minGalois k l] => /=.
have galkK := minGalois_galois k F.
set K := minGalois k F in galkK galKl subl EKl *.
rewrite minGalois_galois// (subv_trans _ (sub_minGalois _ _))/=; last first.
  by rewrite (subv_trans _ EKl)//= field_subvMr.
have /and3P [kK _ normkK] := galkK.
have /and3P [Kl _ normKl] := galKl.
have KM : (K <= minGalois k l)%VS := subv_trans Kl (sub_minGalois _ _).
have kKM : (k <= K <= minGalois k l)%VS by rewrite kK KM.
rewrite (series_sol (normalField_normal _ normkK))//= -/K.
rewrite (isog_sol (normalField_isog _ _ _)) ?minGalois_galois//=.
rewrite [X in _ && X]solkF andbT /minGalois.
have kl : (k <= l)%VS := subv_trans (galois_subW galkK) (galois_subW galKl).
under eq_bigr do rewrite /= (prodv_idPr _)//.
rewrite big_prodv_eq_aspace big_enum_val/=.
have /'forall_implyP/(_ _ _)/eqP/= sK := galois_normalW galkK.
have gKl (i : 'I_#|kAEndf k|) : galois K (enum_val i @: l)%AS.
  move: (enum_val _) (enum_valP i) => s s_end.
  have /splitting_galoisField[/= p [/polyOverP pK p_sep [rs p_eq <-]]] := galKl.
  apply/splitting_galoisField; exists (map_poly s p); split => //=.
  - by apply/polyOverP => j; rewrite coef_map/= -(sK _ s_end) memv_img.
  - by rewrite separable_map.
  - exists (map s rs); last by rewrite aimg_adjoin_seq sK.
    have := p_eq; rewrite -(eqp_map [rmorphism of s])/= => /eqp_trans->//.
    rewrite rmorph_prod/= big_map/=.
    by under eq_bigr do rewrite rmorphB/= map_polyX map_polyC/=; rewrite eqpxx.
rewrite -(injm_sol (gal_big_prodv_cast_inj gKl))//.
rewrite (solvableS (img_gal_big_prodv_cast_sub _)) ?sol_setXn// => i /=.
move: (enum_val _) (enum_valP i) => s s_end; rewrite -(sK _ s_end).
by rewrite -img_map_gal/= morphim_sol.
Qed.

End minGalois.

Lemma aimg_minGalois (F0 : fieldType) (L L' : splittingFieldType F0)
  (iota : 'AHom(L, L')) (K E : {subfield L}) :
  [char F0] =i pred0 -> (* could be removed if the proof were structural
                           or using separability in minGalois_galois instead *)
  (iota @: minGalois K E)%VS = minGalois (iota @: K) (iota @: E).
Proof.
move=> charF0; set G' := minGalois (iota @: _) _; have iK0 := AHom_lker0 iota.
have G'sub : (G' <= iota @: minGalois K E)%VS.
  rewrite minGalois_min ?limgS/= ?sub_minGalois//.
  by rewrite galois_aimg ?minGalois_galois// => n; rewrite char_lalg charF0.
apply/eqP; rewrite eqEsubv G'sub /G'.
have /sub_aimgP[G GE] : (G' <= iota @: fullv)%VS.
  by apply: subv_trans G'sub _; rewrite limgS ?subvf.
rewrite -GE limgS// minGalois_min//.
  by rewrite -(limg_ker0 _ _ iK0) GE/= sub_minGalois.
rewrite -(galois_aimg iota) GE minGalois_galois //.
by move=> n; rewrite char_lalg charF0.
Qed.

Section RadicalRoots.
Variables (F0 : fieldType) (L : fieldExtType F0).
Variables (E : {subfield L}) (n : nat) (x : L) (r : L).
Hypothesis r_root : (n.-primitive_root r)%R.
Hypothesis xnE : (x ^+ n)%R \in E.
Notation rs := [seq x * r ^+ val i | i : 'I_n].

Lemma uniq_roots_Xn_sub_xn : x != 0 -> uniq rs.
Proof using r_root.
move=> xN0; rewrite /image_mem (map_comp (fun i => x * r ^+ i)) val_enum_ord.
apply/(uniqP 0) => i j; rewrite !inE size_map size_iota/= => ip jp.
rewrite !(nth_map 0%N) ?size_iota// ?nth_iota// => /(mulfI xN0).
by move/eqP; rewrite (eq_prim_root_expr r_root) !modn_small// => /eqP.
Qed.

Lemma Xn_sub_xnE : (n > 0)%N ->
 'X^n - (x ^+ n)%:P = \prod_(i < n) ('X - (x * r ^+ i)%:P).
Proof using r_root.
move=> n_gt0; have [->|xN0] := eqVneq x 0.
  under eq_bigr do rewrite mul0r subr0.
  by rewrite expr0n gtn_eqF// subr0 prodr_const card_ord.
rewrite [LHS](@all_roots_prod_XsubC _ _ rs).
- by rewrite (monicP _) ?monic_XnsubC// scale1r big_map big_enum.
- by rewrite size_XnsubC// size_map size_enum_ord.
- rewrite all_map; apply/allP => i _ /=; rewrite /root !hornerE hornerXn.
  by rewrite exprMn exprAC [r ^+ _]prim_expr_order// expr1n mulr1 subrr.
- by rewrite uniq_rootsE uniq_roots_Xn_sub_xn.
Qed.

End RadicalRoots.

Section galois_Fadjoin_prime.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Hypothesis char_L : [char L] =i pred0.
Variables (E : {subfield L}) (n : nat) (x : L) (r : L).
Hypothesis r_root : (n.-primitive_root r)%R.
Hypothesis xnE : (x ^+ n)%R \in E.
Hypothesis rE : r \in E.

Section n_gt0.
Hypothesis n_gt0 : (n > 0)%N.

Lemma galois_Fadjoin_prime : galois E <<E; x>>.
Proof using r_root xnE n_gt0 rE.
have [->|XN0] := eqVneq x 0.
  by rewrite (Fadjoin_idP _) ?rpred0 ?galois_refl.
apply/splitting_galoisField; exists ('X^n - (x ^+ n)%:P)%R.
split; first by rewrite rpredB ?rpredX ?polyOverX ?polyOverC//.
  rewrite (Xn_sub_xnE _ r_root)// -(big_map _ predT (fun x => 'X - x%:P)).
  rewrite separable_prod_XsubC -[index_enum _]enumT.
  by rewrite (uniq_roots_Xn_sub_xn r_root).
exists [seq x * r ^+ val i | i : 'I_n].
  by rewrite (Xn_sub_xnE _ r_root)// big_map big_enum//= eqpxx.
apply/eqP; rewrite /image_mem (map_comp (fun i => x * r ^+ i)) val_enum_ord.
rewrite -[n]prednK ?p_gt0//= mulr1 adjoin_cons (Fadjoin_seq_idP _)// all_map.
by apply/allP => i _/=; rewrite rpredM ?memv_adjoin// rpredX// subvP_adjoin.
Qed.
End n_gt0.

Section n_prime.
Hypothesis xNE : x \notin E.
Hypothesis n_prime : prime n.
Let n_gt0 := prime_gt0 n_prime.

Lemma Fadjoin_primeE : minPoly E x = 'X^n - (x ^+ n)%:P.
Proof using n_prime rE r_root xNE xnE.
have xN0 : x != 0 by apply: contraNneq xNE => ->; rewrite rpred0.
have dvd_mpEx := dvdp_minpoly_Xn_subn xnE.
apply/eqP; rewrite -eqp_monic ?(monic_minPoly, monic_XnsubC)//.
move: {+}dvd_mpEx; rewrite (Xn_sub_xnE _ r_root)//.
pose U x (i : 'I_n) := x * r ^+ i.
rewrite -(big_map (U x) predT (fun z => 'X - z%:P)) /=.
rewrite /index_enum -enumT /=; set rs := map _ _.
case/dvdp_prod_XsubC => [m mpEx].
suff mrsE: mask m rs = rs by rewrite mrsE in mpEx.
have: (minPoly E x)`_0 \in E by apply/polyOverP/minPolyOver.
move: {+}mpEx; rewrite eqp_monic ?(monic_minPoly, monic_prod_XsubC) //.
move/eqP=> ->; rewrite coef0_prod {1}mask_filter //; last first.
  exact: uniq_roots_Xn_sub_xn r_root _.
rewrite big_filter big_map (eq_bigr (U (- x))); last first.
- by move=> i _; rewrite coefB coefX coefC eqxx /U mulNr sub0r.
rewrite big_mkcond big_enum -big_mkcond prodrMl /= fpredMr; last first.
- apply/prodf_neq0=> /= i _; have /eqP := prim_expr_order r_root.
  rewrite -{1}[n](@subnK i n) 1?ltnW // exprD; apply: contraL.
  by move/eqP=> ->; rewrite mulr0 eq_sym oner_eq0.
- by apply/rpred_prod=> i _; apply/rpredX.
rewrite exprNn fpredMl; last first.
- by rewrite signr_eq0.
- by rewrite rpredX // rpredN rpred1.
set S := (S in x ^+ #|S|); case/boolP: (#|S| == 0%N) => [/eqP/card0_eq z_S|nz_S].
- move: {+}mpEx; rewrite mask_filter //; last first.
    exact: uniq_roots_Xn_sub_xn r_root _.
  rewrite big_filter big_map big_pred0.
    by move/eqp_root/(_ x); rewrite root_minPoly rootC oner_eq0.
  by move=> /= i; move: (z_S i).
have: (#|S| <= n)%N by rewrite -[X in (_ <= X)%N]card_ord max_card.
rewrite leq_eqVlt => /orP[Sfull _|lt_S_p].
- rewrite mask_filter ?(uniq_roots_Xn_sub_xn r_root _) //.
  rewrite (@eq_in_filter _ _ predT) ?filter_predT//.
  move=> _ /mapP[/= i _ ->]; apply: contraLR Sfull => xri_maskN.
  rewrite -[X in _ != X]card_ord eqn_leq max_card /= -ltnNge.
  by apply/proper_card/properP; split; [apply/subset_predT | exists i].
move: #|S| nz_S lt_S_p => k nz_k lt_kp; apply/contraTeq => _ /=.
have: coprime n k by rewrite prime_coprime // gtnNdvd // lt0n.
case/(coprimeP _ n_gt0) => -[u v] /= bz.
move: xNE; rewrite -{1}[x]expr1 -bz expfB; last first.
  by rewrite -subn_gt0 bz.
apply: contra => xkE; apply: rpredM.
+ by rewrite mulnC exprM rpredX.
+ by rewrite rpredV mulnC exprM rpredX.
Qed.

Lemma size_Fadjoin_prime : size (minPoly E x) = n.+1.
Proof. by rewrite Fadjoin_primeE ?size_XnsubC. Qed.

Local Notation G := 'Gal(<<E; x>> / E)%g.

(* - Gal(E(x) / E) has order n *)
Lemma order_galois_Fadjoin_prime : #|G| = n.
Proof.
rewrite -galois_dim 1?galois_Fadjoin_prime// -adjoin_degreeE.
by have := size_minPoly E x; rewrite size_Fadjoin_prime// => -[].
Qed.

Lemma Fadjoin_prime_cyclic : cyclic G.
Proof. by apply/prime_cyclic; rewrite order_galois_Fadjoin_prime. Qed.

Lemma Fadjoin_prime_abelian : abelian G.
Proof. exact/cyclic_abelian/Fadjoin_prime_cyclic. Qed.

Lemma solvable_ext_Fadjoin_prime : solvable_ext E <<E; x>>.
Proof.
apply/(solvable_extP char_L); exists <<E; x>>%AS.
by rewrite galois_Fadjoin_prime// abelian_sol ?Fadjoin_prime_abelian/= ?subvv.
Qed.

End n_prime.
End galois_Fadjoin_prime.
