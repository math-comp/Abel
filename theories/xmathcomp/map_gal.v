From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field.
From Abel Require Import various char0.

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
Implicit Types (K E F : {subfield L}).

Lemma galois_subW E F : galois E F -> (E <= F)%VS. Proof. by case/andP. Qed.

Lemma galois_normalW E F : galois E F -> (normalField E F)%VS.
Proof. by case/and3P. Qed.

Lemma galois_separableW E F : galois E F -> (separable E F)%VS.
Proof. by case/and3P. Qed.

Lemma normalField_refl E : normalField E E.
Proof.
apply/forallP => /= u; apply/implyP; rewrite in_set.
by move=> /andP[/andP[_ /fixedSpace_limg->]].
Qed.
Hint Resolve normalField_refl : core.

Lemma galois_refl E : galois E E.
Proof. by rewrite /galois subvv separable_refl normalField_refl. Qed.

Lemma Fadjoin_sub E x y : x \in <<E; y>>%VS -> (<<E; x>> <= <<E; y>>)%VS.
Proof. by move=> xEy; apply/FadjoinP; rewrite subv_adjoin. Qed.

Lemma galvv E : ('Gal(E / E) = 1)%g.
Proof.
apply/trivgP/subsetP=> u uG; rewrite inE.
by apply/gal_eqP => x xE; rewrite gal_id (fixed_gal _ uG).
Qed.

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

Lemma separable_mulv K x y :
  separable_element K x -> separable_element K y -> separable_element K (x * y).
Proof.
move/(separable_elementS (subv_adjoin K y))=> sepKy_x sepKy.
have [z defKz] := Primitive_Element_Theorem x sepKy.
have /(adjoin_separableP _): x * y \in <<K; z>>%VS.
  by rewrite -defKz rpredM ?memv_adjoin // subvP_adjoin ?memv_adjoin.
apply; apply: adjoin_separable sepKy (adjoin_separable sepKy_x _).
by rewrite defKz base_separable ?memv_adjoin.
Qed.

Lemma separable_prod I r (P : pred I) (v_ : I -> L) (K : {subfield L}) :
    (forall i, P i -> separable_element K (v_ i)) ->
  separable_element K (\prod_(i <- r | P i) v_ i).
Proof.
move=> sepKi.
by elim/big_ind: _; [apply/base_separable/mem1v | apply: separable_mulv |].
Qed.

Lemma separable_prodv (k K1 K2 : {subfield L}) :
  separable k (K1 * K2) = (separable k K1 && separable k K2).
Proof.
apply/separableP/andP => [sepK12|].
  split; apply/separableP => y yK; rewrite sepK12//.
    by apply: (subv_trans yK); rewrite field_subvMr.
  by apply: (subv_trans yK); rewrite field_subvMl.
move=> [/separableP sepK1 /separableP sepK2].
move=> x /memv_mulP[n [us [vs [/allP/= usK /allP/= vsK ->]]]].
rewrite separable_sum// => i _; rewrite separable_mulv//.
  by rewrite sepK1 ?usK ?mem_tnth.
by rewrite sepK2 ?vsK ?mem_tnth.
Qed.

Lemma separable_super (k K : {subfield L}) : (k <= K)%VS ->
  separable K k.
Proof. by move=> /separableSr->//; rewrite separable_refl. Qed.

Lemma separable1 (k : {subfield L}) : separable k 1.
Proof. by rewrite separable_super// ?sub1v. Qed.

Lemma separable_big_prodv I r (P : {pred I}) (k : {subfield L})
  (K : I -> {subfield L}) :
  separable k (\big[@prodv _ _/1%VS]_(i <- r | P i) K i) =
  \big[andb/true]_(i <- r | P i) separable k (K i).
Proof.
rewrite big_prodv_eq_aspace; elim/big_rec2: _ => [|i E b _].
  by rewrite separable1.
by rewrite separable_prodv => ->.
Qed.

Lemma separable_big_prodvW I r (P : {pred I}) (k : {subfield L})
  (K : I -> {subfield L}) :
  (forall i, P i -> separable k (K i)) ->
  separable k (\big[@prodv _ _/1%VS]_(i <- r | P i) K i).
Proof.
move=> sepKi; rewrite separable_big_prodv big_tnth big_andE.
by apply/'forall_implyP => i /sepKi.
Qed.

Lemma separable_prodvr (k K F : {subfield L}) : (k <= F)%VS ->
  separable k K -> separable F (K * F).
Proof.
by move=> kF sepkK; rewrite separable_prodv separable_refl (separableSl kF).
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
by rewrite (separable_prodvr kF)// (normal_prodvr kK kF).
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

Lemma galois_isog (k K F : {subfield L}) : galois k K -> (k <= F)%VS ->
  'Gal((K * F) / F) \isog 'Gal (K / K :&: F).
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

Lemma galois_prodv (k K1 K2 : {subfield L}) :
  galois k K1 -> galois k K2 -> galois k (K1 * K2).
Proof.
rewrite /galois => /and3P[kK1 sepK1 normK1] /and3P[kK2 sepK2 normK2].
rewrite -[X in (X <= _)%VS]prodv_id prodvS//=.
by rewrite separable_prodv ?sepK1 ?sepK2// normal_prodv.
Qed.

Lemma galois_big_prodv_seq I r (P : {pred I}) (k : {subfield L})
  (K : I -> {subfield L}) :
  (forall i, P i -> galois k (K i)) ->
  ~~ nilp [seq i <- r | P i] ->
  galois k (\big[@prodv _ _/1%VS]_(i <- r | P i) K i).
Proof.
move=> galkK brP; pose gW := (galois_subW, galois_normalW, galois_separableW).
pose bpv := (subv_big_prodv_seq, separable_big_prodvW, normal_big_prodv).
by rewrite /galois !bpv// => i Pi; rewrite /= gW ?galkK.
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
#[global] Hint Resolve normalField_refl : core.

Section map_hom.
Variables (F0 : fieldType) (L L' : splittingFieldType F0).
Variable (iota : 'Hom(L, L')).

Definition map_hom (f : 'End(L)) := (iota \o f \o iota^-1)%VF.
Definition inv_map_hom (f : 'End(L')) := (iota^-1 \o f \o iota)%VF.

Lemma map_hom_is_linear : linear map_hom.
Proof.
move=> /= k a b; apply/lfunP => x; rewrite /map_hom.
by rewrite !(comp_lfunE, add_lfunE, scale_lfunE) linearP.
Qed.
Canonical map_hom_linear := Linear map_hom_is_linear.

Lemma inv_map_hom_is_linear : linear inv_map_hom.
Proof.
move=> /= k a b; apply/lfunP => x; rewrite /map_hom.
by rewrite !(comp_lfunE, add_lfunE, scale_lfunE) linearP.
Qed.
Canonical inv_map_hom_linear := Linear inv_map_hom_is_linear.

Lemma lker0_map_homC (f : 'End(L)) : lker iota == 0%VS ->
  (map_hom f \o iota = iota \o f)%VF.
Proof. by move=> kiota0; apply/lfunP => x; rewrite !comp_lfunE lker0_lfunK. Qed.

Lemma lker0_map_homE (f : 'End(L)) (x : L) : lker iota == 0%VS ->
  map_hom f (iota x) = iota (f x).
Proof. by rewrite !comp_lfunE => /lker0_lfunK->. Qed.

Lemma inv_map_homC (f : 'End(L')) : (f @: limg iota <= limg iota)%VS ->
  (iota \o inv_map_hom f = f \o iota)%VF.
Proof.
move=> fiota; apply/lfunP => x. rewrite !comp_lfunE limg_lfunVK//.
by rewrite memvE (subv_trans _ fiota)// -memvE !memv_img ?memvf.
Qed.

Lemma inv_map_homE (f : 'End(L')) (x : L) :
  f (iota x) \in (limg iota)%VS ->
  iota (inv_map_hom f x) = f (iota x).
Proof. by move=> fiotax; rewrite !comp_lfunE limg_lfunVK. Qed.

End map_hom.

Section map_ahom.
Variables (F0 : fieldType) (L L' : splittingFieldType F0).
Variable (iota : 'AHom(L, L')).

Lemma map_hom_algE (f : 'End(L)) (x : L) :
  map_hom iota f (iota x) = iota (f x).
Proof. by rewrite lker0_map_homE// AHom_lker0. Qed.

Lemma map_hom_algC (f : 'End(L)) : (map_hom iota f \o iota = iota \o f)%VF.
Proof. by rewrite lker0_map_homC// AHom_lker0. Qed.

Lemma map_ahom_in (f : 'End(L)) (E : {vspace L}) :
  ahom_in (iota @: E) (map_hom iota f) = ahom_in E f.
Proof.
apply/ahom_inP/ahom_inP => -[mfM mf1]; last first.
  split; last by rewrite -(rmorph1 [rmorphism of iota]) map_hom_algE mf1.
  move=> _ _ /memv_imgP[u uE ->] /memv_imgP[v vE ->].
  by rewrite !(map_hom_algE, =^~rmorphM)/= mfM.
split=> [x y xE yE|]; last first.
  have : map_hom iota f (iota 1) = iota 1 by rewrite rmorph1.
  by rewrite map_hom_algE => /fmorph_inj.
have := mfM _ _ (memv_img iota xE) (memv_img iota yE).
by rewrite !(map_hom_algE, =^~rmorphM)/= => /fmorph_inj.
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

Lemma inv_map_hom_kHom (E F : {subfield L}) (f : 'End(L')) :
  (E <= F)%VS -> ((f @: (iota @: F)) <= (limg iota))%VS ->
  kHom E F (inv_map_hom iota f) = kHom (iota @: E) (iota @: F) f.
Proof.
move=> EF fiotaF; have fiotaf u : u \in F -> f (iota u) \in limg iota.
  by move=> uF; apply: subv_trans fiotaF; do !apply: memv_img.
apply/kHomP/kHomP => -[/= fM s_id].
   split=> [_ _/memv_imgP[x xF ->]|_] /memv_imgP[y yF ->].
     rewrite -!rmorphM/= -3?inv_map_homE ?memv_img ?memvf ?fiotaf ?rpredM//.
     by rewrite fM// rmorphM.
  by rewrite -inv_map_homE ?s_id// fiotaf//; apply: subv_trans EF.
split=> [x y xF yF|x xF]; apply: (fmorph_inj [rmorphism of iota]) => /=.
  by rewrite rmorphM/= !inv_map_homE ?fiotaf ?rpredM// rmorphM fM ?memv_img.
by rewrite inv_map_homE s_id ?memv_img ?memvf.
Qed.

Lemma limg_inv_map_ahom  (E : {subfield L}) (f : 'End(L')) :
  ((f @: (iota @: E)) <= (iota @: E))%VS ->
  (iota @: (inv_map_hom iota f @: E))%VS = (f @: (iota @: E))%VS.
Proof.
move=> fiotaE; rewrite -!limg_comp; apply/vspaceP => x.
have fiota u : u \in E -> f (iota u) \in limg iota.
  move=> uE; rewrite memvE (@subv_trans _ _ (f @: (iota @: E))%VS) //.
    by rewrite -memvE !(memv_img, limgS).
  by rewrite (subv_trans fiotaE) ?limgS ?subvf.
by apply/memv_imgP/memv_imgP => -[u uE ->]; exists u => //;
   rewrite [LHS]comp_lfunE [RHS]comp_lfunE inv_map_homE// ?fiota.
Qed.

Lemma inv_map_hom_kAut (E F : {subfield L}) (f : 'End(L')) :
  (E <= F)%VS -> ((f @: (iota @: F)) <= (iota @: F))%VS ->
  kAut E F (inv_map_hom iota f) = kAut (iota @: E) (iota @: F) f.
Proof.
move=> EF fiotaF; rewrite !kAutE -limg_inv_map_ahom// limg_ker0 ?AHom_lker0//.
by rewrite inv_map_hom_kHom// (subv_trans fiotaF) ?limgS ?subvf.
Qed.

Lemma inv_map_ahom_in (f : 'End(L')) (E : {subfield L}) :
    (f @: (iota @: E) <= limg iota)%VS ->
  ahom_in E (inv_map_hom iota f) = ahom_in (iota @: E) f.
Proof.
by move=> fiotaE; rewrite -!k1HomE inv_map_hom_kHom ?sub1v// aimg1.
Qed.

Lemma inv_map_is_ahom (E : {subfield L}) (f : gal_of (iota @: E)) :
  ahom_in E (inv_map_hom iota f).
Proof.
rewrite inv_map_ahom_in ?limg_gal ?limgS ?subvf//.
by rewrite -k1HomE -gal_kHom ?sub1v ?gal1.
Qed.
Canonical inv_map_ahom (f : gal_of (limg iota)) := AHom (inv_map_is_ahom f).

Import AEnd_FinGroup.

Definition map_ahom (f : 'AEnd(L)) := projT1 (map_ahom_subproof f).

Lemma map_ahomC (f : 'AEnd(L)) :
   (map_ahom f \o iota)%VF = (iota \o f)%VF.
Proof. by rewrite /map_ahom; case: map_ahom_subproof. Qed.

Lemma map_ahomE (f : 'AEnd(L)) x : map_ahom f (iota x) = iota (f x).
Proof. by rewrite -!comp_lfunE map_ahomC. Qed.

Lemma limg_map_ahom (f : 'AEnd(L))  (E : {vspace L}) :
  (map_ahom f @: (iota @: E))%VS = (iota @: (f @: E))%VS.
Proof. by rewrite -!limg_comp map_ahomC. Qed.

Lemma map_ahom_kAut s (E F : {subfield L}) :
  kAut (iota @: E)%VS (iota @: F)%VS (map_ahom s) = kAut E F s.
Proof.
rewrite !kAutE limg_map_ahom limg_ker0 ?AHom_lker0// [LHS]andbC [RHS]andbC.
have [sF_sub_F|]//= := boolP (s @: F <= F)%VS.
apply/kAHomP/kAHomP => [s_id x xE|s_id _/memv_imgP[x xE ->]]; last first.
  by rewrite map_ahomE s_id.
apply: (fmorph_inj [rmorphism of iota]).
by rewrite /= -map_ahomE s_id// memv_img.
Qed.

Lemma map_ahom_kAEnd s (E F : {subfield L}) :
  (map_ahom s \in kAEnd (iota @: E)%VS (iota @: F)%VS) = (s \in kAEnd E F).
Proof. by rewrite !inE map_ahom_kAut. Qed.

Lemma map_ahom_kEnd_img s : map_ahom s \in kAEnd 1 (iota @: {: L})%AS.
Proof.
rewrite inE -(aimg1 iota) map_ahom_kAut// kAutfE.
exact/kHom_lrmorphism/ahom_is_lrmorphism.
Qed.

End map_ahom.

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

Definition map_gal (g : gal_of E) : gal_of (iota @: E) :=
  gal (iota @: E) (map_ahom iota g).

Lemma map_galE (g : gal_of E) :
  {in E, forall x, map_gal g (iota x) = iota (g x)}.
Proof.
move=> x xE /=; rewrite galK ?memv_img ?memvf//=.
  by rewrite -!comp_lfunE map_ahomC.
by rewrite limg_map_ahom limg_gal.
Qed.

Definition map_gal_is_morphism : {in setT &,
   {morph map_gal : x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move=> /= f g _ _; apply/eqP/gal_eqP => _/memv_imgP[x xE ->].
rewrite galM ?memv_img// 3?map_galE// ?galM//.
by rewrite -[in X in _ \in X](limg_gal f) memv_img.
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
by rewrite !map_galE// => /fmorph_inj.
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
have /kHom_to_AEnd[f eqf] : kHom K E (inv_map_hom iota f').
  by rewrite inv_map_hom_kHom ?(subv_trans f'E) ?limgS ?subvf//; apply/kAHomP.
have fE : (f @: E <= E)%VS.
  rewrite -(eq_in_limg eqf) -(limg_ker0 _ _ (AHom_lker0 iota)).
  by rewrite limg_inv_map_ahom//.
exists f; rewrite ?inE ?kAut1E ?kAutE/= ?subfield_closed ?subvf ?andbT ?fE.
  apply/kAHomP => x xK; rewrite -eqf ?(subvP subKE)// !comp_lfunE.
  by rewrite f'K ?memv_img// lker0_lfunK.
apply/eqP/gal_eqP => _/memv_imgP[x xE ->]; rewrite map_galE//.
rewrite !galK ?memv_img// -eqf//= inv_map_homE//.
apply: subv_trans (limgS _ (subvf E)); apply: subv_trans f'E.
by do !apply: memv_img.
Qed.

Lemma reflexiveW T (r : rel T) : reflexive r -> forall x y, x = y -> r x y.
Proof. by move=> ? ? ? ->. Qed.

Lemma normalField_aimg (K : {subfield L}) : (K <= E)%VS ->
   normalField (iota @: K) (iota @: E) = normalField K E.
Proof.
move=> KE; have iotaKS : (iota @: K <= iota @: E)%VS by rewrite limgS.
apply/splitting_normalField/splitting_normalField => //= -[p pK [rs peq Krs]].
  have /polyOver_aimg [q qK pE] := pK.
  have /subset_limgP [rs' _ rsE] : {subset rs <= (iota @: E)%VS}.
    by rewrite -Krs; apply/seqv_sub_adjoin.
  exists q => //; exists rs'.
    by have := peq; rewrite pE rsE -map_prod_XsubC/= eqp_map.
  by do [rewrite rsE -aimg_adjoin_seq => /eqP;
         rewrite eq_limg_ker0// => /eqP] in Krs.
exists (map_poly iota p) => //; first by rewrite mapf_polyOver.
by apply/splittingFieldFor_aimg; exists rs.
Qed.

Lemma galois_aimg (K : {subfield L}) :
   galois (iota @: K) (iota @: E) = galois K E.
Proof.
rewrite /galois limg_ker0 ?AHom_lker0// separable_aimg.
by case: (boolP (K <= E)%VS) => // /normalField_aimg->.
Qed.

End map_gal.

Import AEnd_FinGroup.

Section normalClosure.
Variable (F0 : fieldType) (L : splittingFieldType F0).
Implicit Types (K E F : {subfield L}).

Lemma separable_aimgr E F s : s \in kAEndf E ->
   separable E (s @: F) = separable E F.
Proof.
rewrite inE => /kHom_kAut_sub/kAHomP s_id; rewrite -(separable_aimg _ _ s).
suff /eq_in_limg->: {in E, s =1 \1%VF} by rewrite lim1g.
by move=> x xE; rewrite lfunE/= s_id.
Qed.

Definition normalClosure (U V : {vspace L}) :=
  (\big[@prodv _ _/1]_(s in kAEndf U) (s @: (U * V)))%VS.

Definition normalClosure_is_aspace E F : is_aspace (normalClosure E F).
Proof.
by rewrite /normalClosure big_prodv_eq_aspace; case: (\big[_/_]_(_ in _) _).
Qed.
Canonical normalClosure_aspace E F := ASpace (normalClosure_is_aspace E F).

Lemma prodv_sub_normalClosure E F : (E * F <= normalClosure E F)%VS.
Proof.
rewrite /normalClosure (bigD1 \1%AF) ?group1//= lim1g.
by rewrite big_prodv_eq_aspace field_subvMr.
Qed.

Lemma normalClosureSl E F : (E <= normalClosure E F)%VS.
Proof.
by rewrite (subv_trans (field_subvMr _ _) (prodv_sub_normalClosure _ _)).
Qed.
#[local] Hint Resolve normalClosureSl : core.

Lemma normalClosureSr E F : (F <= normalClosure E F)%VS.
Proof. exact: subv_trans (field_subvMl _ _) (prodv_sub_normalClosure _ _). Qed.
Hint Resolve normalClosureSr : core.

Lemma normalClosure_normal E F : normalField E (normalClosure E F).
Proof.
apply/'forall_implyP => s s_end; apply/eqP.
rewrite /normalClosure (big_morph _ (aimgM _) (aimg1 _)).
under eq_bigr => s' do rewrite -limg_comp.
under eq_bigr => s' do have -> : (s \o s')%VF = 'R%act s' s by [].
have /(reindex_astabs 'R _) : s \in ('N(kAEndf E | 'R))%g by rewrite astabsR/=.
by move/(_ _ _ _ (fun i => i @: (E * F))%AS); rewrite !big_prodv_eq_aspace => <-.
Qed.
#[local] Hint Resolve normalClosure_normal : core.

Lemma normalClosure_separable E F : separable E F ->
   separable E (normalClosure E F).
Proof.
move=> sepEF; rewrite separable_big_prodv big_andE; apply/forall_inP => g ggal.
by rewrite separable_aimgr// separable_prodv separable_refl.
Qed.

Lemma normalClosure_galois E F : separable E F -> galois E (normalClosure E F).
Proof.
move=> sepEF; rewrite /galois.
by rewrite normalClosureSl normalClosure_separable// normalClosure_normal.
Qed.
#[local] Hint Resolve normalClosure_galois : core.

Lemma normalClosureP E F K' : (E <= K')%VS -> (F <= K')%VS ->
  normalField E K' -> (normalClosure E F <= K')%VS.
Proof.
move=> EK' FK' /'forall_implyP/(_ _ _)/eqP/= sK'.
apply/big_prod_subfieldP => /= u uEF; rewrite rpred_prod// => s s_end.
by apply/subvP: (uEF s s_end); rewrite -(sK' _ s_end) limgS// prodv_sub.
Qed.

Lemma galoisClosureP E F K' : (F <= K')%VS ->
  galois E K' -> (normalClosure E F <= K')%VS.
Proof. by move=> EK' /and3P[FK' _ ] /normalClosureP; apply. Qed.

Lemma normalClosure_id E F : (E <= F)%VS -> normalField E F ->
   normalClosure E F = F.
Proof.
by move=> EF nEF; apply/eqP; rewrite eqEsubv/= normalClosureSr normalClosureP.
Qed.

Lemma galoisClosure_id E F : galois E F -> normalClosure E F = F.
Proof. by move=> /and3P[EF _ /normalClosure_id->]. Qed.

Definition solvable_ext (E F : {vspace L}) :=
  separable E F && solvable 'Gal(normalClosure E F / E).

Lemma char0_solvable_extE E F : has_char0 L ->
  solvable_ext E F = solvable 'Gal(normalClosure E F / E).
Proof. by rewrite /solvable_ext => /char0_separable->. Qed.

Lemma solvable_extP (E F : {subfield L}) :
  reflect (exists K : {subfield L},
            [&& (F <= K)%VS, galois E K & solvable 'Gal(K / E)])
          (solvable_ext E F).
Proof.
apply: (iffP idP) => [/andP[sepEF solEF]|[K /and3P[FK galEK solEK]]].
  exists [aspace of normalClosure E F].
  by rewrite normalClosure_galois ?normalClosureSr.
have MsubK := galoisClosureP FK galEK; rewrite /solvable_ext.
have sepEF : separable E F by case/and3P: galEK => [_ /separableSr->].
have /and3P [EsubM _ EnormM] := (normalClosure_galois sepEF).
by rewrite -(isog_sol (normalField_isog galEK _ _)) ?EsubM ?quotient_sol ?andbT.
Qed.

Lemma solvable_ext_refl E : solvable_ext E E.
Proof.
by apply/solvable_extP; exists E; rewrite subvv galois_refl/= galvv solvable1.
Qed.
#[local] Hint Resolve solvable_ext_refl : core.

Lemma sub_solvable_ext F K E :
  (E <= F)%VS -> solvable_ext K F -> solvable_ext K E.
Proof.
move=> EF /solvable_extP[M /and3P[Msuper galKM solKM]].
by apply/solvable_extP; exists M; rewrite (subv_trans EF) ?galKM.
Qed.

Lemma solvable_prodv (k E F : {subfield L}) :
  (k <= F)%VS -> solvable_ext k E -> solvable_ext F (E * F)%AS.
Proof.
move=> kF /andP[sepkE solkE]; apply/solvable_extP => //.
exists ([aspace of normalClosure k E] * F)%AS.
rewrite (@galois_prodvr _ _ k) ?normalClosure_galois//.
rewrite ?prodvSl ?sub_normalClosure//=.
rewrite (isog_sol (galois_isog (normalClosure_galois _) _))//.
rewrite (solvableS _ solkE)// galS// subv_cap kF.
by rewrite galois_subW ?normalClosure_galois.
Qed.

Import AEnd_FinGroup.

Lemma solvable_ext_trans (F k E : {subfield L}) : (k <= F <= E)%VS ->
  solvable_ext k F -> solvable_ext F E -> solvable_ext k E.
Proof.
move=> /andP[kF FE] solkF solFE.
move: (solkF) (solFE) => /andP[sepkF solmkF] /andP[sepFE solmFE].
have sepkE := separable_trans sepFE.
have /solvable_extP [/= l /and3P[EKl galKl subl]] :=
  solvable_prodv (normalClosureSr k F) solFE.
apply/solvable_extP; exists [aspace of normalClosure k l] => /=.
have galkK := normalClosure_galois sepkF.
set K := normalClosure k F in galkK galKl subl EKl *.
have /and3P [kK sepkK normkK] := galkK.
have /and3P [Kl sepKl normKl] := galKl.
have sepkl := separable_trans sepkK sepKl.
have kl := subv_trans kK Kl.
rewrite normalClosure_galois ?(subv_trans _ (normalClosureSr _ _))//=; last first.
  by rewrite (subv_trans _ EKl)//= field_subvMr.
have KM : (K <= normalClosure k l)%VS := subv_trans Kl (normalClosureSr _ _).
have kKM : (k <= K <= normalClosure k l)%VS by rewrite kK KM.
rewrite (series_sol (normalField_normal _ normkK))//= -/K.
rewrite (isog_sol (normalField_isog _ _ _)) ?normalClosure_galois//=.
rewrite [X in _ && X]solmkF andbT /normalClosure.
under eq_bigr do rewrite /= (prodv_idPr _)//.
rewrite big_prodv_eq_aspace big_enum_val/=.
have /'forall_implyP/(_ _ _)/eqP/= sK := galois_normalW galkK.
have gKl (i : 'I_#|kAEndf k|) : galois K (enum_val i @: l)%AS.
  move: (enum_val _) (enum_valP i) => s s_end.
  have /splitting_galoisField[/= p [pK p_sep [rs p_eq <-]]] := galKl.
  apply/splitting_galoisField; exists (map_poly s p); split => //=.
  - by rewrite -(sK _ s_end) mapf_polyOver.
  - by rewrite separable_map.
  - rewrite aimg_adjoin_seq -{1}(sK _ s_end); exists (map s rs) => //.
    by rewrite -map_prod_XsubC eqp_map.
rewrite -(injm_sol (gal_big_prodv_cast_inj gKl))//.
rewrite (solvableS (img_gal_big_prodv_cast_sub _)) ?sol_setXn// => i /=.
move: (enum_val _) (enum_valP i) => s s_end; rewrite -(sK _ s_end).
by rewrite -img_map_gal/= morphim_sol.
Qed.

End normalClosure.

#[global] Hint Resolve normalClosureSl : core.
#[global] Hint Resolve normalClosureSr : core.
#[global] Hint Resolve normalClosure_normal : core.
#[global] Hint Resolve solvable_ext_refl : core.

Lemma aimg_normalClosure (F0 : fieldType) (L L' : splittingFieldType F0)
  (iota : 'AHom(L, L')) (K E : {subfield L}) :
  (iota @: normalClosure K E)%VS = normalClosure (iota @: K) (iota @: E).
Proof.
set M' := normalClosure (iota @: _) _; have iK0 := AHom_lker0 iota.
have M'sub : (M' <= iota @: normalClosure K E)%VS.
  by rewrite normalClosureP ?limgS//= normalField_aimg/=.
apply/eqP; rewrite eqEsubv M'sub /M'.
have /sub_aimgP[/= M ME] : (M' <= iota @: fullv)%VS.
  by apply: subv_trans M'sub _; rewrite limgS ?subvf.
have KM : (K <= M)%VS by rewrite -(limg_ker0 _ _ iK0) ME/= normalClosureSl.
rewrite -ME limgS// normalClosureP//.
  by rewrite -(limg_ker0 _ _ iK0) ME/= normalClosureSr.
by rewrite -(normalField_aimg iota)// ME// normalClosure_normal.
Qed.

Lemma solvable_ext_aimg (F0 : fieldType) (L L' : splittingFieldType F0)
  (iota : 'AHom(L, L')) (E F : {subfield L}) :
  solvable_ext (iota @: E) (iota @: F) = solvable_ext E F.
Proof.
rewrite /solvable_ext separable_aimg; have [sepEF|]//= := boolP (separable _ _).
by rewrite -aimg_normalClosure// -img_map_gal injm_sol ?map_gal_inj ?subsetT.
Qed.
