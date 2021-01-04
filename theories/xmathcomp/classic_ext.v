From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field.
From Abel Require Import various cyclotomic_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

Lemma classic_fieldExtFor
  (F0 : fieldType) (L : fieldExtType F0) (p : {poly L}) : p != 0 ->
  classically
  { L' : fieldExtType F0 & { rs : seq L' & { iota : 'AHom(L, L') |
  <<iota @: fullv & rs>>%VS = fullv &
  p ^^ iota %= \prod_(r <- rs) ('X - r%:P) }}}.
Proof.
have [n] := ubnP (size p); elim: n => [|n IHn]// in F0 L p *.
rewrite ltnS => sp_lt p_neq0.
apply: classic_bind (@classic_EM (irreducible_poly p)) => -[]; last first.
  have [|p_gt1] := leqP (size p) 1.
    rewrite leq_eqVlt ltnS leqn0 size_poly_eq0 (negPf p_neq0) orbF.
    move=> /size_poly1P[c cN0 ->] _.
    apply/classicW; exists L, [::], (id_ahom _).
      by rewrite Fadjoin_nil/= lim1g.
    by rewrite big_nil map_polyC/= lfunE/= polyC_eqp1.
  move=> NNred_p; have: classically (exists q : {poly L},
      [/\ size q != 1%N, (size q < size p)%N & q %| p]).
    apply/classicP => Nexq; apply: NNred_p.
    split => // q sq_neq1 dvdqp; apply: contraTT isT => eq_qp.
    case: Nexq; exists q; split => //.
    by rewrite ltn_neqAle dvdp_size_eqp// eq_qp/= dvdp_leq.
  apply: classic_bind => -[q [qN1 sq qp]].
  have qN0 : q != 0 by apply: contraTneq qp => ->; rewrite dvd0p.
  have sqn : (size q < n)%N by rewrite (leq_trans sq).
  apply: classic_bind (IHn _ _ _ sqn qN0) => -[L1 [rs1 [iota1 rs1_full qE]]].
  have /dvdpP [r pE]:= qp.
  have rN0 : r != 0 by apply: contra_eq_neq pE => ->; rewrite mul0r.
  have r1N0 : r ^^ iota1 != 0 by rewrite map_poly_eq0.
  have srn : (size (r ^^ iota1) < n)%N.
    rewrite size_map_poly.
    have /(congr1 (fun p : {poly _} => size p)) := pE.
    rewrite size_mul// [size q]polySpred// addnS/=.
    move=> /(canLR (@addnK _))<-; rewrite (leq_trans _ sp_lt)//.
    rewrite ltn_subrL size_poly_gt0 p_neq0 andbT.
    by rewrite ltn_predRL// ltn_neqAle eq_sym qN1 ?size_poly_gt0/=.
  apply: classic_bind (IHn _ _ _ srn r1N0) => -[L2 [rs2 [iota2 rs2_full rE]]].
  apply/classicW; exists L2, (map iota2 rs1 ++ rs2), (iota2 \o iota1)%AF.
    by rewrite adjoin_cat limg_comp -aimg_adjoin_seq rs1_full rs2_full.
  rewrite big_cat/= big_map (eq_map_poly (comp_lfunE _ _)) map_poly_comp pE.
  rewrite !rmorphM/= mulrC (eqp_trans (eqp_mull _ rE))// eqp_mulr//.
  have := qE; rewrite -(eqp_map [rmorphism of iota2]) => /eqp_trans->//=.
  rewrite (big_morph _ (rmorphM _) (rmorph1 _))/=.
  under eq_bigr do rewrite rmorphB/= -/iota map_polyX map_polyC/=.
  by rewrite eqpxx.
move=> /irredp_FAdjoin[L1 df [r1 r1_root r1_full]].
pose L01 := [fieldExtType F0 of baseFieldType L1].
pose r01 : L01 := r1.
pose inL01 : L -> L01 := in_alg L1.
have iota_morph : lrmorphism inL01.
split; [split; [exact: rmorphB|split; [exact: rmorphM|]]|].
  by rewrite /inL01 rmorph1.
  by move=> k a; rewrite /inL01 -mulr_algl rmorphM/= mulr_algl.
pose iota1 : 'AHom(L, L01) := AHom (linfun_is_ahom (LRMorphism iota_morph)).
have inL01E : inL01 =1 iota1 by move=> x; rewrite lfunE.
have r01_root : root (p ^^ iota1) r01 by rewrite -(eq_map_poly inL01E).
have r01_full : <<limg iota1; r01>>%VS = fullv.
  apply/eqP; rewrite eqEsubv subvf/=; apply/subvP => v _.
  have : (v : L1) \in <<1; r1>>%VS by rewrite r1_full memvf.
  move/Fadjoin_polyP => [pr pr1 ->].
  suff [qr ->] : exists2 qr, pr = qr & qr \is a polyOver (limg iota1).
    exact: mempx_Fadjoin.
  have /polyOver1P[qr ->] := pr1; exists (map_poly iota1 qr).
    by apply/eq_map_poly => w; rewrite lfunE.
  by apply/polyOverP => i; rewrite coef_map/= memv_img ?memvf.
have /dvdpP[q pE] : ('X - r01%:P) %| (p ^^ iota1) by rewrite dvdp_XsubCl.
have qN0 : q != 0.
  by apply: contra_eq_neq pE => ->; rewrite mul0r map_poly_eq0//.
have sq : (size q < n)%N.
  have /(congr1 (fun p : {poly _} => size p)) := pE.
  rewrite size_map_poly size_mul ?polyXsubC_eq0//.
  by rewrite size_XsubC addn2//= => <-.
apply: classic_bind (IHn _ _ _ sq qN0) => -[L2 [rs2 [iota12 rs2_full qE]]].
apply/classicW.
exists L2, (iota12 r01 :: rs2), (iota12 \o iota1)%AF.
  by rewrite adjoin_cons limg_comp -aimg_adjoin r01_full rs2_full.
rewrite big_cons/= (eq_map_poly (comp_lfunE _ _)) map_poly_comp pE.
by rewrite rmorphM/= mulrC rmorphB/= map_polyX map_polyC/= eqp_mull.
Qed.

Lemma classic_cycloExt (F0 : fieldType) (L : fieldExtType F0) n :
  (n%:R != 0 :> F0) -> classically
  { L' : fieldExtType F0 & { r : L' & { iota : 'AHom(L, L') |
    <<iota @: fullv; r>>%VS = fullv & n.-primitive_root r }}}.
Proof.
case: n => [|[_|[two_neq0|n']]]//; first by rewrite eqxx.
- apply/classicW; exists L, 1, (id_ahom _); rewrite ?prim_root1//.
  by rewrite lim1g (Fadjoin_idP _)// rpred1.
- apply/classicW; exists L, (- 1), (id_ahom _) => /=.
    by rewrite lim1g (Fadjoin_idP _)// rpredN1.
  by rewrite prim2_rootN1// -(rmorph_nat [rmorphism of in_alg L]) fmorph_eq0.
set n := n'.+3 => nF0neq0.
have poly_XnsubC_neq0 : 'X^n - 1 != 0 :> {poly L}.
  by rewrite -size_poly_eq0 size_XnsubC.
apply: classic_bind (classic_fieldExtFor (poly_XnsubC_neq0)).
case=> [L' [rs [iota rs_full]]].
rewrite rmorphB rmorph1/= map_polyXn.
rewrite eqp_monic ?monic_XnsubC ?monic_prod_XsubC// => /eqP Xnsub1E.
have rs_uniq : uniq rs.
  rewrite -separable_prod_XsubC -Xnsub1E separable_Xn_sub_1//.
  have: in_alg L' n%:R != 0 by rewrite fmorph_eq0.
  by rewrite raddfMn/= -(@in_algE _ L') rmorph1.
have rs_ge : (n <= size rs)%N.
  have /(congr1 (fun p : {poly _} => size p)) := Xnsub1E.
  rewrite size_XnsubC// size_prod_seq; last first.
    by move=> i _; rewrite polyXsubC_eq0.
  under eq_bigr do rewrite size_XsubC.
  rewrite big_tnth sum_nat_const card_ord subSn ?leq_pmulr//.
  by rewrite muln2 -addnn addnK => -[->].
have rsUroots : all n.-unity_root rs.
  apply/allP => r rrs; apply/eqP; rewrite Xnsub1E.
  by rewrite (big_rem _ rrs)/= hornerM hornerXsubC subrr mul0r.
have /has_prim_root/(_ _ _)/hasP[]// := rsUroots.
move=> r rrs rprim; apply/classicW; exists L', r, iota => //.
symmetry; rewrite -rs_full; have /eq_adjoin-> : rs =i r :: rs.
  by move=> r'; rewrite in_cons; case: eqVneq => // -> /=.
set K := limg iota => {rrs rs_uniq Xnsub1E rs_full rs_ge}.
elim: rs rsUroots => [|r' rs IHrs /andP[r'Uroots rsUroots]].
  by rewrite adjoin_seq1.
have r'K : r' \in <<K; r>>%VS.
  have /unity_rootP/(prim_rootP rprim)[i ->] := r'Uroots.
  by rewrite rpredX// memv_adjoin.
by rewrite !adjoin_cons (Fadjoin_idP r'K) -adjoin_cons IHrs.
Qed.

Lemma SplittingFieldExt
  (F0 : fieldType) (L : splittingFieldType F0) (p : {poly F0})
  (M : fieldExtType F0) (iota : 'AHom(L, M)) :
  splittingFieldFor (iota @: fullv) (p ^^ in_alg M) fullv ->
  SplittingField.axiom M.
Proof.
case=> rs pE rsf; have [_/polyOver1P[q ->] [rsq qE rsqf]] := splittingPoly L.
exists ((p * q) ^^ in_alg M); first by apply/polyOver1P; exists (p * q).
exists (map iota rsq ++ rs); last first.
  by rewrite adjoin_cat -(aimg1 iota) -aimg_adjoin_seq rsqf rsf.
rewrite big_cat/= rmorphM/= big_map mulrC.
rewrite (eqp_trans (eqp_mull _ pE))// eqp_mulr//.
have := qE; rewrite -(eqp_map [rmorphism of iota])/=.
rewrite (big_morph _ (rmorphM _) (rmorph1 _))/=.
under eq_bigr do rewrite rmorphB/= map_polyX map_polyC/=.
by rewrite -map_poly_comp (eq_map_poly (rmorph_alg _)).
Qed.

Lemma classic_cycloSplitting (F0 : fieldType) (L : splittingFieldType F0) n :
  (n%:R != 0 :> F0) -> classically
  { L' : splittingFieldType F0 & { r : L' & { iota : 'AHom(L, L') |
    <<iota @: fullv; r>>%VS = fullv & n.-primitive_root r }}}.
Proof.
move=> /(@classic_cycloExt _ L).
apply/classic_bind => -[M [r [iota rfull rprim]]]; apply/classicW.
suff splitM : SplittingField.axiom M.
  by exists (SplittingFieldType F0 M splitM), r, iota.
apply: (@SplittingFieldExt _ L ('Phi_n ^^ intr) _ iota).
rewrite -map_poly_comp (eq_map_poly (rmorph_int _)) -rfull.
by rewrite (Phi_cyclotomic rprim); apply: splitting_Fadjoin_cyclotomic.
Qed.

Lemma classic_baseCycloExt (F : fieldType) (n : nat) :
  (n%:R != 0 :> F) -> classically
   { L' : splittingFieldType F & { r : L' &
    <<1; r>>%VS = fullv & n.-primitive_root r }}.
Proof.
move=> nN0; suff: classically { L' : fieldExtType F & { r : L' &
    <<1; r>>%VS = fullv & n.-primitive_root r }}.
  apply/classic_bind => -[L [r rfull fprim]]; apply/classicW.
  have splitL : SplittingField.axiom L.
    exists (cyclotomic r n); rewrite ?cyclotomic_over// -rfull.
    exact: splitting_Fadjoin_cyclotomic.
  by exists (SplittingFieldType F L splitL), r.
pose Fo := [splittingFieldType F of F^o].
apply: classic_bind (@classic_cycloExt _ Fo n nN0).
case=> [L [r [iota rfull fprim]]]; apply/classicW.
exists L, r => //; apply/eqP; rewrite eqEsubv subvf/= -rfull.
apply/subvP => x /Fadjoin_polyP[/= p pover ->].
apply/mempx_Fadjoin/polyOverP => i /=.
have /memv_imgP[u _ ->] := polyOverP pover i.
by rewrite -(aimg1 iota) memv_img// -regular_fullv memvf.
Qed.

(******************)
(* unused for now *)
(******************)

Definition no_prim_root (F : fieldType) (n : nat) :=
  forall r : F, ~~ n.-primitive_root r.

Lemma irred_Phi (F : fieldType) (n : nat) : n%:R != 0 :> F -> (n > 2)%N ->
  no_prim_root F n <-> irreducible_poly (map_poly (intr : int -> F) 'Phi_n).
Proof.
case: n => [|[|[|n']]]//=; set n := n'.+3 => nFneq0 n_gt2; split; last first.
  move=> Phi_irred r; apply: contraTN isT => rroot.
  have /(_ _ _)/eqp_size/eqP := Phi_irred ('X - r%:P).
  rewrite size_XsubC dvdp_XsubCl.
  rewrite size_map_poly_id0 ?(monicP _) ?oner_eq0 ?Cyclotomic_monic//.
  rewrite size_Cyclotomic/= (Phi_cyclotomic rroot) root_cyclotomic// rroot eqSS.
  by rewrite ltn_eqF ?totient_gt1//; apply.
move=> Nnroot; split=> [|q sqN1 q_dvd_Phi].
  rewrite size_map_poly_id0 ?(monicP _) ?oner_eq0 ?Cyclotomic_monic//.
  by rewrite size_Cyclotomic ltnS totient_gt0.
apply: (@classic_baseCycloExt F _ nFneq0) => -[L [r rfull rprim]].
move: q_dvd_Phi; rewrite -(eqp_map [rmorphism of in_alg L])/=.
rewrite -(dvdp_map [rmorphism of in_alg L])/= -map_poly_comp/=.
have /eq_map_poly-> : in_alg L \o intr =1 intr
  by move=> x /=; rewrite -in_algE rmorph_int.
have rN1 : r \notin 1%VS.
  apply/vlineP=> -[x rx]; have /negP := Nnroot x; apply.
  by have := rprim; rewrite rx -in_algE fmorph_primitive_root.
rewrite (Phi_cyclotomic rprim) -(minPoly_cyclotomic _ rN1)//.
have q_over1 : q ^^ in_alg L \is a polyOver 1%AS by apply/polyOver1P; exists q.
move=> /(minPoly_irr q_over1)/orP[//|/eqp_size/eqP].
by rewrite size_map_poly size_poly1 (negPf sqN1).
Qed.

Lemma classic_prim_root (F : fieldType) (n : nat) :
  ~ no_prim_root F n -> classically (exists r : F, n.-primitive_root r).
Proof.
by move=> NNprim; apply/classic_ex => xP; apply: NNprim => x; apply/negP/xP.
Qed.

Lemma Nirr_prim_root (F : fieldType) (n : nat) : n%:R != 0 :> F ->
  ~ irreducible_poly (map_poly (intr : int -> F) 'Phi_n) ->
  classically (exists x : F, n.-primitive_root x).
Proof.
move=> nN0 Pirr; apply: classic_prim_root => Nprim; apply: Pirr.
case: n => [|[|[|n']]]//= in Nprim nN0 *; rewrite ?eqxx// in nN0.
- by rewrite Cyclotomic1 rmorphB rmorph1/= map_polyX; apply: irredp_XsubC.
- by rewrite Cyclotomic2 rmorphD rmorph1/= map_polyX; apply: irredp_XaddC.
exact/irred_Phi.
Qed.
