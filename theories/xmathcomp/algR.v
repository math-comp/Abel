From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra archimedean.
From mathcomp Require Import all_solvable all_field.
From Abel Require Import various.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.TTheory Num.Theory.

Local Open Scope ring_scope.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

Record algR := in_algR {algRval : algC; algRvalP : algRval \is Num.real}.

HB.instance Definition _ := [isSub for algRval].
HB.instance Definition _ := [Countable of algR by <:].
HB.instance Definition _ := [SubChoice_isSubIntegralDomain of algR by <:].
HB.instance Definition _ := [SubIntegralDomain_isSubField of algR by <:].
HB.instance Definition _ : Order.isPOrder ring_display algR :=
  Order.CancelPartial.Pcan _ valK.
Lemma total_algR : total (<=%O : rel (algR : porderType _)).
Proof. by move=> x y; apply/real_leVge/valP/valP. Qed.
HB.instance Definition _ := Order.POrder_isTotal.Build _ algR total_algR.

Lemma algRval_is_additive : additive algRval. Proof. by []. Qed.
Lemma algRval_is_multiplicative : multiplicative algRval. Proof. by []. Qed.
HB.instance Definition _ := GRing.isAdditive.Build algR algC algRval
  algRval_is_additive.
HB.instance Definition _ := GRing.isMultiplicative.Build algR algC algRval
  algRval_is_multiplicative.

Definition algR_norm (x : algR) : algR := in_algR (normr_real (val x)).
Lemma algR_ler_norm_add x y : algR_norm (x + y) <= (algR_norm x + algR_norm y).
Proof. exact: ler_normD. Qed.
Lemma algR_normr0_eq0 x : algR_norm x = 0 -> x = 0.
Proof. by move=> /(congr1 val)/normr0_eq0 ?; apply/val_inj. Qed.
Lemma algR_normrMn x n : algR_norm (x *+ n) = algR_norm x *+ n.
Proof. by apply/val_inj; rewrite /= !rmorphMn/= normrMn. Qed.
Lemma algR_normrN x : algR_norm (- x) = algR_norm x.
Proof. by apply/val_inj; apply: normrN. Qed.

Section Num.

Section withz.
Let z : algR := 0.
Lemma algR_addr_gt0 (x y : algR) : z < x -> z < y -> z < x + y.
Proof. exact: addr_gt0. Qed.
Lemma algR_ger_leVge (x y : algR) : z <= x -> z <= y -> (x <= y) || (y <= x).
Proof. exact: ger_leVge. Qed.
Lemma algR_normrM : {morph algR_norm : x y / x * y}.
Proof. by move=> *; apply/val_inj; apply: normrM. Qed.
Lemma algR_ler_def (x y : algR) : (x <= y) = (algR_norm (y - x) == y - x).
Proof. by apply: ler_def. Qed.
End withz.

HB.instance Definition _ := Num.Zmodule_isNormed.Build _ algR
  algR_ler_norm_add algR_normr0_eq0 algR_normrMn algR_normrN.
HB.instance Definition _ := Num.isNumRing.Build algR
  algR_addr_gt0 algR_ger_leVge algR_normrM algR_ler_def.
End Num.

(* TODO: remove when dropping the support for MathComp 2.2 *)
Local Fact real_floor_itv (R : archiNumDomainType) (x : R) :
       x \is Num.real -> (Num.floor x)%:~R <= x < (Num.floor x + 1)%:~R.
Proof. exact: real_floor_itv || exact: floor_itv. Qed.

Definition algR_archiFieldMixin : Num.archimedean_axiom algR.
Proof.
move=> /= x; have /andP[/= _] := real_floor_itv (valP `|x|).
set n := Num.floor _; have [n_lt0|n_ge0] := ltP n 0.
  move=> /(@lt_le_trans _ _ _ _ 0); rewrite lerz0 lezD1.
  by move=> /(_ n_lt0); rewrite normr_lt0.
move=> x_lt; exists (`|(n + 1)%R|%N); apply: lt_le_trans x_lt _.
by rewrite /= rmorphMn/= pmulrn gez0_abs// addr_ge0.
Qed.
HB.instance Definition _ := Num.NumDomain_bounded_isArchimedean.Build algR
  algR_archiFieldMixin.

Definition algRpfactor (x : algC) : {poly algR} :=
  if x \is Num.real =P true is ReflectT xR then 'X - (in_algR xR)%:P else
  'X^2 - (in_algR (Creal_Re x) *+ 2) *: 'X + ((in_algR (normr_real x))^+2)%:P.
Notation algCpfactor x := (algRpfactor x ^^ algRval).

Lemma algRpfactorRE (x : algC) (xR : x \is Num.real) :
  algRpfactor x = 'X - (in_algR xR)%:P.
Proof.
rewrite /algRpfactor; case: eqP xR => //= p1 p2.
by rewrite (bool_irrelevance p1 p2).
Qed.

Lemma algCpfactorRE (x : algC) : x \is Num.real ->
  algCpfactor x = 'X - x%:P.
Proof. by move=> xR; rewrite algRpfactorRE map_polyXsubC. Qed.

Lemma algRpfactorCE (x : algC) : x \isn't Num.real ->
  algRpfactor x =
  'X^2 - (in_algR (Creal_Re x) *+ 2) *: 'X + ((in_algR (normr_real x))^+2)%:P.
Proof. by rewrite /algRpfactor; case: eqP => // p; rewrite p. Qed.

Lemma algCpfactorCE (x : algC) : x \isn't Num.real ->
  algCpfactor x = ('X - x%:P) * ('X - x^*%:P).
Proof.
move=> xNR; rewrite algRpfactorCE//=.
rewrite rmorphD /= rmorphB/= !map_polyZ !map_polyXn/= map_polyX.
rewrite (map_polyC algRval)/=.
rewrite mulrBl !mulrBr -!addrA; congr (_ + _).
rewrite opprD addrA opprK -opprD -rmorphM/= -normCK; congr (- _ + _).
rewrite mulrC !mul_polyC -scalerDl.
rewrite [x in RHS]algCrect conjC_rect ?Creal_Re ?Creal_Im//.
by rewrite addrACA addNr addr0.
Qed.

Lemma algCpfactorE x :
  algCpfactor x = ('X - x%:P) * ('X - x^*%:P) ^+ (x \isn't Num.real).
Proof.
by have [/algCpfactorRE|/algCpfactorCE] := boolP (_ \is _); rewrite ?mulr1.
Qed.

Lemma size_algCpfactor x : size (algCpfactor x) = (x \isn't Num.real).+2.
Proof.
have [xR|xNR] := boolP (_ \is _); first by rewrite algCpfactorRE// size_XsubC.
by rewrite algCpfactorCE// size_mul ?size_XsubC ?polyXsubC_eq0.
Qed.

Lemma size_algRpfactor x : size (algRpfactor x) = (x \isn't Num.real).+2.
Proof. by have := size_algCpfactor x; rewrite size_map_poly. Qed.

Lemma algCpfactor_eq0 x : (algCpfactor x == 0) = false.
Proof. by rewrite -size_poly_eq0 size_algCpfactor. Qed.

Lemma algRpfactor_eq0 x : (algRpfactor x == 0) = false.
Proof. by rewrite -size_poly_eq0 size_algRpfactor. Qed.

Lemma algCpfactorCgt0 x y : x \isn't Num.real -> y \is Num.real ->
  (algCpfactor x).[y] > 0.
Proof.
move=> xNR yR; rewrite algCpfactorCE// hornerM !hornerXsubC.
rewrite [x]algCrect conjC_rect ?Creal_Re ?Creal_Im// !opprD !addrA opprK.
rewrite -subr_sqr exprMn sqrCi mulN1r opprK ltr_wpDl//.
- by rewrite real_exprn_even_ge0// ?rpredB// ?Creal_Re.
by rewrite real_exprn_even_gt0 ?Creal_Im ?orTb//=; apply/eqP/Creal_ImP.
Qed.

Lemma algRpfactorR_mul_gt0 (x a b : algC) :
    x \is Num.real -> a \is Num.real -> b \is Num.real ->
    a <= b ->
    ((algCpfactor x).[a] * (algCpfactor x).[b] <= 0) =
  (a <= x <= b).
Proof.
move=> xR aR bR ab; rewrite !algCpfactorRE// !hornerXsubC.
have [lt_xa|lt_ax|->]/= := real_ltgtP xR aR; last first.
- by rewrite subrr mul0r lexx ab.
- by rewrite nmulr_rle0 ?subr_lt0 ?subr_ge0.
rewrite pmulr_rle0 ?subr_gt0// subr_le0.
by apply: negbTE; rewrite -real_ltNge// (lt_le_trans lt_xa).
Qed.

Lemma monic_algCpfactor x : algCpfactor x \is monic.
Proof. by rewrite algCpfactorE rpredM ?rpredX ?monicXsubC. Qed.

Lemma monic_algRpfactor x : algRpfactor x \is monic.
Proof. by have := monic_algCpfactor x; rewrite map_monic. Qed.

Lemma poly_algR_pfactor (p : {poly algR}) :
  { r : seq algC |
    p ^^ algRval = val (lead_coef p) *: \prod_(z <- r) algCpfactor z }.
Proof.
wlog p_monic : p / p \is monic => [hwlog|].
  have [->|pN0] := eqVneq p 0.
    by exists [::]; rewrite lead_coef0/= rmorph0 scale0r.
  have [|r] := hwlog ((lead_coef p)^-1 *: p).
    by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0//.
  rewrite !lead_coefZ mulVf ?lead_coef_eq0//= scale1r.
  rewrite map_polyZ/= => /(canRL (scalerKV _))->; first by exists r.
  by rewrite fmorph_eq0 lead_coef_eq0.
suff: {r : seq algC | p ^^ algRval = \prod_(z <- r) algCpfactor z}.
  by move=> [r rP]; exists r; rewrite rP (monicP _)// scale1r.
have [/= r pr] := closed_field_poly_normal (p ^^ algRval).
rewrite (monicP _) ?monic_map ?scale1r// {p_monic} in pr *.
have [n] := ubnP (size r).
elim: n r => // n IHn [|x r]/= in p pr *.
 by exists [::]; rewrite pr !big_nil.
rewrite ltnS => r_lt.
have xJxr : x^* \in x :: r.
  rewrite -root_prod_XsubC -pr.
  have /eq_map_poly-> : algRval =1 Num.conj_op \o algRval.
    by move=> a /=; rewrite (CrealP (algRvalP _)).
  by rewrite map_poly_comp mapf_root pr root_prod_XsubC mem_head.
have xJr : (x \isn't Num.real) ==> (x^* \in r) by rewrite implyNb CrealE.
have pxdvdC : algCpfactor x %| p ^^ algRval.
  rewrite pr algCpfactorE big_cons/= dvdp_mul2l ?polyXsubC_eq0//.
  by case: (_ \is _) xJr; rewrite ?dvd1p// dvdp_XsubCl root_prod_XsubC.
pose pr'x := p %/ algRpfactor x.
have [||r'] := IHn (if x \is Num.real then r else rem x^* r) pr'x; last 2 first.
- by case: (_ \is _) in xJr *; rewrite ?size_rem// (leq_ltn_trans (leq_pred _)).
- move=> /eqP; rewrite map_divp -dvdp_eq_mul ?algCpfactor_eq0//= => /eqP->.
  by exists (x :: r'); rewrite big_cons mulrC.
rewrite map_divp/= pr big_cons algCpfactorE/=.
rewrite divp_pmul2l ?expf_neq0 ?polyXsubC_eq0//.
case: (_ \is _) => /= in xJr *; first by rewrite divp1//.
by rewrite (big_rem _ xJr)/= mulKp ?polyXsubC_eq0.
Qed.

Definition algR_rcfMixin : Num.real_closed_axiom algR.
Proof.
move=> p a b le_ab /andP[pa_le0 pb_ge0]/=.
case: ltgtP pa_le0 => //= pa0 _; last first.
  by exists a; rewrite ?lexx// rootE pa0.
case: ltgtP pb_ge0 => //= pb0 _; last first.
  by exists b; rewrite ?lexx ?andbT// rootE -pb0.
have p_neq0 : p != 0 by apply: contraTneq pa0 => ->; rewrite horner0 ltxx.
have {pa0 pb0} pab0 : p.[a] * p.[b] < 0 by rewrite pmulr_llt0.
wlog p_monic : p p_neq0 pab0 / p \is monic => [hwlog|].
  have [|||x axb] := hwlog ((lead_coef p)^-1 *: p).
  - by rewrite scaler_eq0 invr_eq0 lead_coef_eq0 (negPf p_neq0).
  - rewrite !hornerE/= -mulrA mulrACA -expr2 pmulr_rlt0//.
    by rewrite exprn_even_gt0//= invr_eq0 lead_coef_eq0.
  - by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0 ?eqxx.
  by rewrite rootZ ?invr_eq0 ?lead_coef_eq0//; exists x.
have /= [rs prs] := poly_algR_pfactor p.
rewrite (monicP _) ?monic_map// scale1r {p_monic} in prs.
pose ab := [pred x | val a <= x <= val b].
have abR : {subset ab <= Num.real}.
  move=> x /andP[+ _].
  by rewrite -subr_ge0 => /ger0_real; rewrite rpredBr// algRvalP.
wlog : p pab0 {p_neq0 prs} /
    p ^^ algRval = \prod_(x <- rs | x \in ab) ('X - x%:P) => [hw|].
  move: prs; rewrite -!rmorph_prod => /map_poly_inj.
  rewrite (bigID ab)/=; set q := (X in X * _); set u := (X in _ * X) => pqu.
  have [||] := hw q; last first.
  - by move=> x; exists x => //; rewrite pqu rootM q0.
  - by rewrite rmorph_prod/=; under eq_bigr do rewrite algCpfactorRE ?abR//.
  have := pab0; rewrite pqu !hornerM mulrACA [_ * _ * _ < 0]pmulr_llt0//.
  rewrite !horner_prod -big_split/= prodr_gt0// => x.
  have [xR|xNR] := boolP (x \is Num.real); last first.
    rewrite (_ : (0 < ?[a]) = (algRval 0 < algRval ?a))//=.
    by rewrite -!horner_map/= mulr_gt0 ?algCpfactorCgt0 ?algRvalP.
  apply: contraNT; rewrite -leNgt.
  rewrite (_ : (?[a] <= 0) = (algRval ?a <= algRval 0))//= -!horner_map/=.
  by rewrite algRpfactorR_mul_gt0 ?algRvalP.
rewrite -big_filter; have := filter_all ab rs.
set rsab := filter _ _.
have: all (mem Num.real) rsab.
  by apply/allP => x; rewrite mem_filter => /andP[/abR].
case: rsab => [_ _|x rsab]/=; rewrite (big_nil, big_cons).
  move=> pval1; move: pab0.
  have /map_poly_inj-> : p ^^ algRval = 1 ^^ algRval by rewrite rmorph1.
  by rewrite !hornerE ltr10.
move=> /andP[xR rsabR] /andP[axb arsb] prsab.
exists (in_algR xR) => //=.
by rewrite -(mapf_root algRval)//= prsab rootM root_XsubC eqxx.
Qed.
HB.instance Definition _ := Num.RealField_isClosed.Build algR algR_rcfMixin.
