From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import all_field finmap polyrcf qe_rcf_th.
From Abel Require Import Sn_solvable galmx diag.

(******************************************************************************)
(* Tags for the difficulty :                                                  *)
(*    (** Easy **) = the theory is already here, should not take more than    *)
(*                   3 lines (probably !)                                     *)
(*    (** Ok **)   = not the most easy lemma, and not really difficult either *)
(*    (** Hard **) = hard or long, or painful                                 *)
(*    (** N/A **)  = no idea (there shouldn't be any N/A tags left at the     *)
(*                   next meeting)                                            *)
(*    (** No **)   = this lemma should not be proven : its statement is       *)
(*                   unstable or actually not provable (further discussion is *)
(*                   needed)                                                  *)
(*                                                                            *)
(* radical n x U V := V is a pure radical extension of U, by element x, with  *)
(*                    degree n                                                *)
(* r.-tower n A U sU := U :: sU is a tower of extensions, and for each        *)
(*                      extension, there exists an x in A, and an m <= n such *)
(*                      that r m x                                            *)
(* r.-ext U V := there exists a n, an A and a tower of extension which ends   *)
(*               exactly on V, which is an r.-tower n A                       *)
(* solvable_by r E F := E <= F and there exists a field K such that F <= K    *)
(*                      and K is an extension which respects r (r.-ext E K)   *)
(* solvable_by_radicals_poly E F p := if F is a splitting field of p on E     *)
(*                                    then F is solvable_by radicals on E     *)
(* pradical n x U V := prime n && radical n x U V                             *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* missing from coq or mathcomp *)
Inductive iffT T1 T2 : Type := Record {iffT12 : T1 -> T2 ; iffT21 : T2 -> T1}.
Notation "T1 <=> T2" := (iffT T1 T2) (at level 95) : type_scope.


Section Char0MorphismsIdomain.

Variable (R : idomainType).
Hypothesis charR0 : [char R] =i pred0.

Implicit Type z : int.

Lemma char0_intr_eq0 (z : int) : ((z%:~R : R) == 0) = (z == 0).
Proof.
suff hPos (m : nat) : (m%:~R == 0 :> R) = (Posz m == 0).
  by case: z => [m | m] => //; rewrite NegzE rmorphN /= !oppr_eq0.
by rewrite [m%:~R]/(m%:R); move/charf0P: (charR0)->.
Qed.

Lemma char0_intr_inj : injective (fun i => i%:~R : R).
Proof.
move=> i j /eqP; rewrite -subr_eq0 -rmorphB /= char0_intr_eq0 subr_eq0.
by move/eqP.
Qed.

End Char0MorphismsIdomain.

Definition char0_ratr (F : fieldType) (charF0 : [char F] =i pred0) := (@ratr F).

Lemma char0_ratrE (F : fieldType) (charF0 : [char F] =i pred0) :
  char0_ratr charF0 = ratr.
Proof. by []. Qed.

Section Char0MorphismsField.

Variable (F : fieldType).
Hypothesis charF0 : [char F] =i pred0.

Local Notation ratrF := (char0_ratr charF0).

(* Lemma char0_ratr0 : ratrF 0 = 0. *)
(* Proof. by rewrite /ratr divr1. Qed. *)

(* Lemma char0_ratr1 : ratrF 1 = 1. *)
(* Proof. by rewrite /ratr divr1. Qed. *)

Fact char0_ratr_is_rmorphism : rmorphism ratrF.
Proof.
rewrite /char0_ratr.
have injZtoQ: @injective rat int intr by apply: intr_inj.
have nz_den x: (denq x)%:~R != 0 :> F by rewrite char0_intr_eq0 // denq_eq0.
do 2?split; rewrite /ratr ?divr1 // => x y; last first.
  rewrite mulrC mulrAC; apply: canLR (mulKf (nz_den _)) _; rewrite !mulrA.
  do 2!apply: canRL (mulfK (nz_den _)) _; rewrite -!rmorphM; congr _%:~R.
  apply: injZtoQ; rewrite !rmorphM [x * y]lock /= !numqE -lock.
  by rewrite -!mulrA mulrA mulrCA -!mulrA (mulrCA y).
apply: (canLR (mulfK (nz_den _))); apply: (mulIf (nz_den x)).
rewrite mulrAC mulrBl divfK ?nz_den // mulrAC -!rmorphM.
apply: (mulIf (nz_den y)); rewrite mulrAC mulrBl divfK ?nz_den //.
rewrite -!(rmorphM, rmorphB); congr _%:~R; apply: injZtoQ.
rewrite !(rmorphM, rmorphB) [_ - _]lock /= -lock !numqE.
by rewrite (mulrAC y) -!mulrBl -mulrA mulrAC !mulrA.
Qed.

Canonical char0_ratr_additive  := Additive char0_ratr_is_rmorphism.
Canonical char0_ratr_rmorphism := RMorphism char0_ratr_is_rmorphism.

End Char0MorphismsField.


Section NumberFieldsProps.

Variable (L : fieldExtType rat).

Lemma char_ext : [char L] =i pred0. (* this works more generally for `lalgType rat` *)
Proof. by move=> x; rewrite char_lalg Num.Theory.char_num. Qed.
Hint Resolve char_ext : core.

Lemma rat_extratr0 : ratr 0 = 0 :> L.
(* watch out: no // to discharge charL as it is in Prop :) *)
Proof. by rewrite -char0_ratrE raddf0. Qed.

Notation ratrL := (char0_ratr char_ext).

Lemma char0_ratrN : {morph ratrL : x / - x}. Proof. exact: raddfN. Qed.
Lemma char0_ratrD : {morph ratrL : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma char0_ratrB : {morph ratrL : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma char0_ratrMn n : {morph ratrL : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma char0_ratrMNn n : {morph ratrL : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma char0_ratr_sum I r (P : pred I) E :
  ratrL (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) ratrL (E i).
Proof. exact: raddf_sum. Qed.
 Lemma char0_ratrMsign n : {morph ratrL : x / (- 1) ^+ n * x}.
Proof. exact: raddfMsign. Qed.

Lemma char0_ratr1 : ratrL 1 = 1. Proof. by exact: rmorph1. Qed.
Lemma char0_ratrM : {morph ratrL : x y  / x * y}. Proof. by exact: rmorphM. Qed.

Lemma char0_ratr_prod I r (P : pred I) E :
  ratrL (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) ratrL (E i).
Proof. exact: rmorph_prod. Qed.

Lemma char0_ratrX n : {morph ratrL : x / x ^+ n}.
Proof. exact: rmorphX.  Qed.

Lemma char0_nat n : ratrL n%:R = n%:R. Proof. exact: ratr_nat. Qed.

Lemma char0_ratrN1 : ratrL (- 1) = (- 1). Proof. exact: rmorphN1. Qed.

Lemma char0_ratr_sign n : ratrL ((- 1) ^+ n) = (- 1) ^+ n.
Proof. by exact: rmorph_sign. Qed.

Lemma char0_ratr_inj : injective ratrL.
Proof.
suff inj0 z : ratrL z = 0 -> z = 0.
  move=> x y /eqP; rewrite -subr_eq0 -char0_ratrB => /eqP /inj0 /eqP.
  by rewrite subr_eq0 => /eqP.
rewrite /ratrL /ratr; move/eqP; rewrite mulf_eq0 invr_eq0 orbC.
have /negPf-> /= : (denq z)%:~R != 0 :> L by rewrite char0_intr_eq0 // denq_eq0.
by rewrite char0_intr_eq0 // numq_eq0 => /eqP.
Qed.

Lemma char0_rmorph_int z : ratrL z%:~R =  z%:~R. Proof. exact: rmorph_int. Qed.

(* Are these two necessary? *)
Lemma char0_ratr_eq_nat x n : (ratrL x == n%:R) = (x == n%:R).
Proof. apply: rmorph_eq_nat; exact: char0_ratr_inj. Qed.

Lemma char0_ratr_eq1 x : (ratrL x == 1) = (x == 1).
Proof. exact: char0_ratr_eq_nat 1%N. Qed.

End NumberFieldsProps.


(* Field extensions in characteristic 0 are always separable *)
Section FieldExtChar0.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (charL : [char L] =i pred0).
Implicit Types (E F : {subfield L}) (p : {poly L}) (x : L).

(* (** Easy **) *)
(* Lemma subv_splittingFieldFor : (E <= F)%VS. *)
(* Proof. case: splitting_p => b pE <-; exact: subv_adjoin_seq. Qed. *)

(** Ok **)
Lemma root_make_separable p x : root p x = root (p %/ gcdp p p^`()) x.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite div0p root0.
have := dvdp_gcdl p p^`(); rewrite dvdp_eq => /eqP p_eq_pDgMg.
apply/idP/idP => [rpx|]; last first.
  move=> dx_eq0; rewrite p_eq_pDgMg.
  by rewrite /root hornerM mulf_eq0 (eqP dx_eq0) eqxx.
have [[|m] [q]] := multiplicity_XsubC p x; rewrite p_neq0/= => rNqx p_eq.
  by rewrite p_eq mulr1 (negPf rNqx) in rpx.
have q_neq0 : q != 0; first by apply: contra_eq_neq p_eq => ->; rewrite mul0r.
rewrite p_eq; set f := ('X - _).
have f_neq0 : f != 0 by rewrite polyXsubC_eq0.
rewrite -dvdp_XsubCl derivM deriv_exp/= derivXsubC mul1r.
rewrite -mulr_natl exprS !mulrA -mulrDl.
set r := (_ * f + _)%R.
have Nrx : ~~ root r x.
  rewrite /root !hornerE subrr mulr0 add0r mulf_neq0//.
  have -> : m.+1%:R = m.+1%:R%:P :> {poly L} by rewrite !raddfMn.
  rewrite hornerC natf_neq0/= (eq_pnat _ (eq_negn charL))/=.
  by apply/andP; split => //; apply/allP.
rewrite (eqp_dvdr _ (eqp_divr _ (gcdp_mul2r _ _ _))).
rewrite divp_pmul2r//; last 2 first.
- by rewrite ?expf_neq0 ?polyXsubC_eq0.
- by rewrite ?gcdp_eq0 negb_and ?mulf_neq0.
rewrite mulrC -divp_mulA ?dvdp_mulr//.
have := dvdp_gcdl (f * q) r; rewrite Gauss_dvdpr//.
by rewrite coprimep_XsubC root_gcd (negPf Nrx) andbF.
Qed.

Lemma char0_minPoly_separable x E : separable_poly (minPoly E x).
Proof.
have pE := minPolyOver E x; set p := minPoly E x.
suff /eqp_separable-> : p %= p %/ gcdp p p^`().
  by rewrite make_separable ?monic_neq0 ?monic_minPoly.
rewrite /eqp divp_dvd ?dvdp_gcdl// andbT.
rewrite minPoly_dvdp ?divp_polyOver ?gcdp_polyOver ?polyOver_deriv//.
by rewrite -root_make_separable// root_minPoly.
Qed.

Lemma char0_separable_element x E : separable_element E x.
Proof. exact: char0_minPoly_separable. Qed.

Lemma char0_separable E F : separable E F.
Proof. by apply/separableP => y _; apply: char0_separable_element. Qed.

Lemma char0_galois E F : (E <= F)%VS -> normalField E F -> galois E F.
Proof. by move=> sEF nEF; apply/and3P; split=> //; apply: char0_separable. Qed.

End FieldExtChar0.

Lemma tpermJt (X : finType) (x y z : X) : x != z -> y != z ->
   (tperm x z ^ tperm x y)%g = tperm y z.
Proof.
by move=> neq_xz neq_yz; rewrite tpermJ tpermL [tperm _ _ z]tpermD.
Qed.

Lemma gen_tperm (X : finType) x :
  <<[set tperm x y | y in X]>>%g = [set: {perm X}].
Proof.
apply/eqP; rewrite eqEsubset subsetT/=; apply/subsetP => s _.
have [ts -> _] := prod_tpermP s; rewrite group_prod// => -[/= y z] _.
have [<-|Nyz] := eqVneq y z; first by rewrite tperm1 group1.
have [<-|Nxz] := eqVneq x z; first by rewrite tpermC mem_gen ?mem_imset.
by rewrite -(tpermJt Nxz Nyz) groupJ ?mem_gen ?mem_imset.
Qed.

Lemma gen_tperm_step n (k : 'I_n.+2) : coprime n.+2 k ->
  <<[set tperm i (i + k) | i : 'I_n.+2]>>%g = [set: 'S_n.+2].
Proof.
rewrite -unitZpE// natr_Zp => k_unit.
apply/eqP; rewrite eqEsubset subsetT/= -(gen_tperm 0)/= gen_subG.
apply/subsetP => s /imsetP[/= i _ ->].
rewrite -[i](mulVKr k_unit) -[_ * i]natr_Zp mulr_natr.
elim: (val _) => //= {i} [|[|i] IHi]; first by rewrite tperm1 group1.
  by rewrite mulrSr mem_gen//; apply/imsetP; exists 0.
have [->|kS2N0] := eqVneq (k *+ i.+2) 0; first by rewrite tperm1 group1.
have kSSneqkS : k *+ i.+2 != k *+ i.+1.
  rewrite -subr_eq0 -mulrnBr// subSnn mulr1n.
  by apply: contraTneq k_unit => ->; rewrite unitr0.
rewrite -(@tpermJt _ (k *+ i.+1)) 1?eq_sym//.
rewrite groupJ// 1?tpermC// mulrSr 1?tpermC.
by rewrite mem_gen//; apply/imsetP; exists (k *+ i.+1).
Qed.

Lemma gen_tpermS n : <<[set tperm i (i + 1) | i : 'I_n.+2]>>%g = [set: 'S_n.+2].
Proof. by rewrite gen_tperm_step// coprimen1. Qed.

Lemma iter_addr (V : zmodType) n x y : iter n (+%R x) y = x *+ n + y :> V.
Proof. by elim: n => [|n ih]; rewrite ?add0r //= ih mulrS addrA. Qed.

Lemma perm_add1X n (j k : 'I_n.+2) : (perm (addrI 1%R) ^+ j)%g k = j + k.
Proof. by rewrite permX (eq_iter (permE _)) iter_addr natr_Zp. Qed.

Lemma gen_tpermn_cycle n (i j : 'I_n.+2)
    (c := perm (addrI 1)) : coprime n.+2 (j - i)%R ->
  <<[set tperm i j ; c]>>%g = [set: 'S_n.+2].
Proof.
move=> jBi_coprime; apply/eqP; rewrite eqEsubset subsetT/=.
rewrite -(gen_tperm_step jBi_coprime) gen_subG.
apply/subsetP => s /imsetP[/= k _ ->].
suff -> : tperm k (k + (j - i)) = (tperm i j ^ c ^+ (k - i)%R)%g.
  by rewrite groupJ ?groupX ?mem_gen ?inE ?eqxx ?orbT.
by rewrite tpermJ !perm_add1X addrNK addrAC addrA.
Qed.

Lemma gen_tperm01_cycle n (c := perm (addrI 1)) :
  <<[set tperm 0 1%R ; c]>>%g = [set: 'S_n.+2].
Proof. by rewrite gen_tpermn_cycle// subr0 coprimen1. Qed.

Lemma prime_orbit (X : finType) x c :
  prime #|X| -> #[c]%g = #|X| -> orbit 'P <[c]> x = [set: X].
Proof.
move=> X_prime ord_c; have dvd_orbit y : (#|orbit 'P <[c]> y| %| #|X|)%N.
  by rewrite (dvdn_trans (dvdn_orbit _ _ _))// [#|<[_]>%g|]ord_c.
have [] := boolP [forall y, #|orbit 'P <[c]> y| == 1%N].
  move=> /'forall_eqP-/(_ _)/card_orbit1 orbit1; suff c_eq_1 : c = 1%g.
    by rewrite c_eq_1 ?order1 in ord_c; rewrite -ord_c in X_prime.
  apply/permP => y; rewrite perm1.
  suff: c y \in orbit 'P <[c]> y by rewrite orbit1 inE => /eqP->.
  by apply/orbitP; exists c => //; rewrite mem_gen ?inE.
move=> /forallPn[y orbit_y_neq0]; have orbit_y : orbit 'P <[c]> y = [set: X].
  apply/eqP; rewrite eqEcard subsetT cardsT.
  by have /(prime_nt_dvdP X_prime orbit_y_neq0)<-/= := dvd_orbit y.
by have /orbit_in_eqP-> : x \in orbit 'P <[c]> y; rewrite ?subsetT ?orbit_y.
Qed.

Lemma prime_astab (X : finType) (x : X) (c : {perm X}) :
  prime #|X| -> #[c]%g = #|X| -> 'C_<[c]>[x | 'P]%g = 1%g.
Proof.
move=> X_prime ord_c; have /= := card_orbit_stab 'P [group of <[c]>%g] x.
rewrite prime_orbit// cardsT [#|<[_]>%g|]ord_c -[RHS]muln1 => /eqP.
by rewrite eqn_mul2l gtn_eqF ?prime_gt0//= -trivg_card1 => /eqP.
Qed.

Lemma expgDzmod (gT : finGroupType) (x : gT) d (n m : 'Z_d) : (d > 0)%N ->
  (#[x]%g %| d)%N -> (x ^+ (n + m)%R)%g = (x ^+ n * x ^+ m)%g.
Proof.
move=> d_gt0 xdvd; apply/eqP; rewrite -expgD eq_expg_mod_order/= modn_dvdm//.
by case: d d_gt0 {m n} xdvd => [|[|[]]]//= _; rewrite dvdn1 => /eqP->.
Qed.

Lemma eq_expg_ord (gT : finGroupType) (x : gT) d (n m : 'I_d) :
  (d <= #[x]%g)%N -> ((x ^+ m)%g == (x ^+ n)%g) = (m == n).
Proof.
by move=> d_leq; rewrite eq_expg_mod_order !modn_small// (leq_trans _ d_leq).
Qed.

Lemma gen_tperm_cycle (X : finType) x y c : prime #|X| ->
  x != y -> #[c]%g = #|X| ->
  <<[set tperm x y; c]>>%g = ('Sym_X)%g.
Proof.
move=> Xprime neq_xy ord_c; apply/eqP; rewrite eqEsubset subsetT/=.
have c_gt1 : (1 < #[c]%g)%N by rewrite ord_c prime_gt1.
have cppSS : #[c]%g.-2.+2 = #|X| by rewrite ?prednK ?ltn_predRL.
pose f (i : 'Z_#[c]%g) : X := Zpm i x.
have [g fK gK] : bijective f.
  apply: inj_card_bij; rewrite ?cppSS ?card_ord// /f /Zpm => i j cijx.
  pose stabx := ('C_<[c]>[x | 'P])%g.
  have cjix : (c ^+ (j - i)%R)%g x = x.
    by apply: (@perm_inj _ (c ^+ i)%g); rewrite -permM -expgDzmod// addrNK.
  have : (c ^+ (j - i)%R)%g \in stabx.
    by rewrite !inE ?groupX ?mem_gen ?sub1set ?inE// ['P%act _ _]cjix eqxx.
  rewrite [stabx]prime_astab// => /set1gP.
  move=> /(congr1 (mulg (c ^+ i))); rewrite -expgDzmod// addrC addrNK mulg1.
  by move=> /eqP; rewrite eq_expg_ord// ?cppSS ?ord_c// => /eqP->.
pose gsf s := g \o s \o f.
have gsf_inj (s : {perm X}) : injective (gsf s).
  apply: inj_comp; last exact: can_inj fK.
  by apply: inj_comp; [exact: can_inj gK|exact: perm_inj].
pose fsg s := f \o s \o g.
have fsg_inj (s : {perm _}) : injective (fsg s).
  apply: inj_comp; last exact: can_inj gK.
  by apply: inj_comp; [exact: can_inj fK|exact: perm_inj].
have gsf_morphic : morphic 'Sym_X (fun s => perm (gsf_inj s)).
  apply/morphicP => u v _ _; apply/permP => /= i.
  by rewrite !permE/= !permE /gsf /= gK permM.
pose phi := morphm gsf_morphic; rewrite /= in phi.
have phi_inj : ('injm phi)%g.
  apply/subsetP => /= u /mker/=; rewrite morphmE => gsfu1.
  apply/set1gP/permP=> z; have /permP/(_ (g z)) := gsfu1.
  by rewrite !perm1 permE /gsf/= gK => /(can_inj gK).
have phiT : (phi @* 'Sym_X)%g = [set: {perm 'Z_#[c]%g}].
  apply/eqP; rewrite eqEsubset subsetT/=; apply/subsetP => /= u _.
  apply/morphimP; exists (perm (fsg_inj u)); rewrite ?in_setT//.
  by apply/permP => /= i; rewrite morphmE permE /gsf/fsg/= permE/= !fK.
have f0 : f 0 = x by rewrite /f /Zpm permX.
pose k := g y; have k_gt0 : (k > 0)%N.
  by rewrite lt0n (val_eqE k 0) -(can_eq fK) eq_sym gK f0.
have phixy : phi (tperm x y) = tperm 0 k.
  apply/permP => i; rewrite permE/= /gsf/=; apply: (canLR fK).
  by rewrite !permE/= -f0 -[y]gK !(can_eq fK) -!fun_if.
have phic : phi c = perm (addrI 1%R).
  apply/permP => i; rewrite permE /gsf/=; apply: (canLR fK).
  by rewrite !permE /f /Zpm -permM addrC expgDzmod.
rewrite -(injmSK phi_inj)//= morphim_gen/= ?subsetT//= -/phi.
rewrite phiT /morphim !setTI/= -/phi imsetU1 imset_set1/= phixy phic.
suff /gen_tpermn_cycle<- : coprime #[c]%g.-2.+2 (k - 0)%R by [].
by rewrite subr0 prime_coprime ?gtnNdvd// ?cppSS.
Qed.

Section missing_from_mathcomp.

Lemma dvdz_charf (R : ringType) (p : nat) :
  p \in [char R] -> forall n : int, (p %| n)%Z = (n%:~R == 0 :> R).
Proof.
move=> charRp [] n; rewrite [LHS](dvdn_charf charRp)//.
by rewrite NegzE abszN rmorphN// oppr_eq0.
Qed.

Lemma dvdp_exp_XsubC (R : idomainType) (p : {poly R}) (c : R) n :
  reflect (exists2 k, (k <= n)%N & p %= ('X - c%:P) ^+ k)
          (p %| ('X - c%:P) ^+ n).
Proof.
apply: (iffP idP) => [|[k lkn /eqp_dvdl->]]; last by rewrite dvdp_exp2l.
move=> /Pdiv.WeakIdomain.dvdpP[[/= a q] a_neq0].
have [m [r]] := multiplicity_XsubC p c; have [->|pN0]/= := eqVneq p 0.
  rewrite mulr0 => _ _ /eqP;  rewrite scale_poly_eq0 (negPf a_neq0)/=.
  by rewrite expf_eq0/= andbC polyXsubC_eq0.
move=> rNc ->; rewrite mulrA => eq_qrm; exists m.
  have: ('X - c%:P) ^+ m %| a *: ('X - c%:P) ^+ n by rewrite eq_qrm dvdp_mull.
  by rewrite (eqp_dvdr _ (eqp_scale _ _))// dvdp_Pexp2l// size_XsubC.
suff /eqP : size r = 1%N.
  by rewrite size_poly_eq1 => /eqp_mulr/eqp_trans->//; rewrite mul1r eqpxx.
have : r %| a *: ('X - c%:P) ^+ n by rewrite eq_qrm mulrAC dvdp_mull.
rewrite (eqp_dvdr _ (eqp_scale _ _))//.
move: rNc; rewrite -coprimep_XsubC => /(coprimep_expr n) /coprimepP.
by move=> /(_ _ (dvdpp _)); rewrite -size_poly_eq1 => /(_ _)/eqP.
Qed.

Lemma eisenstein (p : nat) (q : {poly int}) : prime p -> (size q != 1)%N ->
  (~~ (p %| lead_coef q))%Z -> (~~ ((p : int) ^+ 2 %| q`_0))%Z ->
  (forall i, (i < (size q).-1)%N -> p %| q`_i)%Z ->
  irreducible_poly (map_poly (intr : int -> rat) q).
Proof.
move=> p_prime qN1 Ndvd_pql Ndvd_pq0 dvd_pq.
have qN0 : q != 0 by rewrite -lead_coef_eq0; apply: contraNneq Ndvd_pql => ->.
split.
   rewrite size_map_poly_id0 ?intr_eq0 ?lead_coef_eq0//.
   by rewrite ltn_neqAle eq_sym qN1 size_poly_gt0.
move=> f' +/dvdpP_rat_int[f [d dN0 feq]]; rewrite {f'}feq size_scale// => fN1.
move=> /= [g q_eq]; rewrite q_eq (eqp_trans (eqp_scale _ _))//.
have fN0 : f != 0 by apply: contra_neq qN0; rewrite q_eq => ->; rewrite mul0r.
have gN0 : g != 0 by apply: contra_neq qN0; rewrite q_eq => ->; rewrite mulr0.
rewrite size_map_poly_id0 ?intr_eq0 ?lead_coef_eq0// in fN1.
have [/eqP[/size_poly1P[c cN0 ->]]|gN1] := eqVneq (size g) 1%N.
  by rewrite mulrC mul_polyC map_polyZ/= eqp_sym eqp_scale// intr_eq0.
have c_neq0 : (lead_coef q)%:~R != 0 :> 'F_p
   by rewrite -(dvdz_charf (char_Fp _)).
have : map_poly (intr : int -> 'F_p) q = (lead_coef q)%:~R *: 'X^(size q).-1.
  apply/val_inj/(@eq_from_nth _ 0) => [|i]; rewrite size_map_poly_id0//.
    by rewrite size_scale// size_polyXn -polySpred.
  move=> i_small; rewrite coef_poly i_small coefZ coefXn lead_coefE.
  move: i_small; rewrite polySpred// ltnS/=.
  case: ltngtP => // [i_lt|->]; rewrite (mulr1, mulr0)//= => _.
  by apply/eqP; rewrite -(dvdz_charf (char_Fp _))// dvd_pq.
rewrite [in LHS]q_eq rmorphM/=.
set c := (X in X *: _); set n := (_.-1).
set pf := map_poly _ f; set pg := map_poly _ g => pfMpg.
have dvdXn (r : {poly _}) : size r != 1%N -> r %| c *: 'X^n -> r`_0 = 0.
  move=> rN1; rewrite (eqp_dvdr _ (eqp_scale _ _))//.
  rewrite -['X]subr0; move=> /dvdp_exp_XsubC[k lekn]; rewrite subr0.
  move=> /eqpP[u /andP[u1N0 u2N0]]; have [->|k_gt0] := posnP k.
    move=> /(congr1 (size \o val))/eqP.
    by rewrite /= !size_scale// size_polyXn (negPf rN1).
  move=> /(congr1 (fun p : {poly _} => p`_0))/eqP.
  by rewrite !coefZ coefXn ltn_eqF// mulr0 mulf_eq0 (negPf u1N0) => /eqP.
suff : ((p : int) ^+ 2 %| q`_0)%Z by rewrite (negPf Ndvd_pq0).
have := c_neq0; rewrite q_eq coefM big_ord1.
rewrite lead_coefM rmorphM mulf_eq0 negb_or => /andP[lpfN0 qfN0].
have pfN1 : size pf != 1%N by rewrite size_map_poly_id0.
have pgN1 : size pg != 1%N by rewrite size_map_poly_id0.
have /(dvdXn _ pgN1) /eqP : pg %| c *: 'X^n by rewrite -pfMpg dvdp_mull.
have /(dvdXn _ pfN1) /eqP : pf %| c *: 'X^n by rewrite -pfMpg dvdp_mulr.
by rewrite !coef_map// -!(dvdz_charf (char_Fp _))//; apply: dvdz_mul.
Qed.

Lemma prodrMl {R : comRingType} {I : finType} (A : pred I) (x : R) F :
  \prod_(i in A) (x * F i) = x ^+ #|A| * \prod_(i in A) F i.
Proof.
rewrite -sum1_card; elim/big_rec3: _; first by rewrite expr0 mulr1.
by move=> i y p z iA ->; rewrite mulrACA exprS.
Qed.

Lemma expr_sum {R : ringType} {T : Type} (x : R) (F : T -> nat) P s :
  x ^+ (\sum_(i <- s | P i) F i) = \prod_(i <- s | P i) x ^+ (F i).
Proof. by apply: big_morph; [exact: exprD | exact: expr0]. Qed.

Lemma lead_coef_XnsubC {R : ringType} n (c : R) : (0 < n)%N ->
  lead_coef ('X^n - c%:P) = 1.
Proof.
move=> gt0_n; rewrite lead_coefDl ?lead_coefXn //.
by rewrite size_opp size_polyC size_polyXn ltnS (leq_trans (leq_b1 _)).
Qed.

Lemma lead_coef_XsubC {R : ringType} (c : R) :
  lead_coef ('X - c%:P) = 1.
Proof. by apply: (@lead_coef_XnsubC _ 1%N). Qed.

Lemma monic_XsubC {R : ringType} (c : R) : 'X - c%:P \is monic.
Proof. by rewrite monicE lead_coef_XsubC. Qed.

Lemma monic_XnsubC {R : ringType} n (c : R) : (0 < n)%N -> 'X^n - c%:P \is monic.
Proof. by move=> gt0_n; rewrite monicE lead_coef_XnsubC. Qed.

Lemma size_XnsubC {R : ringType} n (c : R) : (0 < n)%N -> size ('X^n - c%:P) = n.+1.
Proof.
move=> gt0_n; rewrite size_addl ?size_polyXn //.
by rewrite size_opp size_polyC; case: (c =P 0).
Qed.

Lemma lead_coef_prod {R : idomainType} (ps : seq {poly R}) :
  lead_coef (\prod_(p <- ps) p) = \prod_(p <- ps) lead_coef p.
Proof. by apply/big_morph/lead_coef1; apply: lead_coefM. Qed.

Lemma lead_coef_prod_XsubC {R : idomainType} (cs : seq R) :
  lead_coef (\prod_(c <- cs) ('X - c%:P)) = 1.
Proof.
rewrite -(big_map (fun c : R => 'X - c%:P) xpredT idfun) /=.
rewrite lead_coef_prod big_seq (eq_bigr (fun=> 1)) ?big1 //=.
by move=> i /mapP[c _ ->]; apply: lead_coef_XsubC.
Qed.

Lemma coef0M {R : ringType} (p q : {poly R}) : (p * q)`_0 = p`_0 * q`_0.
Proof. by rewrite coefM big_ord1. Qed.

Lemma coef0_prod {R : ringType} {T : Type} (ps : seq T) (F : T -> {poly R}) P :
  (\prod_(p <- ps | P p) F p)`_0 = \prod_(p <- ps | P p) (F p)`_0.
Proof.
by apply: (big_morph (fun p : {poly R} => p`_0)); [apply: coef0M | rewrite coefC eqxx].
Qed.

(* rename primeNsig? *)
Lemma primePn (n : nat) : ~~ prime n -> (2 <= n)%N ->
  { d : nat | (1 < d < n)%N & (d %| n)%N }.
Proof.
move=> primeN_n le2n; case/pdivP: {+}le2n => d /primeP[lt1d prime_d] dvd_dn.
exists d => //; rewrite lt1d /= ltn_neqAle dvdn_leq 1?andbT //; last first.
  by apply: (leq_trans _ le2n).
by apply: contra primeN_n => /eqP <-; apply/primeP.
Qed.

Lemma adjoin_cat
    (K : fieldType) (aT : FalgType K) (V : {vspace aT}) (rs1 rs2 : seq aT)
  : <<V & rs1 ++ rs2>>%VS = <<<<V & rs1>> & rs2>>%VS.
Proof.
elim: rs1 => /= [|r rs1 ih] in V *.
- by rewrite adjoin_nil agenv_add_id.
- by rewrite !adjoin_cons ih.
Qed.

Lemma eq_adjoin (K : fieldType) (aT : FalgType K) (U : {vspace aT})
    (rs1 rs2 : seq aT) :
  rs1 =i rs2 -> (<<U & rs1>> = <<U & rs2>>)%VS.
Proof.
by move=> rs12; apply/eqP; rewrite eqEsubv !adjoin_seqSr// => x; rewrite rs12.
Qed.

(* turn into a reflect before adding to mathcomp? *)
Lemma Fadjoin_seq_idP
    (F0 : fieldType) (L : fieldExtType F0) (K : {subfield L}) (xs : seq L)
  : all (mem K) xs -> <<K & xs>>%VS = K.
Proof.
elim: xs => /= [|x xs ih]; first by  rewrite Fadjoin_nil.
by case/andP=> xK {}/ih ih; rewrite adjoin_cons (Fadjoin_idP _).
Qed.

Lemma memv_mulP (K : fieldType) (aT : FalgType K) (U V : {vspace aT}) w :
  reflect (exists n (us vs : n.-tuple aT),
            [/\ all (mem U) us, all (mem V) vs & w = \sum_(i < n) tnth us i * tnth vs i])
          (w \in (U * V)%VS).
Proof.
apply: (iffP idP) => [|[b [us [vs [usU vsV ->]]]]]; last first.
  by rewrite rpred_sum// => i _; rewrite memv_mul//; apply/all_tnthP.
rewrite unlock span_def big_tuple => /memv_sumP[/= w_ w_mem ->].
have wP_ i : exists2 uv, (uv.1 \in U) && (uv.2 \in V) & w_ i = uv.1 * uv.2.
  have /vlineP[k ->] := w_mem i isT; set UV := (X in tnth X _).
  have /allpairsP[[u v] [uP vP ->]] := mem_tnth i UV.
  by exists (k *: u, v); rewrite /= ?rpredZ ?vbasis_mem// scalerAl.
pose uv i := (projT1 (sig2_eqW (wP_ i))).
exists _, [tuple (uv i).1 | i < _], [tuple (uv i).2 | i < _]; rewrite /uv.
split; do ?by apply/allP => _/mapP[i _ ->]; case: sig2_eqW => /= ? /andP[].
by apply: eq_bigr => i; rewrite !tnth_map/= tnth_ord_tuple; case: sig2_eqW.
Qed.

Lemma big_rcons (R : Type) (idx : R) (op : R -> R -> R) (I : Type)
    (i : I) (r : seq I) (P : pred I) (F : I -> R)
    (idx' := if P i then op (F i) idx else idx) :
  \big[op/idx]_(j <- rcons r i | P j) F j = \big[op/idx']_(j <- r | P j) F j.
Proof. by elim: r => /= [|j r]; rewrite ?(big_nil, big_cons)// => ->. Qed.

Lemma big_change_idx (R : Type) (idx : R) (op : Monoid.law idx) (I : Type)
    (x : R)  (r : seq I) (P : pred I) (F : I -> R) :
  \big[op/x]_(j <- r | P j) F j = op (\big[op/idx]_(j <- r | P j) F j) x.
Proof.
elim: r => [|i r]; rewrite ?(big_nil, big_cons, Monoid.mul1m)// => ->.
by case: ifP => // Pi; rewrite Monoid.mulmA.
Qed.

Lemma big_prodv_seqP (I : eqType) (r : seq I)  (P : {pred I})
  (K : fieldType) (aT : FalgType K) (U : {vspace aT})
  (V : I -> {vspace aT}) (W : {vspace aT}) : uniq r ->
  reflect (forall u (v : I -> aT), u \in  U -> (forall i, P i -> v i \in V i) ->
                               \big[*%R/u]_(i <- r | P i) v i \in W)
  (\big[@prodv _ _/U]_(i <- r | P i) V i <= W)%VS.
Proof.
elim/last_ind: r => [|r i IHr] //= in U W * => [_|].
  apply: (iffP idP) => [+ v u uP vP|]; rewrite !big_nil; first by move/subvP->.
  move=> WP; apply/subvP => u /(WP _ (fun=> 0)); rewrite big_nil; apply.
  by move=> i; rewrite mem0v.
rewrite rcons_uniq => /andP[iNr r_uniq].
apply: (iffP idP) => [+ u v uU vV|WP]; rewrite !big_rcons.
  by move=> /IHr; apply => //; case: ifP => Pi//; rewrite memv_mul// vV.
case: ifP => Pi; last first.
  by apply/IHr => // u v uU vV; have := WP _  _ uU vV; rewrite big_rcons Pi.
apply/IHr => //w v /memv_mulP[n [vs [us [/allP/= vsP /allP/= usP ->]]]] vV.
rewrite big_change_idx/= mulr_sumr rpred_sum// => j _.
rewrite -big_change_idx/=.
have := WP (tnth us j) (fun k : I => if k == i then tnth vs j else v k).
rewrite big_rcons Pi eqxx big_seq_cond.
under eq_bigr => k /andP[kr]
   do [rewrite ifN; last by apply: contraNneq iNr => <-].
rewrite -big_seq_cond; apply; first by rewrite usP ?mem_tnth.
by move=> k Pk; case: eqP => [->|]; rewrite ?vV ?vsP ?mem_tnth.
Qed.

Lemma big_prod_subfield_seqP (I : eqType) (r : seq I) (r_uniq : uniq r) (P : {pred I})
  (K : fieldType) (aT : fieldExtType K) (U : I -> {vspace aT}) (W : {subfield aT}) :
  reflect (forall u : I -> aT, (forall i, P i -> u i \in U i) ->
                               \prod_(i <- r | P i) u i \in W)
  (\big[@prodv _ _/1%VS]_(i <- r | P i) U i <= W)%VS.
Proof.
apply: (iffP (big_prodv_seqP _ _ _ _ _)) => // [WP u uU|WP u v uU vV].
  by apply: WP; rewrite ?mem1v.
by rewrite big_change_idx/= memvM ?WP//; apply/subvP: uU; rewrite sub1v.
Qed.

Lemma big_prod_subfieldP (I : finType) (D : {pred I})
  (K : fieldType) (aT : fieldExtType K) (U : I -> {vspace aT}) (W : {subfield aT}) :
  reflect (forall u : I -> aT, (forall i, D i -> u i \in U i) ->
                               \prod_(i in D) u i \in W)
  (\big[@prodv _ _/1%VS]_(i in D) U i <= W)%VS.
Proof. by apply/big_prod_subfield_seqP/index_enum_uniq. Qed.

Lemma prodv_Fadjoinl (F0 : fieldType) (L : fieldExtType F0)
  (K F : {subfield L}) (x : L) : (<<K; x>> * F)%VS = <<K * F; x>>%VS.
Proof.
apply/eqP; rewrite eqEsubv; apply/andP; split.
  apply/prodvP => y z /Fadjoin_polyP[p pK ->] zF.
  have -> : p.[x] * z = (z *: p).[x] by rewrite hornerZ mulrC.
  rewrite mempx_Fadjoin// polyOverZ//=.
    by apply/subvP: zF; rewrite field_subvMl.
  by move: pK; apply/polyOverS/subvP; rewrite field_subvMr.
apply/subvP => y /Fadjoin_polyP [p /polyOverP pKF ->].
rewrite horner_coef rpred_sum// => i _.
have /memv_mulP[n [us [vs [/allP/= usP /allP/= vsP ->]]]] := pKF i.
rewrite mulr_suml rpred_sum // => j _.
rewrite mulrAC memv_mul ?rpredM ?rpredX ?memv_adjoin ?vsP ?mem_tnth//.
by rewrite subvP_adjoin// usP ?mem_tnth.
Qed.

Lemma prodv_Fadjoinr (F0 : fieldType) (L : fieldExtType F0)
  (K F : {subfield L}) (x : L) : (F * <<K; x>>)%VS = <<F * K; x>>%VS.
Proof. by rewrite prodvC prodv_Fadjoinl prodvC. Qed.

Lemma prodv_idPl  (F0 : fieldType) (L : fieldExtType F0)
  (K F : {subfield L}) :  reflect (F * K = F)%VS (K <= F)%VS.
Proof.
apply: (iffP idP) => [KF|<-]; last by rewrite field_subvMl.
by apply/eqP; rewrite eqEsubv prodv_sub//= field_subvMr.
Qed.
Arguments prodv_idPl {F0 L K F}.

Lemma prodv_idPr  (F0 : fieldType) (L : fieldExtType F0)
  (K F : {subfield L}) :  reflect (K * F = F)%VS (K <= F)%VS.
Proof. by rewrite prodvC; apply: prodv_idPl. Qed.
Arguments prodv_idPr {F0 L K F}.

Lemma tnth_lshift {T : Type} {n1 n2} (t1 : n1.-tuple T) (t2 : n2.-tuple T) (i : 'I_n1) :
  tnth [tuple of t1 ++ t2] (lshift n2 i) = tnth t1 i.
Proof.
have x0 := tnth_default t1 i; rewrite !(tnth_nth x0).
by rewrite nth_cat size_tuple /= ltn_ord.
Qed.

Lemma tnth_rshift {T : Type} {n1 n2} (t1 : n1.-tuple T) (t2 : n2.-tuple T) (i : 'I_n2) :
  tnth [tuple of t1 ++ t2] (rshift n1 i) = tnth t2 i.
Proof.
have x0 := tnth_default t2 i; rewrite !(tnth_nth x0).
by rewrite nth_cat size_tuple ltnNge leq_addr /= addKn.
Qed.

End missing_from_mathcomp.
Arguments prodv_idPl {F0 L K F}.
Arguments prodv_idPr {F0 L K F}.

Section ExternalNDirProd.

Variables (n : nat) (gT : 'I_n -> finGroupType).
Notation gTn := {dffun forall i, gT i}.

Definition extprod_mulg (x y : gTn) : gTn := [ffun i => (x i * y i)%g].
Definition extprod_invg (x : gTn) : gTn := [ffun i => (x i)^-1%g].

Lemma extprod_mul1g : left_id [ffun=> 1%g] extprod_mulg.
Proof. by move=> x; apply/ffunP => i; rewrite !ffunE mul1g. Qed.

Lemma extprod_mulVg : left_inverse [ffun=> 1%g] extprod_invg extprod_mulg.
Proof. by move=> x; apply/ffunP => i; rewrite !ffunE mulVg. Qed.

Lemma extprod_mulgA : associative extprod_mulg.
Proof. by move=> x y z; apply/ffunP => i; rewrite !ffunE mulgA. Qed.

Definition extprod_groupMixin :=
  Eval hnf in FinGroup.Mixin extprod_mulgA extprod_mul1g extprod_mulVg.
Canonical extprod_baseFinGroupType :=
  Eval hnf in BaseFinGroupType gTn extprod_groupMixin.
Canonical prod_group := FinGroupType extprod_mulVg.

End ExternalNDirProd.

Definition setXn n (fT : 'I_n -> finType) (A : forall i, {set fT i}) :
   {set {dffun forall i, fT i}} :=
   [set x : {dffun forall i, fT i} | [forall i : 'I_n, x i \in A i]].

Lemma setXn_group_set n (gT : 'I_n -> finGroupType) (G : forall i, {group gT i}) :
  group_set (setXn G).
Proof.
apply/andP => /=; split.
  by rewrite inE; apply/forallP => i; rewrite ffunE group1.
apply/subsetP => x /mulsgP[u v]; rewrite !inE => /forallP uG /forallP vG {x}->.
by apply/forallP => x; rewrite ffunE groupM ?uG ?vG.
Qed.

Canonical setXn_group n (gT : 'I_n -> finGroupType) (G : forall i, {group gT i}) :=
  Group (setXn_group_set G).

Lemma setX0 (gT : 'I_0 -> finGroupType) (G : forall i, {group gT i}) :
  setXn G = 1%g.
Proof.
apply/setP => x; rewrite !inE; apply/forallP/idP => [_|? []//].
by apply/eqP/ffunP => -[].
Qed.

Lemma sol_setXn n (gT : 'I_n -> finGroupType) (G : forall i, {group gT i}) :
  (forall i, solvable (G i)) -> solvable (setXn G).
Proof.
elim: n => [|n IHn] in gT G * => solG; first by rewrite setX0 solvable1.
pose gT' (i : 'I_n) := gT (lift ord0 i).
pose f (x : prod_group gT) : prod_group gT' := [ffun i => x (lift ord0 i)].
have fm : morphic (setXn G) f.
  apply/'forall_implyP => -[a b]; rewrite !inE/=.
  by move=> /andP[/forallP aG /forallP bG]; apply/eqP/ffunP => i; rewrite !ffunE.
rewrite (@series_sol _ [group of setXn G] ('ker (morphm fm))) ?ker_normal//=.
rewrite (isog_sol (first_isog _))/=.
have -> : (morphm fm @* setXn G)%g = setXn (fun i => G (lift ord0 i)).
  apply/setP => v; rewrite !inE morphimEdom; apply/idP/forallP => /=.
    move=> /imsetP[/=x]; rewrite inE => /forallP/= xG ->.
    by move=> i; rewrite morphmE ffunE xG.
  move=> vG; apply/imsetP.
  pose w : prod_group gT := [ffun i : 'I_n.+1 =>
             match unliftP ord0 i with
             | UnliftSome j i_eq => ecast i (gT i) (esym i_eq) (v j)
             | UnliftNone i0 => 1%g
             end].
  have wl i : w (lift ord0 i) = v i.
    rewrite ffunE; case: unliftP => //= j elij.
    have eij : i = j by case: elij; apply/val_inj.
    by rewrite [elij](eq_irrelevance _ (congr1 _ eij)); case: _ / eij.
  have w0 : w ord0 = 1%g by rewrite ffunE; case: unliftP.
  exists w; last by apply/ffunP => i; rewrite morphmE ffunE/= wl.
  rewrite inE; apply/forallP => i.
  by case: (unliftP ord0 i) => [j|]->; rewrite ?wl ?w0 ?vG.
rewrite IHn ?andbT//; last by move=> i; apply: solG.
pose k (x : gT ord0) : prod_group gT :=
   [ffun i : 'I_n.+1 => if (ord0 =P i) is ReflectT P then ecast i (gT i) P x else 1%g].
have km : morphic (G ord0) k.
  apply/'forall_implyP => -[a b]; rewrite !inE/= => /andP[aG bG].
  apply/eqP/ffunP => i; rewrite !ffunE; case: eqP => //; rewrite ?mulg1//.
  by case: _ /.
suff -> : ('ker (morphm fm) = morphm km @* G ord0)%g by rewrite morphim_sol.
apply/setP => x; rewrite morphimEdom; apply/idP/imsetP => [xker|].
  exists (x ord0).
     by have := dom_ker xker; rewrite inE => /forallP/(_ ord0).
  rewrite /= morphmE; apply/ffunP => i; rewrite ffunE; case: eqP => //=.
    by case: _ /.
  move/eqP; rewrite eq_sym; have /mker/= := xker; rewrite morphmE => /ffunP.
  by case: (@unliftP _ ord0 i) => [j|] ->//= /(_ j); rewrite !ffunE.
move=> [x0 xG0 -> /=]; rewrite morphmE; apply/kerP; rewrite ?inE.
  by apply/forallP => i; rewrite ffunE; case: eqP => //=; case: _ /.
by rewrite /= morphmE; apply/ffunP => i; rewrite !ffunE; case: eqP.
Qed.

Section Prodv.

Variables (F0 : fieldType) (L : splittingFieldType F0).

Lemma galois_subW (E F : {subfield L}) : galois E F -> (E <= F)%VS.
Proof. by case/andP. Qed.

Lemma galois_normalW (E F : {subfield L}) : galois E F -> (normalField E F)%VS.
Proof. by case/and3P. Qed.

Lemma galois_separableW (E F : {subfield L}) : galois E F -> (separable E F)%VS.
Proof. by case/and3P. Qed.

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
move=> kK kF /(splitting_normalField kK) [p [pk [rs p_eq krs]]].
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

Import AEnd_FinGroup.
Lemma normalField_refl (K : {subfield L}) : normalField K K.
Proof.
apply/forallP => /= u; apply/implyP; rewrite in_set.
by move=> /andP[/andP[_ /fixedSpace_limg->]].
Qed.
Hint Resolve normalField_refl.

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

Section RadicalExtension.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Hypothesis (charL : [char L] =i pred0). (* overspecialize for easy separability *)

Section Defs.

Implicit Types (U V : {vspace L}).

Definition radical U x n := [&& (n > 0)%N & x ^+ n \in U].

Lemma radicalP U x n :
  reflect
    [/\ (n > 0)%N & x ^+ n \in U]
    [&& (n > 0)%N & x ^+ n \in U].
Proof. exact: andP. Qed.

Definition pradical U x p := [&& prime p & x ^+ p \in U].

Lemma pradicalP U x p :
  reflect
    [/\ prime p & x ^+ p \in U]
    [&& prime p & x ^+ p \in U].
Proof. exact: andP. Qed.

Implicit Types r : {vspace L} -> L -> nat -> bool.

Definition tower r n U (e : n.-tuple L) (pw : n.-tuple nat) :=
  [forall i : 'I_n, r << U & take i e >>%VS (tnth e i) (tnth pw i)].

Lemma towerP r n U (e : n.-tuple L) (pw : n.-tuple nat) :
  reflect
    (forall i : 'I_n, r << U & take i e >>%VS (tnth e i) (tnth pw i))
    (tower r U e pw).
Proof. exact: forallP. Qed.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.

Inductive extension_pred r U V : Type :=
| Extension n (e : n.-tuple L) (pw : n.-tuple nat) of
    << U & e >>%VS = V & r.-tower n U e pw.

Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Definition ep_size r U V (h : r.-ext U V) : nat :=
  let: Extension n _ _ _ _ := h in n.

Definition ep_e r U V (h : r.-ext U V) : (ep_size h).-tuple L :=
  let: Extension _ e _ _ _ := h in e.

Definition ep_pw r U V (h : r.-ext U V) : (ep_size h).-tuple nat :=
  let: Extension _ _ pw _ _ := h in pw.

Definition solvable_by r (U V : {subfield L}) : Type :=
  { E : {subfield L} & ((r.-ext U E) * (V <= E)%VS)%type }.

Definition solvable_by_radicals_poly (E F : {subfield L}) (p : {poly L}) :=
  splittingFieldFor E p F -> solvable_by radical E F.

Import AEnd_FinGroup.

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
have EsubM := galois_subW (minGalois_galois E F).
have EnormM := galois_normalW (minGalois_galois E F).
by rewrite -(isog_sol (normalField_isog galEK _ _)) ?EsubM// quotient_sol.
Qed.

End Defs.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.
Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Local Open Scope fset_scope.

Section Properties.

Implicit Types r : {vspace L} -> L -> nat -> bool.
Implicit Types (U V : {subfield L}) (A : {fset L}).

Lemma rext_refl r (E : {subfield L}) : r.-ext E E.
Proof.
exists _ [tuple] [tuple] => /=.
- by rewrite Fadjoin_nil.
- by apply/forallP; case.
Qed.

Lemma rext_r r n (U : {subfield L}) x : r U x n -> r.-ext U << U; x >>%VS.
Proof.
move=> rUxn; exists _ [tuple x] [tuple n] => /=; first by rewrite adjoin_seq1.
by apply/forallP=> /= i; rewrite ord1 /= !tnth0 Fadjoin_nil.
Qed.

Lemma rext_trans r (F E K : {subfield L}) :
  r.-ext E F -> r.-ext F K -> r.-ext E K.
Proof.
move=> [n1 e1 pw1] FE Ee [n2 e2 pw2] KE Fe.
exists _ [tuple of e1 ++ e2] [tuple of pw1 ++ pw2] => /=.
  by rewrite adjoin_cat FE.
apply/forallP=> /= i; case: (unsplitP i) => [j eq_ij|k eq_i_n1Dk].
- rewrite eq_ij !tnth_lshift takel_cat /=; last first.
    by rewrite size_tuple ltnW.
  by move/forallP/(_ j): Ee.
- rewrite eq_i_n1Dk take_cat size_tuple ltnNge leq_addr /= addKn.
  by rewrite adjoin_cat FE !tnth_rshift; move/forallP/(_ k): Fe.
Qed.

Lemma rext_r_trans r n (E F K : {subfield L}) x :
  r.-ext E F -> r F x n -> r.-ext E << F; x>>%VS.
Proof. by move=> rEF /rext_r; apply: rext_trans. Qed.

Lemma rext_subspace r E F : r.-ext E F -> (E <= F)%VS.
Proof. by case=> [n e pw] <- _; apply: subv_adjoin_seq. Qed.

Lemma solvable_by_radicals_radicalext (E F : {subfield L}) :
  radical.-ext E F -> solvable_by radical E F.
Proof. by move=> extEF; exists F. Qed.

Lemma radical_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  (0 < n)%N -> x ^+ n \in E -> radical E x n.
Proof. by move=> ??; apply/radicalP. Qed.

Lemma pradical_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  prime n -> x ^+ n \in E -> pradical E x n.
Proof. by move=> ??; apply/pradicalP. Qed.

Lemma radical_ext_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  (0 < n)%N -> x ^+ n \in E -> radical.-ext E <<E; x>>%VS.
Proof. by move=> n_gt0 xnE; apply/rext_r/(radical_Fadjoin n_gt0 xnE). Qed.

Lemma pradical_ext_Fadjoin (p : nat) (x : L) (E : {subfield L}) :
  prime p -> x ^+ p \in E -> pradical.-ext E <<E; x>>%AS.
Proof. by move=> p_prime Exn; apply/rext_r/(pradical_Fadjoin p_prime Exn). Qed.

Lemma pradicalext_radical n (x : L) (E : {subfield L}) :
  radical E x n -> pradical.-ext E << E; x >>%VS.
Proof.
move=> /radicalP[n_gt0 xnE]; have [k] := ubnP n.
elim: k => // k IHk in n x E n_gt0 xnE *; rewrite ltnS => lenk.
have [prime_n|primeN_n] := boolP (prime n).
- by apply: (@pradical_ext_Fadjoin n).
case/boolP: (2 <= n)%N; last first.
- case: n {lenk primeN_n} => [|[]]// in xnE n_gt0 * => _.
  suff ->:  <<E; x>>%VS = E by apply: rext_refl.
  by rewrite (Fadjoin_idP _).
move/primePn=> -/(_ primeN_n)[d /andP[d_gt1 d_ltn] dvd_dn].
have [m n_eq_md]: {k : nat | n = (k * d)%N}.
+ by exists (n %/ d)%N; rewrite [LHS](divn_eq _ d) (eqP dvd_dn) addn0.
have m_gt0 : (m > 0)%N.
  by move: n_gt0; rewrite !lt0n n_eq_md; apply: contra_neq => ->.
apply: (@rext_trans _ <<E; x ^+ d>>) => //.
  apply: (@IHk m (x ^+ d)) => //.
  - by rewrite -exprM mulnC -n_eq_md//.
  - by rewrite (leq_trans _ lenk)// n_eq_md ltn_Pmulr.
suff -> : <<E; x>>%AS = <<<<E; x ^+ d>>; x>>%AS.
  apply: (IHk d) => //.
  - by rewrite (leq_trans _ d_gt1)//.
  - by rewrite memv_adjoin.
  - by rewrite (leq_trans _ lenk).
apply/val_inj; rewrite /= adjoinC [<<_; x ^+ d>>%VS](Fadjoin_idP _)//.
by rewrite rpredX// memv_adjoin.
Qed.

Lemma tower_sub r1 r2 n E (e : n.-tuple L) (pw : n.-tuple nat) :
  (forall U x n, r1 U x n -> r2 U x n) ->
    r1.-tower _ E e pw -> r2.-tower _ E e pw.
Proof. by move=> sub_r /forallP /= h; apply/forallP=> /= i; apply/sub_r/h. Qed.

Lemma radical_pradical U x p : pradical U x p -> radical U x p.
Proof.
case/pradicalP=> prime_p xpU; apply/radicalP; split=> //.
by case/primeP: prime_p => /ltnW.
Qed.

Lemma radicalext_pradicalext (E F : {subfield L}) :
  pradical.-ext E F -> radical.-ext E F.
Proof.
case=> [n e pw] FE Ee; exists _ e pw => //.
by apply: (tower_sub radical_pradical).
Qed.

Lemma pradicalext_radicalext (E F : {subfield L}) :
  radical.-ext E F -> pradical.-ext E F.
Proof.
case=> [n e pw]; elim: n e pw E => [|n ih] e pw E FE Ee.
  by rewrite -FE tuple0 /= Fadjoin_nil; apply: rext_refl.
apply: (@rext_trans _ << E; tnth e 0 >>).
  apply: (@pradicalext_radical (tnth pw 0)).
  by move/forallP/(_ ord0): Ee; rewrite take0 Fadjoin_nil.
apply: (ih [tuple of behead e] [tuple of behead pw]) => /=.
  by rewrite -adjoin_cons -drop1 (tnth_nth 0) -drop_nth 1?(drop0, size_tuple).
apply/forallP=> /= i; move/forallP/(_ (rshift 1 i)): Ee => /=.
rewrite !(tnth_nth 0, tnth_nth 0%N) !nth_behead [_ (rshift 1 i)]/=.
by rewrite -adjoin_cons take_addn drop1 (take_nth 0) 1?size_tuple // take0.
Qed.

Lemma solvable_by_radical_pradical (E F : {subfield L}) :
  solvable_by pradical E F -> solvable_by radical E F.
Proof. by case=> [R [/radicalext_pradicalext ERe FR]]; exists R. Qed.

Lemma solvable_by_pradical_radical (E F : {subfield L}) :
  solvable_by radical E F -> solvable_by pradical E F.
Proof. by case=> [R [/pradicalext_radicalext ERe FR]]; exists R. Qed.
End Properties.

Lemma solvable_prodv (k E F : {subfield L}) :
  (k <= F)%VS -> solvable_ext k E -> solvable_ext F (E * F)%AS.
Proof.
move=> kF solkE; apply/solvable_extP => //.
exists ([aspace of minGalois k E] * F)%AS.
rewrite (@galois_prodvr _ _ k) ?minGalois_galois ?prodvSl ?sub_minGalois//=.
rewrite (isog_sol (galois_isog (minGalois_galois _ _) _))//.
by rewrite (solvableS _ solkE)// galS// subv_cap kF galois_subW ?minGalois_galois.
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
rewrite minGalois_galois (subv_trans _ (sub_minGalois _ _))/=; last first.
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
have lkers0 : lker s == 0%VS by rewrite AEnd_lker0.
have Jgs g : ((s \o (g \o s^-1)) \o s)%VF = (s \o g)%VF.
  by rewrite comp_lfunA lker0_compfVK.
have JGsub (a : gal_of l) : ((s^-1 * a * s)%g @: (s @: l) <= s @: l)%VS.
  by rewrite -limg_comp/= Jgs limg_comp limg_gal.
pose f (g : gal_of l) : gal_of (s @: l) := gal (s @: l) (s^-1 * g * s)%g.
have fm : morphic 'Gal(l / K)%g f.
  apply/'forall_implyP => -[a b]; rewrite inE/= => /andP[aG bG].
  apply/gal_eqP => x /memv_imgP[y yl ->]; rewrite /f/=.
  rewrite !(galK, galM)// ?JGsub/= ?comp_lfunE ?memv_img//; last first.
    have /subvP : (a @: l <= l)%VS by rewrite limg_gal.
    by rewrite lker0_lfunK//; apply; rewrite memv_img.
  by rewrite lker0_lfunK// galM// lker0_lfunK.
suff <- : (morphm fm @* 'Gal(l / K) = 'Gal(s @: l / s @: K))%g
  by rewrite morphim_sol.
apply/setP => u; rewrite morphimEdom gal_kHom/= ?limgS ?galois_subW//.
apply/idP/idP.
  move=> /imsetP[g gG -> /=].
  apply/kAHomP => x /memv_imgP[y yG ->].
  rewrite /f galK//= ?memv_img//; last exact: subvP yG.
    rewrite -comp_lfunE/= Jgs// comp_lfunE (fixed_gal _ _ yG)//=.
  by rewrite -limg_comp Jgs// limg_comp limg_gal.
move=> /kAHomP sKeq.
have glJ : gal l (s * u * s^-1)%g \in ('Gal(l / K))%g.
  rewrite gal_kHom//=; apply/kAHomP => x xK.
  rewrite !galK//=; last exact: subvP xK.
    by rewrite !comp_lfunE sKeq ?memv_img// lker0_lfunK.
  by rewrite !limg_comp limg_gal -limg_comp lker0_compVf// lim1g.
apply/imsetP; exists (gal l (s * u * s^-1)%g) => //.
rewrite morphmE; apply/eqP/gal_eqP => x /memv_imgP[y yl ->].
rewrite galK//= ?memv_img//; last first.
  by rewrite -limg_comp Jgs// limg_comp limg_gal.
rewrite !comp_lfunE/= galK/=; first last.
- by rewrite lker0_lfunK.
- by rewrite !limg_comp limg_gal -limg_comp lker0_compVf// lim1g.
by rewrite -!comp_lfunE lker0_compfVK// lker0_compVKf.
Qed.

End RadicalExtension.

Arguments tower {F0 L}.
Arguments extension_pred {F0 L}.
Arguments radical {F0 L}.

Section PhiCyclotomic.

Variable (F : fieldType).

Local Notation ZtoF := (intr : int -> F).
Local Notation pZtoF := (map_poly ZtoF).

Lemma Phi_cyclotomic (n : nat) (z : F) : n.-primitive_root z ->
   pZtoF 'Phi_n = cyclotomic z n.
Proof.
elim/ltn_ind: n z => n ihn z prim_z.
have n_gt0 := prim_order_gt0 prim_z.
pose P k := pZtoF 'Phi_k.
pose Q k := cyclotomic (z ^+ (n %/ k)) k.
have eP : \prod_(d <- divisors n) P d = 'X^n - 1.
  by rewrite -rmorph_prod /= prod_Cyclotomic // rmorphB /= map_polyC map_polyXn.
have eQ : \prod_(d <- divisors n) Q d = 'X^n - 1 by rewrite -prod_cyclotomic.
have fact (u : nat -> {poly F}) : \prod_(d <- divisors n) u d =
              u n * \prod_(d <- rem n (divisors n)) u d.
  by rewrite [LHS](big_rem n) ?divisors_id.
pose p := \prod_(d <- rem n (divisors n)) P d.
pose q := \prod_(d <- rem n (divisors n)) Q d.
have ePp : P n * p = 'X^n - 1 by rewrite -eP fact.
have eQq : Q n * q = 'X^n - 1 by rewrite -eQ fact.
have Xnsub1N0 : 'X^n - 1 != 0 :> {poly F}.
  by rewrite -size_poly_gt0 size_Xn_sub_1.
have pN0 : p != 0 by apply: dvdpN0 Xnsub1N0; rewrite -ePp dvdp_mulIr.
have epq : p = q.
  case: (divisors_correct n_gt0) => uniqd sortedd dP.
  apply: eq_big_seq=> i; rewrite mem_rem_uniq ?divisors_uniq // inE.
  case/andP=> NiSn di; apply: ihn; last by apply: dvdn_prim_root; rewrite -?dP.
  suff: (i <= n)%N by rewrite leq_eqVlt (negPf NiSn).
  by apply: dvdn_leq => //; rewrite -dP.
have {epq} : P n * p = Q n * p by rewrite [in RHS]epq ePp eQq.
by move/(mulIf pN0); rewrite /Q divnn n_gt0.
Qed.

End PhiCyclotomic.

Section Cyclotomic.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (E : {subfield L}) (r : L) (n : nat).
Hypothesis r_is_nth_root : n.-primitive_root r.

Lemma cyclotomic_over : cyclotomic r n \is a polyOver E.
Proof. Admitted.
Hint Resolve cyclotomic_over : core.

(** Very Hard **)
(*     - E(x) is cyclotomic                                                   *)
Lemma minPoly_cyclotomic : r \notin E -> minPoly E r = cyclotomic r n.
Proof.
move=> Er; apply/eqP; rewrite -eqp_monic ?monic_minPoly ?cyclotomic_monic//.
rewrite /eqp minPoly_dvdp ?root_cyclotomic//=; last first.
   rewrite /cyclotomic.
(* minPoly %| cyclotomic *)
(* then using a decomposition of minPoly in linear terms : its constant *)
(* coefficient is a power of x, and in E : it can only be at power p, hence *)
(* its size, and value *)
Admitted.

(** Ok, easy to finish CHECK whether r \notin E is needed **)
Lemma splitting_Fadjoin_cyclotomic :
  (* r \notin E -> *) splittingFieldFor E (cyclotomic r n) <<E; r>>.
Proof.
(* move=> Er;  *)exists [seq r ^+ val k | k <- enum 'I_n & coprime (val k) n].
  by rewrite /cyclotomic big_map big_filter big_enum_cond/= eqpxx.
have foo i :  <<<<E; r>>; r ^+ i>>%VS = <<E; r>>%VS.
  by rewrite (Fadjoin_idP _)// rpredX// memv_adjoin.
Admitted.

(** Easy **)
(*     - E(x) is Galois                                                       *)
Lemma galois_Fadjoin_cyclotomic : galois E <<E; r>>.
Proof.
have [rE|rNE] := boolP (r \in E).
  admit.
apply/splitting_galoisField; exists (cyclotomic r n).
split => //; last exact: splitting_Fadjoin_cyclotomic.
rewrite /cyclotomic -(big_image _ _ _ (fun x => 'X - x%:P))/=.
rewrite separable_prod_XsubC.
Admitted.

Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Lemma radicalext_Fadjoin_cyclotomic : radical.-ext E <<E; r>>%AS.
Proof.
apply: (@radical_ext_Fadjoin _ _ n r).
  exact: prim_order_gt0 r_is_nth_root.
by rewrite (prim_expr_order r_is_nth_root) mem1v.
Qed.

Lemma abelian_cyclotomic : abelian 'Gal(<<E; r>> / E)%g.
Proof.
case: (boolP (r \in E)) => [r_in_E |r_notin_E].
  suff -> : ('Gal(<<E; r>> / E) = 1)%g by apply: abelian1.
  apply/eqP; rewrite -subG1; apply/subsetP => x x_in.
  rewrite inE gal_adjoin_eq ?group1 // (fixed_gal _ x_in r_in_E) ?gal_id //.
  by have /Fadjoin_idP H := r_in_E; rewrite -{1}H subvv.
(* using the definition, gal_adjoin_eq and prim_rootP *)
rewrite card_classes_abelian /classes.
apply/eqP; apply: card_in_imset => f g f_in g_in; rewrite -!orbitJ.
move/orbit_eqP/orbitP => [] h h_in <- {f f_in}; apply/eqP.
rewrite gal_adjoin_eq //= /conjg /= ?groupM ?groupV //.
rewrite ?galM ?memv_gal ?memv_adjoin //.
have hg_gal f : f \in 'Gal(<<E; r>> / E)%g -> ((f r) ^+ n = 1)%R.
  move=> f_in; apply/prim_expr_order.
  have /and3P[subF _ NF] := galois_Fadjoin_cyclotomic.
  rewrite -(root_cyclotomic r_is_nth_root) -(minPoly_cyclotomic r_notin_E) //.
  by rewrite root_minPoly_gal // ?subF ?subvv ?memv_adjoin.
have := svalP (prim_rootP r_is_nth_root (hg_gal _ g_in)).
have h1_in : (h^-1)%g \in 'Gal(<<E; r>> / E)%g by rewrite ?groupV.
have := svalP (prim_rootP r_is_nth_root (hg_gal _ h1_in)).
set ih1 := sval _ => hh1; set ig := sval _ => hg.
rewrite hh1 GRing.rmorphX /= hg GRing.exprAC -hh1 GRing.rmorphX /=.
by rewrite -galM ?memv_adjoin // mulVg gal_id.
Qed.

(*     - Gal(E(x) / E) is then solvable                                       *)
Lemma solvable_Fadjoin_cyclotomic : solvable 'Gal(<<E; r>> / E).
Proof. exact/abelian_sol/abelian_cyclotomic. Qed.

End Cyclotomic.


(* Following the french wikipedia proof :
https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_d%27Abel_(alg%C3%A8bre)#D%C3%A9monstration_du_th%C3%A9or%C3%A8me_de_Galois
*)

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.
Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Section Abel.

(******************************************************************************)
(*                                                                            *)
(* Part 1 : solvable -> radical.-ext                                          *)
(*                                                                            *)
(* With the hypothesis that F has a (order of the galois group)-primitive     *)
(*  root of the unity :                                                       *)
(* Part 1a : if G = Gal(F/E) is abelian, then F has a basis (as an E-vspace)  *)
(*           with only radical elements on E                                  *)
(* Part 1b : recurrence on the solvability chain or the order of the group,   *)
(*           using part1a and radicalext_fixedField                           *)
(*                                                                            *)
(* With the hypothesis that L contains a (order of the galois group) -        *)
(*  primitive root of the unity :                                             *)
(* Part 1c : F is once again a radical extension of E                         *)
(*                                                                            *)
(******************************************************************************)

Section Part1.

Section Part1a.

Import GRing.Theory.

(* - each element of G is diagonalizable *)
(* - the elements of G are simultaneously diagonalizable *)
(* - their eigenvalues are n-th root of the unity because their minimal *)
(*   polynomial divides X^n - 1 *)
(* - let (r1, ..., rn) be their common basis *)
(* - we use the fact :  ri^n is unchanged by any m of G => ri^n is in E *)
(*   - let lambda be the eigenvalue which corresponds to m and ri *)
(*   - then m(ri^n) = (m(ri))^n (m automorphism) *)
(*   - m(ri) = lambda ri (lambda eigenvalue) *)
(*   - lambda^n ri^n = ri^n (lambda is an n-th root of the unity) *)
(*   - ri^n is unchanged by m *)
(*   - then ri^n is in E *)
(* - ri is a radical element on E *)

Lemma part1a (F0 : fieldType) (L : splittingFieldType F0)
    (E F : {subfield L}) (G := 'Gal(F / E)%g) (n := \dim_E F) (r : L) :
      galois E F -> abelian G ->
      r \in E -> (n.-primitive_root r)%R ->
  radical.-ext E F.
Proof.
move=> galois_EF abelian_G r_in_E r_is_nth_root.
have subv_EF := galois_subW galois_EF.
have n_gt0 : (n > 0)%N by rewrite /n -dim_aspaceOver ?adim_gt0.
have asimp := (mem_aspaceOver, subv_adjoin_seq).
suff [/= r_ /andP[r_basis /allP r_F] m_r {abelian_G}] :
     { r_ : n.-tuple L |
       basis_of (aspaceOver E F) (r_ : seq (fieldOver E)) && all (mem F) r_ &
         forall i m, m \in G -> exists2 l, (l \in E) && (l ^+ n == 1)
                                           & m (tnth r_ i) = l * tnth r_ i }.
  pose f i := <<E & take i r_>>%AS.
  have f0E : f 0%N = E by apply/val_inj; rewrite /f/= take0 Fadjoin_nil.
  have Er_eq_F : <<E & r_>>%AS = F :> {vspace _}.
    apply/eqP; rewrite eqEsubv/=; apply/andP; split.
      by apply/Fadjoin_seqP; split.
    apply/subvP => x; rewrite -(mem_aspaceOver subv_EF).
    move=> /(coord_basis r_basis)->; rewrite memv_suml// => i _.
    rewrite fieldOver_scaleE/= rpredM//.
      by rewrite (subvP (subv_adjoin_seq _ _))//; apply: valP.
    have lt_ir : (i < size r_)%N by rewrite size_tuple.
    by rewrite (subvP (seqv_sub_adjoin _ (mem_nth 0 lt_ir)))// memv_line.
  exists _ r_ [tuple of nseq n n] => //; apply/forallP=> /= i.
  rewrite {2}/tnth nth_nseq ltn_ord; apply/radicalP; split=> //.
  suff: (tnth r_ i) ^+ n \in fixedField G.
    by rewrite (galois_fixedField _)//; apply/(subvP (subv_adjoin_seq _ _)).
  apply/fixedFieldP; first by rewrite rpredX ?[_ \in _]r_F ?mem_nth ?size_tuple.
  move=> g /(m_r i)[l /andP[lE /eqP lX1]].
  by rewrite (tnth_nth 0) rmorphX/= => ->; rewrite exprMn lX1 mul1r.
pose LE := [fieldExtType subvs_of E of fieldOver E].
have [e e_basis] : { e : n.-1.+1.-tuple _ | basis_of (aspaceOver E F) e}.
  rewrite prednK//; have := vbasisP (aspaceOver E F); move: (vbasis _).
  by rewrite dim_aspaceOver// => e; exists e.
have e_free := basis_free e_basis.
have Gminpoly g : g \in G -> mxminpoly (galmx e g) %| 'X ^+ n - 1.
  move=> gG; rewrite mxminpoly_min// rmorphB rmorph1 rmorphX/= horner_mx_X.
  apply: (canLR (addrK _)); rewrite add0r -galmxX//.
  by rewrite [n]galois_dim// expg_cardG// galmx1.
have /sig2W [p p_unit dG] : codiagonalisable [seq galmx e g | g in G].
  apply/codiagonalisableP; split.
    apply/all_commP => _ _ /mapP[g gG ->] /mapP[g' g'G ->].
    rewrite ?mem_enum in gG g'G.
    by rewrite -![_ *m _]galmxM// (centsP abelian_G).
  move=> _/mapP[g gG ->]; rewrite mem_enum in gG *.
  pose l := [seq Subvs r_in_E ^+ i | i <- index_iota 0 n].
  apply/diagonalisableP; exists l.
    rewrite map_inj_in_uniq ?iota_uniq//.
    move=> x y; rewrite !mem_index_iota !leq0n/= => x_n y_n.
    move=> /(congr1 val)/=/eqP; rewrite !rmorphX/=.
    by rewrite (eq_prim_root_expr r_is_nth_root) !modn_small// => /eqP.
  rewrite big_map (@factor_Xn_sub_1 _ _ (Subvs r_in_E)) ?Gminpoly//.
  by rewrite /= -(fmorph_primitive_root [rmorphism of vsval]).
pose r_ := [tuple galvec e (row i p) | i < n.-1.+1].
rewrite -[n]prednK//; exists r_.
  apply/andP; split; last by apply/allP => _ /mapP[/=i _ ->]; rewrite galvec_in.
  rewrite basisEdim; apply/andP; split; last first.
    by rewrite size_tuple dim_aspaceOver// prednK.
  apply/subvP => x /=; rewrite mem_aspaceOver// => xEF.
  have [l ->] : exists l, x = galvec e (l *m p).
    by exists (galrow e x *m invmx p); rewrite mulmxKV ?galrowK.
  rewrite span_def big_map big_enum_cond/= mulmx_sum_row linear_sum/=.
  by  apply: memv_sumr => i _; rewrite linearZ/= [_ \in _]memvZ// memv_line.
move=> i g gG; have /allP /(_ (galmx e g) (map_f _ _))/sim_diagPex := dG.
case=> // [|M pg]; first by rewrite mem_enum.
exists (val (M 0 i)); [apply/andP; split|]; first by rewrite /= subvsP.
  rewrite [X in _ ^+ X]prednK// -subr_eq0.
  have := Gminpoly _ gG; rewrite (simLR _ pg)//.
  move => /dvdpP [q] /(congr1 (val \o horner^~ (M 0 i)))/=.
  rewrite hornerM hornerD hornerN hornerXn hornerC/= rmorphX algid1 => ->.
  rewrite mxminpoly_uconj ?unitmx_inv// mxminpoly_diag/= horner_prod.
  set u := undup _; under eq_bigr do rewrite hornerXsubC.
  suff /eqP-> : \prod_(i0 <- u) (M 0 i - i0) == 0 by rewrite mulr0.
  rewrite prodf_seq_eq0; apply/hasP; exists (M 0 i); rewrite ?subrr ?eqxx//.
  by rewrite mem_undup map_f ?mem_enum.
have /(simP p_unit)/(congr1 (mulmx (@delta_mx _ 1 _ 0 i))) := pg.
rewrite !mulmxA -!rowE row_diag_mx -scalemxAl -rowE => /(congr1 (galvec e)).
by rewrite galvecM// linearZ/= tnth_map tnth_ord_tuple.
Qed.

End Part1a.

Section Part1b.
Variables (F0 : fieldType) (L : splittingFieldType F0).

Lemma part1b (E : {subfield L}) (F : {subfield L}) (r : L) :
  let n := \dim_E F in
  galois E F -> solvable 'Gal(F / E)%g -> r \in E -> n.-primitive_root r ->
  radical.-ext E F.
Proof.
move=> n galEF; have [k] := ubnP n; elim: k => // k IHk in r E F n galEF *.
rewrite ltnS => le_nk; have subEF : (E <= F)%VS by case/andP: galEF.
have n_gt0 : (0 < n)%N by rewrite ltn_divRL ?field_dimS// mul0n adim_gt0.
move=> solEF Er rn; have [n_le1|n_gt1] := leqP n 1%N.
  have /eqP : n = 1%N by case: {+}n n_gt0 n_le1 => [|[]].
  rewrite -eqn_mul ?adim_gt0 ?field_dimS// mul1n eq_sym dimv_leqif_eq//.
  by rewrite val_eqE => /eqP<-; apply: rext_refl.
have /sol_prime_factor_exists[|H Hnormal] := solEF.
  by rewrite -cardG_gt1 -galois_dim.
have [<-|H_neq] := eqVneq H ('Gal(F / E))%G; first by rewrite indexgg.
have galEH := normal_fixedField_galois galEF Hnormal.
have subEH : (E <= fixedField H)%VS by case/andP: galEH.
rewrite -dim_fixed_galois ?normal_sub// galois_dim//=.
pose d := \dim_E (fixedField H); pose p := \dim_(fixedField H) F.
have p_gt0 : (p > 0)%N by rewrite divn_gt0 ?adim_gt0 ?dimvS ?fixedField_bound.
have n_eq : n = (p * d)%N by rewrite /p /d -dim_fixedField dim_fixed_galois;
                             rewrite ?Lagrange ?normal_sub -?galois_dim.
have Erm : r ^+ (n %/ d) \in E by rewrite rpredX.
move=> /prime_cyclic/cyclic_abelian/part1a/(_ Erm)-/(_ galEH)/=.
rewrite dvdn_prim_root// => [/(_ isT)|]; last by rewrite n_eq dvdn_mull.
move=> /rext_trans; apply.
apply: (IHk (r ^+ (n %/ p))) => /=.
- exact: fixedField_galois.
- rewrite (leq_trans _ le_nk)// -dim_fixedField /n galois_dim// proper_card//.
  by rewrite properEneq H_neq normal_sub.
- by rewrite gal_fixedField (solvableS (normal_sub Hnormal)).
- by rewrite rpredX//; apply: subvP Er.
- by rewrite dvdn_prim_root// n_eq dvdn_mulr.
Qed.

End Part1b.

Section Part1c.

(* common context *)
Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (E F : {subfield L}).
Hypothesis galois_EF : galois E F.
Local Notation G := ('Gal(F / E)%g).
Local Notation n := (\dim_E F).
Variable (r : L).
Hypothesis r_is_nth_root : (n.-primitive_root r)%R.

(* Part 1c : *)
(* If : *)
(* - G is solvable *)
Hypothesis solvable_G : solvable G.

Let subEF : (E <= F)%VS := galois_subW galois_EF.


(*** the prodv part must be proven/modified before attempting this ***)
(* We want to prove that F is solvable by radicals on E                       *)
Lemma part1c : solvable_by radical E F.
Proof.
pose G : {group gal_of F} := 'Gal(F / F :&: <<E; r>>%AS)%G.
have EEr := subv_adjoin E r.
rewrite /solvable_by; exists (F * <<E; r>>)%AS.
rewrite field_subvMr; split=> //.
apply: rext_trans (radicalext_Fadjoin_cyclotomic _ r_is_nth_root) _.
have galErFEr: galois <<E; r>>%AS (F * <<E; r>>)%AS.
  by rewrite (@galois_prodvr _ _ E).
pose r' := r ^+ (n %/ #|G|).
have r'prim : #|G|.-primitive_root r'.
  by apply: dvdn_prim_root; rewrite // galois_dim ?cardSg ?galS ?subv_cap ?subEF.
have r'Er : r' \in <<E; r>>%VS by rewrite rpredX ?memv_adjoin.
apply: part1b r'Er _ => //=.
  rewrite (isog_sol (galois_isog galois_EF _))//.
  by apply: solvableS solvable_G; apply: galS; rewrite subv_cap subEF.
by rewrite galois_dim// (card_isog (galois_isog galois_EF _)).
Qed.

End Part1c.

(** Ok **)
(* Main lemma of part 1 *)
(* there is the problem of the nth-root which must be present in the big field L
to resolve here, but here is a first suggestion *)
Lemma part1 (F0 : fieldType) (L : splittingFieldType F0)
      (E F : {subfield L}) (p : {poly L}) :
  let n := (\dim_E F) in
  (exists r : L, (n.-primitive_root r)%R) -> galois E F ->
  solvable 'Gal(F / E) -> solvable_by radical E F.
Proof. by move=> /= /sigW [r r_prim] EF /(part1c EF r_prim); apply. Qed.

End Part1.

(******************************************************************************)
(*                                                                            *)
(* Part 2 : solvable_by_radicals -> solvable                                  *)
(*  with the hypothesis that F has a (dim of E)-primitive root of the unity   *)
(*                                                                            *)
(* Part 2a : let x be a pth root of an element of E with p prime, then E(x)   *)
(*           is galois and its galois group is abelian                        *)
(* Part 2b : given a prime extension tower, if L has a nth root of the unity  *)
(*           then F/E is solvable                                             *)
(*                                                                            *)
(******************************************************************************)

Section Part2.

Variables (F0 : fieldType) (L : splittingFieldType F0).

Section IntermediateLemmas.

(* Part 2a : *)
(* If : *)
(* - E contains the p-th root of the unity, where p is prime *)
(* - let x be a p-th root of an element of E *)
Variables (E : {subfield L}) (p : nat) (x : L) (r : L).
Hypothesis char_L : [char L] =i pred0.
Hypothesis prime_p : prime p.
Hypothesis r_is_pth_root : (p.-primitive_root r)%R.
Hypothesis x_notin_E : x \notin E.
Hypothesis xp_in_E : (x ^+ p)%R \in E.
Local Notation G := ('Gal(<<E; x>> / E))%g.

Section Part2a.
Hypothesis r_in_E : r \in E.

Lemma uniq_roots_Xp_sub_xp : uniq [seq x * r ^+ (val i) | i : 'I_p].
Proof.
apply/(uniqP 0) => i j; rewrite !inE size_map size_enum_ord => ltip ltjp.
rewrite (nth_map (Ordinal ltip)) ?size_enum_ord //= nth_enum_ord //.
rewrite (nth_map (Ordinal ltjp)) ?size_enum_ord //= nth_enum_ord //.
have: x != 0 by apply/contra: x_notin_E => /eqP->; rewrite rpred0.
move/mulfI=> h{}/h /eqP; rewrite (eq_prim_root_expr r_is_pth_root).
by rewrite !modn_small -1?size_rs // => /eqP.
Qed.

Lemma Xp_sub_xpE : ('X^p - (x ^+ p)%:P)%R = \prod_(i < p) ('X - (x * r ^+ i)%:P).
Proof.
have := uniq_roots_Xp_sub_xp; rewrite -uniq_rootsE.
move/all_roots_prod_XsubC => eq; rewrite {}[LHS]eq; first last.
- apply/allP=> z /mapP[/= i _ ->]; rewrite rootE !(hornerE, hornerXn) exprMn exprAC.
  by rewrite [r ^+ p]prim_expr_order // expr1n mulr1 subrr.
- by rewrite size_XnsubC ?prime_gt0 // size_map size_enum_ord.
rewrite (monicP _) 1?scale1r; last by apply/monic_XnsubC/prime_gt0.
by rewrite big_map /index_enum -enumT.
Qed.

Lemma Fadjoin_primeE : minPoly E x = ('X^p - (x ^+ p)%:P)%R.
Proof.
have dvd_mpEx: minPoly E x %| ('X^p - (x ^+ p)%:P); first apply: minPoly_dvdp.
- by rewrite rpredB 1?polyOverC //; apply/rpredX/polyOverX.
- by apply/rootP; rewrite !(hornerE, hornerXn) subrr.
rewrite (rwP eqP) -eqp_monic ?(monic_minPoly, monic_XnsubC) ?prime_gt0 //.
move: {+}dvd_mpEx; rewrite Xp_sub_xpE; pose F x (i : 'I_p) := x * r ^+ i.
rewrite -(big_map (F x) predT (fun z => 'X - z%:P)) /=.
rewrite /index_enum -enumT /=; set rs := map _ _.
case/dvdp_prod_XsubC => [m mpEx].
suff mrsE: mask m rs = rs by rewrite mrsE in mpEx.
have: (minPoly E x)`_0 \in E by apply/polyOverP/minPolyOver.
move: {+}mpEx; rewrite eqp_monic ?(monic_minPoly, monic_prod_XsubC) //.
move/eqP=> ->; rewrite coef0_prod {1}mask_filter //; last first.
  exact: uniq_roots_Xp_sub_xp.
rewrite big_filter big_map (eq_bigr (F (-x))); last first.
- by move=> i _; rewrite coefB coefX coefC eqxx /F mulNr sub0r.
rewrite big_mkcond big_enum -big_mkcond prodrMl /= fpredMr; last first.
- apply/prodf_neq0=> /= i _; have /eqP := prim_expr_order r_is_pth_root.
  rewrite -{1}[p](@subnK i p) 1?ltnW // exprD; apply: contraL.
  by move/eqP=> ->; rewrite mulr0 eq_sym oner_eq0.
- by apply/rpred_prod=> i _; apply/rpredX.
rewrite exprNn fpredMl; last first.
- by rewrite signr_eq0.
- by rewrite rpredX // rpredN rpred1.
set S := (S in x ^+ #|S|); case/boolP: (#|S| == 0%N) => [/eqP/card0_eq z_S|nz_S].
- move: {+}mpEx; rewrite mask_filter //; last first.
    exact: uniq_roots_Xp_sub_xp.
  rewrite big_filter big_map big_pred0.
    by move/eqp_root/(_ x); rewrite root_minPoly rootC oner_eq0.
  by move=> /= i; move: (z_S i).
have: (#|S| <= p)%N by rewrite -[X in (_ <= X)%N]card_ord max_card.
rewrite leq_eqVlt => /orP[Sfull _|lt_S_p].
- rewrite mask_filter ?uniq_roots_Xp_sub_xp // (@eq_in_filter _ _ predT).
    by rewrite filter_predT.
  move=> _ /mapP[/= i _ ->]; apply: contraLR Sfull => xri_maskN.
  rewrite -[X in _ != X]card_ord eqn_leq max_card /= -ltnNge.
  by apply/proper_card/properP; split; [apply/subset_predT | exists i].
move: #|S| nz_S lt_S_p => k nz_k lt_kp; apply/contraTeq => _ /=.
have: coprime p k by rewrite prime_coprime // gtnNdvd // lt0n.
case/(coprimeP _ (prime_gt0 prime_p)) => -[u v] /= bz.
move: x_notin_E; rewrite -{1}[x]expr1 -bz expfB; last first.
  by rewrite -subn_gt0 bz.
apply: contra => xkE; apply: rpredM.
+ by rewrite mulnC exprM rpredX.
+ by rewrite rpredV mulnC exprM rpredX.
Qed.

Lemma size_Fadjoin_prime : size (minPoly E x) = p.+1.
Proof.
rewrite Fadjoin_primeE Xp_sub_xpE size_prod_XsubC.
by rewrite /index_enum /= -enumT size_enum_ord.
Qed.

(* - E(x) is Galois                                                           *)
Lemma galois_Fadjoin_prime : galois E <<E; x>>.
Proof.
apply/splitting_galoisField => /=; exists ('X^p - (x ^+ p)%:P); split.
- by rewrite rpredB // 1?polyOverC //; apply/rpredX/polyOverX.
- rewrite Xp_sub_xpE /index_enum -enumT /=.
  rewrite -(big_map _ predT (fun z => 'X - z%:P)) /=.
  by rewrite separable_prod_XsubC uniq_roots_Xp_sub_xp.
pose rs := [seq x * r ^+ i | i : 'I_p]; exists rs.
- rewrite Xp_sub_xpE /index_enum -enumT /=.
  by rewrite -(big_map _ predT (fun z => 'X - z%:P)) /eqp dvdpp. (* eqpp *)
rewrite /rs /image_mem (map_comp (fun i => x * r ^+ i) _) val_enum_ord.
rewrite -[X in iota 0 X]prednK ?prime_gt0 // -add1n iota_add.
rewrite map_cat /= expr0 mulr1 adjoin_cons.
rewrite Fadjoin_seq_idP //; apply/allP => z /mapP[/= i].
rewrite mem_iota /= add0n add1n prednK 1?[(0 < p)%N]prime_gt0 //.
case/andP=> _ ltip ->; apply: rpredM.
- exact: memv_adjoin.
- by apply/subvP_adjoin/rpredX.
Qed.

(* - Gal(E(x) / E) has order p                                                *)
Lemma order_galois_Fadjoin_prime : #|G| = p.
Proof.
rewrite -galois_dim 1?galois_Fadjoin_prime // -adjoin_degreeE.
by have [] := size_minPoly E x; rewrite size_Fadjoin_prime => -[].
Qed.

(* - Gal(E(x) / E) is cyclic                                                  *)
(* - Gal(E(x) / E) is abelian                                                 *)
(* (end of part2a)                                                            *)
Lemma abelian_Fadjoin_prime : abelian G.
Proof.
by apply/cyclic_abelian/prime_cyclic; rewrite order_galois_Fadjoin_prime.
Qed.

Lemma solvable_ext_Fadjoin_prime : solvable_ext E <<E; x>>.
Proof.
apply/(solvable_extP char_L); exists <<E; x>>%AS.
by rewrite galois_Fadjoin_prime abelian_sol ?abelian_Fadjoin_prime/= ?subvv.
Qed.

End Part2a.

End IntermediateLemmas.

Lemma part2 (E F : {subfield L}) : [char L] =i pred0 ->
  (E <= F)%VS -> solvable_by radical E F ->
  {n : nat | forall r : L, n.-primitive_root r -> solvable_ext E F}.
Proof.
move=> charL EF [K [/pradicalext_radicalext [n e pw {K}<- /towerP epwP FK]]].
pose K := <<E & e>>%VS; pose d := (\prod_(i < n) tnth pw i)%N.
exists d => r r_root.
have EK: (E <= K)%VS by apply: subv_trans FK.
suff [/(solvable_extP charL) [M /and3P[KrsubM EM solEM]]] : solvable_ext E <<K; r>>%AS.
  apply/(solvable_extP charL); exists M; rewrite EM solEM (subv_trans _ KrsubM)//=.
  by rewrite (subv_trans _ (subv_adjoin _ _)).
pose k := n; have -> : <<K ; r>>%AS = <<E & r :: take k e>>%AS.
  rewrite take_oversize ?size_tuple//.
  apply/val_inj; rewrite /= -adjoin_rcons.
  by rewrite (@eq_adjoin _ _ _ (rcons _ _) (r :: e))// => x; rewrite mem_rcons.
elim: k => /= [|k IHsol]; rewrite ?take0 ?adjoin_seq1.
  apply/(solvable_extP charL); exists <<E & [:: r] >>%AS.
  rewrite /= adjoin_seq1 subvv/= (galois_Fadjoin_cyclotomic _ r_root).
  by rewrite (solvable_Fadjoin_cyclotomic _ r_root).
have [ltnk|lenk] := ltnP k n; last first.
  by rewrite !take_oversize ?size_tuple// leqW in IHsol *.
rewrite (take_nth r) ?size_tuple// -rcons_cons adjoin_rcons.
pose ko := Ordinal ltnk; have /pradicalP[pwk_prime ekP] := epwP ko.
have [ekE|ekNE] := boolP (nth r e k \in <<E & r :: take k e>>%VS).
  by rewrite (Fadjoin_idP _).
have prim : (tnth pw ko).-primitive_root (r ^+ (d %/ tnth pw ko)).
  by rewrite dvdn_prim_root// /d (bigD1 ko)//= dvdn_mulr.
apply: (solvable_ext_trans charL) IHsol _; first by rewrite subv_adjoin_seq subv_adjoin.
rewrite (solvable_ext_Fadjoin_prime charL pwk_prime prim)//.
  rewrite -[k]/(val ko) -tnth_nth; apply: subvP ekP.
  by apply: adjoin_seqSr => x xe; rewrite in_cons xe orbT.
by rewrite /= adjoin_cons rpredX// (subvP (subv_adjoin_seq _ _))// memv_adjoin.
Qed.

End Part2.


(******************************************************************************)
(*                                                                            *)
(* Abel/Galois Theorem                                                        *)
(*                                                                            *)
(******************************************************************************)

(** Ok **)
Lemma AbelGalois  (F0 : fieldType) (L : splittingFieldType F0)
  (E F : {subfield L}) (p : {poly L}) :
  splittingFieldFor E p F ->
  { r : L & (#|'Gal(F / E)|%g).-primitive_root r ->
        (radical.-ext E F <=> solvable 'Gal (F / E))
  }.
Proof.
Admitted.

End Abel.






Section Examples.


Import GRing.Theory Num.Theory.

Open Scope ring_scope.

Section PrimeDegreeTwoComplexRoots.

Variables (L : splittingFieldType rat) (iota : {rmorphism L -> algC}).
Let charL := char_ext L.

Variables (p : {poly rat}) (rp' : seq L).
Hypothesis p_irr : irreducible_poly p.
Hypothesis rp'_uniq : uniq rp'.
Hypothesis ratr_p' : map_poly ratr p = \prod_(x <- rp') ('X - x%:P).
Let d := (size p).-1.
Hypothesis d_prime : prime d.
Hypothesis count_rp' : count [pred x | iota x \isn't Num.real] rp' = 2.

Let rp := [seq x <- rp' | iota x \isn't Num.real]
          ++ [seq x <- rp' | iota x \is Num.real].

Let rp_perm : perm_eq rp rp'. Proof. by rewrite perm_catC perm_filterC. Qed.
Let rp_uniq : uniq rp. Proof. by rewrite (perm_uniq rp_perm). Qed.
Let ratr_p : map_poly ratr p = \prod_(x <- rp) ('X - x%:P).
Proof. by symmetry; rewrite ratr_p'; apply: perm_big. Qed.

Lemma nth_rp_real i : (iota rp`_i \is Num.real) = (i > 1)%N.
Proof.
rewrite nth_cat size_filter count_rp'; case: ltnP => // iP; [apply/negbTE|].
  apply: (allP (filter_all [predC (mem Creal) \o iota] _)) _ (mem_nth 0 _).
  by rewrite size_filter count_rp'.
have [i_big|i_small] := leqP (size [seq x <- rp' | iota x \is Creal]) (i - 2).
  by rewrite nth_default// rmorph0 rpred0.
exact: (allP (filter_all (mem Creal \o iota) _)) _ (mem_nth 0 _).
Qed.

Let K := <<1 & rp'>>%AS.
Let K_eq : K = <<1 & rp>>%AS :> {vspace _}.
Proof. exact/esym/eq_adjoin/perm_mem. Qed.

Let K_split_p : splittingFieldFor 1%AS (map_poly ratr p) K.
Proof. by exists rp => //; rewrite ratr_p eqpxx. Qed.

Let p_monic : p \is monic.
Proof.
by rewrite -(map_monic [rmorphism of char0_ratr charL]) ratr_p monic_prod_XsubC.
Qed.

Let p_sep : separable_poly p.
Proof.
rewrite -(separable_map [rmorphism of char0_ratr charL]) ratr_p.
by rewrite separable_prod_XsubC.
Qed.

Let p_neq0 : p != 0. Proof. exact: irredp_neq0. Qed.

Let d_gt0 : (d > 0)%N.
Proof. by rewrite prime_gt0. Qed.

Let d_gt1 : (d > 1)%N.
Proof. by rewrite prime_gt1. Qed.

Lemma size_rp : size rp = d.
Proof.
have /(congr1 (size \o val))/= := ratr_p; rewrite -char0_ratrE size_map_poly.
by rewrite size_prod_XsubC polySpred// => -[].
Qed.

Let i0 := Ordinal d_gt0.
Let i1 := Ordinal d_gt1.

Lemma ratr_p_over : map_poly (ratr : rat -> L) p \is a polyOver 1%AS.
Proof.
apply/polyOverP => i; rewrite -char0_ratrE coef_map /=.
by rewrite char0_ratrE -alg_num_field rpredZ ?mem1v.
Qed.

Lemma galois1K : galois 1%VS K.
Proof.
apply/splitting_galoisField; exists (map_poly ratr p); split => //.
  exact: ratr_p_over.
by rewrite -char0_ratrE separable_map.
Qed.

Lemma all_rpK : all (mem K) rp.
Proof. by rewrite K_eq; apply/allP/seqv_sub_adjoin. Qed.

Lemma root_p : root (map_poly ratr p) =i rp.
Proof. by move=> x; rewrite ratr_p [x \in root _]root_prod_XsubC. Qed.

Lemma rp_roots : all (root (map_poly ratr p)) rp.
Proof. by apply/allP => x; rewrite -root_p. Qed.

Lemma ratr_p_rp i : (i < d)%N -> (map_poly ratr p).[rp`_i] = 0.
Proof. by move=> ltid; apply/eqP; rewrite [_ == _]root_p mem_nth ?size_rp. Qed.

Lemma rpK i : (i < d)%N -> rp`_i \in K.
Proof. by move=> ltid; rewrite [_ \in _](allP all_rpK) ?mem_nth ?size_rp. Qed.

Lemma eq_size_rp : size rp == d. Proof. exact/eqP/size_rp. Qed.
Let trp := Tuple eq_size_rp.

Definition mup (x : L) (p : {poly L}) :=
  [arg max_(n > 0 : 'I_(size p).+1 | ('X - x%:P) ^+ n %| p) n] : nat.

Lemma mup_geq x q n : q != 0 -> (n <= mup x q)%N = (('X - x%:P) ^+ n %| q).
Proof.
move=> q_neq0; rewrite /mup; symmetry.
case: arg_maxP; rewrite ?expr0 ?dvd1p//= => i i_dvd gti.
case: ltnP => [|/dvdp_exp2l/dvdp_trans]; last exact.
apply: contraTF => dvdq; rewrite -leqNgt.
suff n_small : (n < (size q).+1)%N by exact: (gti (Ordinal n_small)).
by rewrite ltnS ltnW// -(size_exp_XsubC _ x) dvdp_leq.
Qed.

Lemma mup_leq x q n : q != 0 -> (mup x q <= n)%N = ~~ (('X - x%:P) ^+ n.+1 %| q).
Proof. by move=> qN0; rewrite leqNgt mup_geq. Qed.

Lemma mup_ltn x q n : q != 0 -> (mup x q < n)%N = ~~ (('X - x%:P) ^+ n %| q).
Proof. by move=> qN0; rewrite ltnNge mup_geq. Qed.

Lemma XsubC_dvd x q : q != 0 -> ('X - x%:P %| q) = (0 < mup x q)%N.
Proof. by move=> /mup_geq-/(_ _ 1%N)/esym; apply. Qed.

Lemma mup_XsubCX n (x y : L) :
  mup x (('X - y%:P) ^+ n) = (if (y == x) then n else 0)%N.
Proof.
have Xxn0 : ('X - y%:P) ^+ n != 0 by rewrite ?expf_neq0 ?polyXsubC_eq0.
apply/eqP; rewrite eqn_leq mup_leq ?mup_geq//.
have [->|Nxy] := eqVneq x y.
  by rewrite /= dvdpp ?dvdp_Pexp2l ?size_XsubC ?ltnn.
by rewrite dvd1p dvdp_XsubCl /root horner_exp !hornerE expf_neq0// subr_eq0.
Qed.

Lemma mupNroot (x : L) q : ~~ root q x -> mup x q = 0%N.
Proof.
move=> qNx; have qN0 : q != 0 by apply: contraNneq qNx => ->; rewrite root0.
by move: qNx; rewrite -dvdp_XsubCl XsubC_dvd// lt0n negbK => /eqP.
Qed.

Lemma mupMl x q1 q2 : ~~ root q1 x -> mup x (q1 * q2) = mup x q2.
Proof.
move=> q1Nx; have q1N0 : q1 != 0 by apply: contraNneq q1Nx => ->; rewrite root0.
have [->|q2N0] := eqVneq q2 0; first by rewrite mulr0.
apply/esym/eqP; rewrite eqn_leq mup_geq ?mulf_neq0// dvdp_mull -?mup_geq//=.
rewrite mup_leq ?mulf_neq0// Gauss_dvdpr -?mup_ltn//.
by rewrite coprimep_expl// coprimep_sym coprimep_XsubC.
Qed.

Lemma mupM x q1 q2 : q1 != 0 -> q2 != 0 ->
   mup x (q1 * q2) = (mup x q1 + mup x q2)%N.
Proof.
move=> q1N0 q2N0; apply/eqP; rewrite eqn_leq mup_leq ?mulf_neq0//.
rewrite mup_geq ?mulf_neq0// exprD ?dvdp_mul; do ?by rewrite -mup_geq.
have [m1 [r1]] := multiplicity_XsubC q1 x; rewrite q1N0 /= => r1Nx ->.
have [m2 [r2]] := multiplicity_XsubC q2 x; rewrite q2N0 /= => r2Nx ->.
rewrite !mupMl// ?mup_XsubCX eqxx/= mulrACA exprS exprD.
rewrite dvdp_mul2r ?mulf_neq0 ?expf_neq0 ?polyXsubC_eq0//.
by rewrite dvdp_XsubCl rootM negb_or r1Nx r2Nx.
Qed.

Lemma mu_prod_XsubC (x : L) (s : seq L) :
   mup x (\prod_(x <- s) ('X - x%:P)) = count_mem x s.
Proof.
elim: s => [|y s IHs]; rewrite (big_cons, big_nil)/=.
  by rewrite mupNroot// root1.
rewrite mupM ?polyXsubC_eq0// ?monic_neq0 ?monic_prod_XsubC//.
by rewrite IHs (@mup_XsubCX 1).
Qed.

Lemma eq_prod_XsubC (s t : seq L) :
  \prod_(x <- s) ('X - x%:P) = \prod_(x <- t) ('X - x%:P) -> perm_eq s t.
Proof.
move=> eq_prod; apply/allP => x _ /=; apply/eqP.
by have /(congr1 (mup x)) := eq_prod; rewrite !mu_prod_XsubC.
Qed.

Lemma gal1 (g : gal_of K) : g \in 'Gal(K / 1%VS)%g.
Proof. by rewrite gal_kHom ?sub1v// k1HomE ahomWin. Qed.

Lemma gal_perm_eq (g : gal_of K) : perm_eq [seq g x | x <- trp] trp.
Proof.
apply: eq_prod_XsubC; rewrite -ratr_p big_map.
transitivity (map_poly (g \o ratr) p).
  rewrite map_poly_comp/= ratr_p rmorph_prod/=.
  by apply: eq_bigr => x; rewrite rmorphB/= map_polyX map_polyC/=.
apply: eq_map_poly => x /=; rewrite (fixed_gal _ (gal1 g)) ?sub1v//.
by rewrite -alg_num_field rpredZ ?mem1v.
Qed.

Definition gal_perm g : 'S_d := projT1 (sig_eqW (tuple_permP (gal_perm_eq g))).

Lemma gal_permP g i : rp`_(gal_perm g i) = g (rp`_i).
Proof.
rewrite /gal_perm; case: sig_eqW => /= s.
move=> /(congr1 (((@nth _ 0))^~ i)); rewrite (nth_map 0) ?size_rp// => ->.
by rewrite (nth_map i) ?size_enum_ord// (tnth_nth 0)/= nth_ord_enum.
Qed.

(** N/A **)
Lemma gal_perm_is_morphism :
  {in ('Gal(K / 1%AS))%G &, {morph gal_perm : x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move=> u v _ _; apply/permP => i; apply/val_inj.
apply: (uniqP 0 rp_uniq); rewrite ?inE ?size_rp ?ltn_ord//=.
by rewrite permM !gal_permP galM// ?rpK.
Qed.
Canonical gal_perm_morphism :=  Morphism gal_perm_is_morphism.

Lemma minPoly_rp x : x \in rp -> minPoly 1%VS x = map_poly ratr p.
Proof.
move=> xrp; apply/eqP; rewrite -eqp_monic ?monic_minPoly//; last first.
  by rewrite ratr_p monic_prod_XsubC.
have : minPoly 1 x %| map_poly ratr p.
  by rewrite minPoly_dvdp ?ratr_p_over ?[root _ _]root_p//=.
have : size (minPoly 1 x) != 1%N by rewrite size_minPoly.
have /polyOver1P[q ->] := minPolyOver 1 x.
have /eq_map_poly -> : in_alg L =1 ratr.
  by move=> r; rewrite in_algE alg_num_field.
by rewrite -char0_ratrE /eqp !dvdp_map -/(_ %= _) size_map_poly; apply: p_irr.
Qed.

Lemma injm_gal_perm : ('injm gal_perm)%g.
Proof.
apply/subsetP => u /mker/= gu1; apply/set1gP/eqP/gal_eqP => x Kx.
have fixrp : all (fun r => frel u r r) rp.
  apply/allP => r/= /(nthP 0)[i]; rewrite size_rp => ltid <-.
  have /permP/(_ (Ordinal ltid))/(congr1 val)/= := gu1.
  by rewrite perm1/= => {2}<-; rewrite gal_permP.
rewrite K_eq /= in Kx.
elim/last_ind: rp x Kx fixrp => [|s r IHs] x.
  rewrite adjoin_nil subfield_closed => x1 _.
  by rewrite (fixed_gal _ (gal1 u)) ?sub1v ?gal_id.
rewrite adjoin_rcons => /Fadjoin_poly_eq <-.
rewrite all_rcons => /andP[/eqP ur /IHs us].
rewrite gal_id -horner_map/= ur map_poly_id//=.
move=> a /(nthP 0)[i i_lt <-]; rewrite us ?gal_id//.
exact/polyOverP/Fadjoin_polyOver.
Qed.

Lemma dvd_dG : (d %| #|'Gal(K / 1%VS)%g|)%N.
Proof.
rewrite dim_fixedField (galois_fixedField _) ?galois1K ?dimv1 ?divn1//.
rewrite (@dvdn_trans (\dim_(1%VS : {vspace L}) <<1; rp`_0>>%VS))//.
  rewrite -adjoin_degreeE -[X in (_ %| X)%N]/(_.+1.-1).
  rewrite -size_minPoly minPoly_rp ?mem_nth ?size_rp//.
  by rewrite -char0_ratrE size_map_poly.
rewrite dimv1 divn1 K_eq field_dimS//= -adjoin_seq1 adjoin_seqSr//.
have: (0 < size rp)%N by rewrite size_rp.
by case: rp => //= x l _ y; rewrite inE => /eqP->; rewrite inE eqxx.
Qed.

Definition gal_cycle : gal_of K := projT1 (Cauchy d_prime dvd_dG).

Lemma gal_cycle_order : #[gal_cycle]%g = d.
Proof. by rewrite /gal_cycle; case: Cauchy. Qed.

Lemma gal_perm_cycle_order : #[(gal_perm gal_cycle)]%g = d.
Proof. by rewrite order_injm ?gal_cycle_order ?injm_gal_perm ?gal1. Qed.

Definition conjL : {lrmorphism L -> L} :=
  projT1 (restrict_aut_to_normal_num_field iota conjC).

Definition iotaJ : {morph iota : x / conjL x >-> x^*} :=
  projT2 (restrict_aut_to_normal_num_field _ _).

Lemma conjLK : involutive conjL.
Proof. by move=> x; apply: (fmorph_inj iota); rewrite !iotaJ conjCK. Qed.

Lemma conjL_rp : {mono conjL : x / x \in rp}.
Proof.
suff rpJ : {homo conjL : x / x \in rp}.
  by move=> x; apply/idP/idP => /rpJ//; rewrite conjLK.
move=> ?/(nthP 0)[i]; rewrite size_rp => ltid <-.
rewrite -!root_p -!topredE /root/=.
have /eq_map_poly<- : conjL \o char0_ratr charL =1 _ := fmorph_eq_rat _.
by rewrite map_poly_comp horner_map ratr_p_rp ?rmorph0.
Qed.

Lemma conjL_K : {mono conjL : x / x \in K}.
Proof.
suff rpJ : {homo conjL : x / x \in K}.
  by move=> x; apply/idP/idP => /rpJ//; rewrite conjLK.
move=> x; rewrite K_eq => xK.
have : conjL x \in (linfun conjL @:  <<1 & rp>>)%VS.
  by apply/memv_imgP; exists x => //; rewrite lfunE.
rewrite aimg_adjoin_seq aimg1/= (@eq_adjoin _ _ _ _ rp)// => y.
apply/mapP/idP => [[z zrp->]|yrp]; first by rewrite lfunE conjL_rp.
by exists (conjL y); rewrite ?conjL_rp//= !lfunE [RHS]conjLK.
Qed.

Lemma CrealJ (C : numClosedFieldType) : {mono (@conjC C) : x / x \is Num.real}.
Proof.
suff realK : {homo (@conjC C) : x / x \is Num.real}.
  by move=> x; apply/idP/idP => /realK//; rewrite conjCK.
by move=> x xreal; rewrite conj_Creal.
Qed.

Lemma conj_rp0 : conjL rp`_i0 = rp`_i1.
Proof.
have /(nthP 0)[j jlt /esym rpj_eq]: conjL rp`_i0 \in rp.
  by rewrite conjL_rp mem_nth ?size_rp.
rewrite size_rp in jlt; rewrite rpj_eq; congr nth.
have: j != i0.
  apply: contra_eq_neq rpj_eq => ->.
  by rewrite -(inj_eq (fmorph_inj iota)) iotaJ -CrealE nth_rp_real.
have: (j < 2)%N by rewrite ltnNge -nth_rp_real -rpj_eq iotaJ CrealJ nth_rp_real.
by case: j {jlt rpj_eq} => [|[|[]]].
Qed.

Lemma conj_rp1 : conjL rp`_i1 = rp`_i0.
Proof. by apply: (canLR conjLK); rewrite conj_rp0. Qed.

Lemma conj_nth_rp (i : 'I_d) : conjL (rp`_i) = rp`_(tperm i0 i1 i).
Proof.
rewrite permE/=; case: eqVneq => [->|Ni0]; first by rewrite conj_rp0.
case: eqVneq => [->|Ni1]; first by rewrite conj_rp1.
have i_gt : (i > 1)%N by case: i Ni0 Ni1 => [[|[|[]]]].
apply: (fmorph_inj iota); rewrite iotaJ.
by rewrite conj_Creal ?nth_rp_real// tpermD// -val_eqE/= ltn_eqF// ltnW.
Qed.

Definition galJ : gal_of K := gal K (AHom (linfun_is_ahom conjL)).

Lemma galJ_tperm : gal_perm galJ = tperm i0 i1.
Proof.
apply/permP => i; apply/val_inj.
apply: (uniqP 0 rp_uniq); rewrite ?inE ?size_rp ?ltn_ord//=.
rewrite gal_permP /galJ/= galK ?rpK//= ?lfunE ?[LHS]conj_nth_rp//.
by apply/subvP => /= _/memv_imgP[x Ex ->]; rewrite lfunE conjL_K.
Qed.

Lemma surj_gal_perm : (gal_perm @* 'Gal (K / 1%AS) = 'Sym_('I_d))%g.
Proof.
apply/eqP; rewrite eqEsubset subsetT/=.
rewrite -(@gen_tperm_cycle _ i0 i1 (gal_perm gal_cycle));
  do ?by rewrite ?dpair_ij0 ?card_ord ?gal_perm_cycle_order.
 rewrite gen_subG; apply/subsetP => s /set2P[]->;
   rewrite -?galJ_tperm ?mem_morphim ?gal1//.
Qed.

Lemma isog_gal_perm : 'Gal (K / 1%AS) \isog ('Sym_('I_d)).
Proof.
apply/isogP; exists gal_perm_morphism; first exact: injm_gal_perm.
exact: surj_gal_perm.
Qed.

End PrimeDegreeTwoComplexRoots.


Section Example1.

Definition poly_example_int : {poly int} := 'X^5 - 4%:R *: 'X + 2%:R%:P.
Definition poly_example : {poly rat} := 'X^5 - 4%:R *: 'X + 2%:R%:P.

Lemma poly_exampleEint : poly_example = map_poly intr poly_example_int.
Proof.
pose simp := (rmorphB, rmorphD, rmorphN, map_polyZ,
              map_polyXn, map_polyX, map_polyC).
by do !rewrite [map_poly _ _]simp/= ?natz.
Qed.

Lemma size_poly_ex_int : size poly_example_int = 6.
Proof.
rewrite /poly_example_int -addrA size_addl ?size_polyXn//.
by rewrite size_addl ?size_opp ?size_scale ?size_polyX ?size_polyC.
Qed.

Lemma size_poly_ex : size poly_example = 6.
Proof.
rewrite poly_exampleEint size_map_poly_id0 ?size_poly_ex_int//.
by rewrite intr_eq0 lead_coef_eq0 -size_poly_eq0 size_poly_ex_int.
Qed.

Lemma poly_ex_int_neq0 : poly_example_int != 0.
Proof. by rewrite -size_poly_eq0 size_poly_ex_int. Qed.

Lemma poly_example_neq0 : poly_example != 0.
Proof. by rewrite -size_poly_eq0 size_poly_ex. Qed.

Lemma irreducible_ex : irreducible_poly poly_example.
Proof.
pose coefE := (coefB, coefD, coefZ, coefC, coefX, coefXn).
rewrite poly_exampleEint; apply: (@eisenstein 2) => // [|||i];
  rewrite ?lead_coefE ?size_poly_ex_int ?coefE//.
by move: i; do 6!case=> //.
Qed.

Lemma separable_ex : separable_poly poly_example.
Proof.
apply/coprimepP => q /(irredp_XsubCP irreducible_ex) [//| eqq].
have size_deriv_ex : size poly_example^`() = 5.
  rewrite !derivCE addr0 alg_polyC -scaler_nat /=.
  by rewrite size_addl ?size_scale ?size_opp ?size_polyXn ?size_polyC.
by rewrite gtNdvdp -?size_poly_eq0 ?size_deriv_ex ?(eqp_size eqq) ?size_poly_ex.
Qed.

Lemma prime_ex : prime (size poly_example).-1.
Proof. by rewrite size_poly_ex. Qed.

(* Using the package real_closed, we should be able to monitor the sign of    *)
(* the derivative, and find that the polynomial has exactly three real roots. *)
(*** By Cyril ?                                                             ***)
Lemma count_roots_ex :
  let rp := sval (closed_field_poly_normal ((map_poly ratr poly_example) : {poly algC})) in
  count (fun x => x \isn't Num.real) rp == 2.
Proof.
Admitted.

(** No **)
(* An example of how it could feel to use the proposed statement              *)
Lemma example_not_solvable_by_radicals
  (L : splittingFieldType rat) (iota : {rmorphism L -> algC}) (K : {subfield L}) :
  splittingFieldFor 1%VS (map_poly ratr poly_example) K ->
  solvable_by radical 1%AS K -> False.
Proof.
have charL := char_ext L; move=> p_split; have galois1K : galois 1 K.
  rewrite char0_galois ?sub1v//; apply/splitting_normalField; rewrite ?sub1v//.
  exists (map_poly ratr poly_example) => //.
  suff /eq_map_poly<- : in_alg L =1 ratr by exact: alg_polyOver.
  exact: fmorph_eq_rat.
move=> /part2-/(_ (char_ext _) (sub1v _))[n].

 (* (galois1K _ separable_ex))[n]. *)
(* have := (isog_sol (isog_gal_perm separable_ex irreducible_ex *)
(*                                  prime_ex _)). *)

(* have [] := AbelGalois K_splitP. *)
(* have := (example1 K_splitP separable_ex irreducible_ex prime_ex count_roots_ex). *)
(* by move/isog_sol => ->; apply: not_solvable_Sym; rewrite card_ord size_poly_ex. *)
Admitted.

End Example1.

Section Formula.

Variables (L : splittingFieldType rat) (iota : {rmorphism L -> algC}).
Variable (K : {subfield L}).

Inductive algformula : Type :=
| Const of rat
| Add of algformula & algformula
| Opp of algformula
| Mul of algformula & algformula
| Inv of algformula
| NRoot of nat & algformula.

Fixpoint alg_eval (f : algformula) : algC :=
  match f with
  | Const x => ratr x
  | Add f1 f2 => (alg_eval f1) + (alg_eval f2)
  | Opp f1 => - (alg_eval f1)
  | Mul f1 f2 => (alg_eval f1) * (alg_eval f2)
  | Inv f1 => (alg_eval f1)^-1
  | NRoot n f1 => nthroot n (alg_eval f1)
  end.

(** No **)
(* I changed a little bit the statement your proposed as being solvable by    *)
(* radicals can't be obtain from a formula for only one root.                 *)
(* I also feel that giving both the coefficients of the polynomial and access *)
(* to the rationals is redundant.                                             *)
Lemma example_formula (p : {poly rat}) :
  splittingFieldFor 1%AS (map_poly ratr poly_example) K ->
  solvable_by radical 1%AS K <=>
  {in root (map_poly ratr p), forall x, exists f : algformula, alg_eval f = x}.
Proof.
Admitted.

End Formula.

End Examples.
