From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field polyrcf.
From Abel Require Import various classic_ext map_gal algR.
From Abel Require Import char0 cyclotomic_ext real_closed_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section ArtinSchreier.
Variable (p : nat) (F0 : fieldType) (L : splittingFieldType F0).
Variable (E : {subfield L}) (x : L).
Hypothesis (pchar : p \in [char L]) (xpE : x ^+ p - x \in E).

Let pprim : prime p.
Proof. by move: pchar => /andP[]. Qed.

Let p0 : p%:R == 0 :> L.
Proof. by move: pchar => /andP[_]. Qed.

Let p_gt0 : (0 < p)%N.
Proof. by apply: prime_gt0. Qed.

Let p1 : (1 < p)%N.
Proof. by apply: prime_gt1. Qed.

Let rs := [tuple x + i%:R | i < p].

Let AS := 'X^p - 'X - (x ^+ p - x)%:P.

Let x_rs : x \in rs.
Proof.
apply/tnthP; exists (Ordinal p_gt0).
by rewrite tnth_map/= tnth_ord_tuple/= addr0.
Qed.

Lemma ArtinSchreier_factorize : AS = \prod_(i < p) ('X - (x + i%:R)%:P).
Proof.
have sNXXp : (size ('X : {poly L}) < size ('X^p : {poly L}))%N.
  by rewrite size_polyXn size_polyX.
have sCXp (c : L) : (size c%:P < size ('X^p : {poly L}))%N.
  by rewrite size_polyXn ltnS (leq_trans (size_polyC_leq1 _)) ?prime_gt0.
have lcLHS : lead_coef ('X^p - 'X - (x ^+ p - x)%:P) = 1.
  by rewrite !lead_coefDl ?lead_coefXn ?scale1r// ?size_addl ?size_opp.
rewrite [LHS](@all_roots_prod_XsubC _ _ rs).
- by rewrite lcLHS scale1r big_map big_enum.
- by rewrite size_tuple ?size_addl ?size_opp// size_polyXn.
- apply/allP => y /mapP[/= i _ ->]; rewrite rootE !hornerE hornerXn.
  rewrite -!Frobenius_autE rmorphD rmorph_nat.
  by rewrite opprD addrACA subrr addr0 subrr.
- by rewrite uniq_rootsE/= map_inj_uniq ?enum_uniq// => i j /addrI/ZprI; apply.
Qed.

Let ASE : AS = \prod_(i <- rs) ('X - i%:P).
Proof. by rewrite ArtinSchreier_factorize big_image/=. Qed.

Lemma ArtinSchreier_splitting : splittingFieldFor E AS <<E; x>>%AS.
Proof.
exists rs; first by rewrite ASE eqpxx.
have /eq_adjoin-> : rs =i x :: rem x rs by apply/perm_mem/perm_to_rem.
rewrite adjoin_cons (Fadjoin_seq_idP _)//=.
apply/allP => y /mem_rem /mapP[i _ ->]/=.
by rewrite rpredD ?memv_adjoin// subvP_adjoin// rpredMn// rpred1.
Qed.

Lemma ArtinSchreier_polyOver : AS \is a polyOver E.
Proof. by rewrite rpredB ?polyOverC// rpredB ?rpredX// polyOverX. Qed.

Lemma ArtinSchreier_galois : galois E <<E; x>>.
Proof.
apply/splitting_galoisField; exists ('X^p - 'X - (x ^+ p - x)%:P); split.
- exact ArtinSchreier_polyOver.
- rewrite /separable_poly derivB derivC subr0 derivB derivXn derivX -scaler_nat.
  rewrite charf0// scale0r add0r -(@coprimepZr _ (-1)) ?oppr_eq0 ?oner_eq0//.
  by rewrite scaleNr scale1r opprK coprimep1.
- by apply: ArtinSchreier_splitting.
Qed.

Lemma minPoly_ArtinSchreier : x \notin E -> minPoly E x = AS.
Proof.
move=> xE; have /(minPoly_dvdp ArtinSchreier_polyOver) : root AS x.
  by rewrite ASE root_prod_XsubC.
rewrite ASE => /dvdp_prod_XsubC[m]; rewrite eqp_monic ?monic_minPoly//;
  last by rewrite monic_prod// => i _; rewrite monic_XsubC.
rewrite -map_mask.
have [{}m sm ->] := resize_mask m (enum 'I_p).
set s := mask _ _ => /eqP mEx.
have [|smp_gt0] := posnP (size s).
  case: s mEx => // /(congr1 (horner^~x))/esym/eqP.
  by rewrite minPolyxx big_nil hornerC oner_eq0.
suff leq_pm : (p <= size s)%N.
  move: mEx; suff /eqP -> : s == enum 'I_p by [].
  by rewrite -(geq_leqif (size_subseq_leqif _)) ?mask_subseq// size_enum_ord.
have /polyOverP/(_ (size s).-1%N) := minPolyOver E x; rewrite {}mEx.
rewrite -(size_map (fun i => x + (val i)%:R)).
rewrite coefPn_prod_XsubC size_map -?lt0n// big_map.
rewrite memvN big_split/= big_const_seq count_predT iter_addr_0 => DE.
have sE: \sum_(i <- s) i%:R \in E by apply: rpred_sum => i _; apply: rpred_nat.
move: (rpredB DE sE) => {DE} {sE}.
rewrite -addrA subrr addr0 => xsE.
apply/negP => sltp.
have /coprimeP: coprime (size s) p.
  rewrite coprime_sym (prime_coprime _ pprim).
  by apply/negP => /(dvdn_leq smp_gt0).
move=> /(_ smp_gt0) [[u v]]/= uv1.
have /ltnW vltu: (v * p < u * size s)%N by rewrite ltnNge -subn_eq0 uv1.
move: uv1 => /eqP; rewrite -(eqn_add2l (v * p)) addnBA// addnC -addnBA//.
rewrite subnn addn0 => /eqP sE.
move: xsE => /(rpredMn u).
rewrite -mulrnA mulnC sE addn1 mulrS mulrnA -mulr_natr.
move: p0 => /eqP ->; rewrite mulr0 addr0.
by move: xE => /negP.
Qed.

End ArtinSchreier.

