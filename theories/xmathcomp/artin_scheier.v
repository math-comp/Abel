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
Proof. by move: pchar=>/andP[]. Qed.

Let p0 : p%:R == 0 :> L.
Proof. by move: pchar=>/andP[_]. Qed.

Let p1 : (1 < p)%N.
Proof. by apply prime_gt1. Qed.

Lemma ArtinScheier_factorize :
  'X^p - 'X - (x ^+ p - x)%:P =
  \prod_(z <- [seq x + (val i)%:R | i <- (index_enum (ordinal_finType p))])
      ('X - z%:P).
Proof.
case: p pchar pprim p0 p1 => // n nchar nprim n0 n1.
apply/eqP; rewrite -eqp_monic; first last.
- by apply monic_prod_XsubC.
- apply/monicP; rewrite -addrA -opprD lead_coefDl ?lead_coefXn//.
  by rewrite size_opp size_XaddC size_polyXn ltnS.
- rewrite eqp_sym -dvdp_size_eqp.
    rewrite big_map size_prod; last first.
      move=> [i]/= _ _; apply/negP => /eqP
        /(congr1 (fun p : {poly L} => size p)).
      by rewrite size_XsubC size_polyC eqxx.
      have ->: \big[addn/0%N]_(i < n.+1) size ('X - (x + (val i)%:R)%:P)%R =
    \big[addn/0%N]_(i < n.+1) 2%N.
      by apply eq_bigr=> i _; rewrite size_XsubC.
    rewrite big_const_ord iter_addn_0.
    rewrite -add1n mul2n -addnn addnA card_ord -addnBA// subnn addn0 add1n.
    rewrite -addrA -opprD size_addl size_polyXn// size_opp size_XaddC ltnS.
    by move: pchar => /andP [ /prime_gt1 ].
  apply uniq_roots_dvdp.
    apply/allP => + /mapP [i _ ->] => _.
    rewrite/root !hornerE ?hornerXn -(Frobenius_autE nchar (x + (val i)%:R)).
  (* FIXME: remove ?hornerXn when requiring MC >= 1.16.0 *)
    rewrite rmorphD/= rmorph_nat (Frobenius_autE nchar x).
    rewrite opprD opprB addrACA -addrA 2![x+_]addrA subrr add0r.
    by rewrite addrAC addrCA subrr addr0 addrC subrr.
  rewrite uniq_rootsE; apply/(uniqP 0) => i j.
  rewrite 2!inE size_map => ilt jlt.
  rewrite (nth_map ord0)// (nth_map ord0)// => /addrI/esym/eqP.
  set ip := nth ord0 (index_enum (ordinal_finType n.+1)) i.
  set jp := nth ord0 (index_enum (ordinal_finType n.+1)) j.
  move=>ijE.
  suff: jp = ip.
    rewrite/ip/jp => /esym ijE0.
    by move: (index_enum_uniq (ordinal_finType n.+1))=>/uniqP
      /(_ i j ilt jlt ijE0).
  move:ijE.
  wlog ij : {i} {j} {ilt} {jlt} ip jp / (val ip <= val jp)%N.
    move=> h.
    move: (Order.TotalTheory.le_total (val ip) (val jp)) => /orP; case => ij.
       by apply h.
    by rewrite eq_sym=> ijE; apply /esym/h.
  rewrite -subr_eq0 -natrB// -(dvdn_charf nchar).
  case /posnP: (val jp - val ip)%N.
    move=>/eqP; rewrite subn_eq0 => ji _; apply/val_inj/eqP.
    by rewrite Order.POrderTheory.eq_le; apply/andP; split.
  move=>ij0 /(dvdn_leq ij0); rewrite ltn_subRL -addnS.
  move=>/(leq_trans (leq_addl _ _)).
  have: (val jp < n.+1)%N by destruct jp.
  by rewrite ltnS => jle; move => /(leq_ltn_trans jle); rewrite ltnn.
Qed.

Lemma ArtinSchreier_splitting :
   splittingFieldFor E ('X^p - 'X - (x ^+ p - x)%:P) <<E; x>>%AS.
Proof.
exists ([seq x + (val i)%:R | i <- (index_enum (ordinal_finType p))]).
  by rewrite ArtinScheier_factorize big_map eqpxx.
apply/eqP; rewrite eqEsubv; apply/andP; split.
   apply/Fadjoin_seqP; split; first by apply subv_adjoin.
   move=>+ /mapP [i _ ->] => _.
   apply (@rpredD _ _ (memv_addrPred <<E; x>>%AS)); first by apply memv_adjoin.
   by apply rpred_nat.
apply/FadjoinP; split; first by apply subv_adjoin_seq.
case: p pchar pprim p0 p1 => // n nchar nprim n0 n1.
apply/seqv_sub_adjoin/mapP; exists ord0; first by apply mem_index_enum.
by rewrite addr0.
Qed.

Lemma ArtinSchreier_polyOver :
  'X^p - 'X - (x ^+ p - x)%:P \is a polyOver E.
Proof. by rewrite rpredB ?polyOverC// rpredB ?rpredX// polyOverX. Qed.

Lemma ArtinSchreier_galois :
  galois E <<E; x>>.
Proof.
apply/splitting_galoisField; exists ('X^p - 'X - (x ^+ p - x)%:P); split.
- exact ArtinSchreier_polyOver.
- rewrite/separable_poly derivB derivC subr0 derivB derivXn derivX -scaler_nat.
  move: pchar; rewrite inE => /andP[_ /eqP ->].
  rewrite scale0r add0r.
  apply/Bezout_eq1_coprimepP; exists (0, (-1)) => /=.
  by rewrite mul0r add0r mulN1r opprK.
- by apply ArtinSchreier_splitting.
Qed.

Lemma minPoly_ArtinSchreier : (x \notin E) ->
  minPoly E x = 'X^p - 'X - (x ^+ p - x)%:P.
Proof.
move=> xE.
have /(minPoly_dvdp ArtinSchreier_polyOver): root ('X^p - 'X - (x ^+ p - x)%:P) x.
  rewrite ArtinScheier_factorize root_prod_XsubC.
  case: p pchar pprim p0 p1 => // n nchar nprim n0 n1.
  apply/mapP; exists ord0; first by rewrite mem_index_enum.
  by rewrite addr0.
rewrite ArtinScheier_factorize big_map.
move=> /dvdp_prod_XsubC[m]; rewrite eqp_monic ?monic_minPoly//; last first.
  by rewrite monic_prod// => i _; rewrite monic_XsubC.
have [{}m sm ->] := resize_mask m (index_enum (ordinal_finType p)).
set s := mask _ _ => /eqP mEx.
have [|smp_gt0] := posnP (size s).
  case: s mEx => // /(congr1 (horner^~x))/esym/eqP.
  by rewrite minPolyxx big_nil hornerC oner_eq0.
suff leq_pm : (p <= size s)%N.
  move: mEx; suff /eqP->: s == index_enum (ordinal_finType p) by [].
  rewrite -(geq_leqif (size_subseq_leqif _)) ?mask_subseq//.
  by rewrite/index_enum; case: index_enum_key=>/=; rewrite -enumT size_enum_ord.
have /polyOverP/(_ (size s).-1%N) := minPolyOver E x; rewrite {}mEx.
have ->: \prod_(i <- s) ('X - (x + (val i)%:R)%:P) = \prod_(i <- [seq x + (val i)%:R | i <- s]) ('X - i%:P) by rewrite big_map.
rewrite -(size_map (fun i => x + (val i)%:R)) coefPn_prod_XsubC size_map -?lt0n// big_map.
rewrite memvN big_split/= big_const_seq count_predT iter_addr_0 => DE.
have sE: \sum_(i <- s) i%:R \in E by apply rpred_sum => i _; apply rpred_nat.
move:(rpredB DE sE) => {DE} {sE}.
rewrite -addrA subrr addr0 => xsE.
apply/negP => sltp.
have /coprimeP: coprime (size s) p.
  by rewrite coprime_sym (prime_coprime _ pprim); apply/negP => /(dvdn_leq smp_gt0).
move=> /(_ smp_gt0) [[u v]]/= uv1.
have /ltnW vltu: (v * p < u * size s)%N by rewrite ltnNge -subn_eq0 uv1.
move:uv1 => /eqP; rewrite -(eqn_add2l (v * p)) addnBA// addnC -addnBA// subnn addn0 => /eqP sE.
move: xsE => /(rpredMn u); rewrite -mulrnA mulnC sE addn1 mulrS mulrnA -mulr_natr.
move: p0 => /eqP ->; rewrite mulr0 addr0.
by move: xE => /negP.
Qed.

End ArtinSchreier.

