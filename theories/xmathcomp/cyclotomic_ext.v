From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field.
From Abel Require Import char0 various.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Lemma Cyclotomic1 : 'Phi_1 = 'X - 1.
Proof.
by have := @prod_Cyclotomic 1%N isT; rewrite big_cons big_nil mulr1.
Qed.

Lemma Cyclotomic2 : 'Phi_2 = 'X + 1.
Proof.
have := @prod_Cyclotomic 2%N isT; rewrite !big_cons big_nil mulr1/=.
rewrite Cyclotomic1 -(@expr1n [ringType of {poly int}] 2%N).
by rewrite subr_sqr expr1n => /mulfI->//; rewrite polyXsubC_eq0.
Qed.

Lemma prim_root1 (F : fieldType) n : (n.-primitive_root (1 : F)) = (n == 1)%N.
Proof.
case: n => [|[|n]]//.
  by apply/'forall_eqP => i; rewrite ord1//= eqxx; apply/unity_rootP.
apply/'forall_eqP => /= /(_ (@Ordinal _ n _))/=/(_ _)/unity_rootP.
by rewrite !ltnS leqnSn ltn_eqF//; apply => //; rewrite expr1n.
Qed.

Lemma prim2_rootN1 (F : fieldType) : 2%:R != 0 :> F ->
   2.-primitive_root (- 1 : F).
Proof.
move=> tow_neq0; apply/'forall_eqP => -[[|[|]]]//= _; last first.
  by apply/unity_rootP; rewrite -signr_odd.
by apply/unity_rootP/eqP; rewrite expr1 eq_sym -addr_eq0 -mulr2n.
Qed.

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

Section CyclotomicExt.

Variables (F0 : fieldType) (L : fieldExtType F0).
Variables (E : {subfield L}) (r : L) (n : nat).
Hypothesis r_is_nth_root : n.-primitive_root r.

Lemma splitting_Fadjoin_cyclotomic :
  splittingFieldFor E (cyclotomic r n) <<E; r>>.
Proof.
exists [seq r ^+ val k | k <- enum 'I_n & coprime (val k) n].
  by rewrite /cyclotomic big_map big_filter big_enum_cond/= eqpxx.
rewrite map_comp -(filter_map _ (fun i => coprime i n)) val_enum_ord.
have [n_gt1|] := ltnP 1 n; last first.
  case: n r_is_nth_root (prim_order_gt0 r_is_nth_root) => [|[|]]//= rnth _ _.
  by rewrite adjoin_seq1 expr0 -[r]expr1 prim_expr_order.
set s := (X in <<_ & X>>%VS); suff /eq_adjoin-> : s =i r :: s.
  rewrite adjoin_cons (Fadjoin_seq_idP _)//.
  by apply/allP => _/mapP[i _ ->]/=; rewrite rpredX// memv_adjoin.
move=> x; rewrite in_cons orbC; symmetry; have []//= := boolP (_ \in _).
apply: contraNF => /eqP ->; rewrite -[r]expr1 map_f//.
by rewrite mem_filter mem_iota// coprime1n.
Qed.

Lemma cyclotomic_over : cyclotomic r n \is a polyOver E.
Proof.
by apply/polyOverP=> i; rewrite -Phi_cyclotomic // coef_map /= rpred_int.
Qed.

Hint Resolve cyclotomic_over : core.

End CyclotomicExt.

Section Cyclotomic.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (E : {subfield L}) (r : L) (n : nat).
Hypothesis r_is_nth_root : n.-primitive_root r.

(* MISSING *)
Lemma root_dvdp (F : idomainType) (p q : {poly F}) (x : F) :
  root p x -> p %| q -> root q x.
Proof. rewrite -!dvdp_XsubCl; exact: dvdp_trans. Qed.

(* MISSING *)
Lemma primitive_root_pow (F : fieldType) (m : nat) (s z : F) :
  m.-primitive_root s -> m.-primitive_root z -> exists2 k, coprime k m & z = s ^+ k.
Proof.
move/root_cyclotomic<-.
rewrite /cyclotomic -big_filter; have [t et [uniqs tP /= perms]] := big_enumP.
pose rs := [seq s ^+ (val i) | i <- t]; set p := (X in root X).
have {p} -> :  p = \prod_(z <- rs) ('X - z%:P) by rewrite /p big_map.
rewrite root_prod_XsubC; case/mapP=> [[i ltim]]; rewrite tP /= => copim ez.
by exists i.
Qed.

(** Easy **)
(*     - E(x) is Galois                                                       *)
Lemma galois_Fadjoin_cyclotomic : galois E <<E; r>>.
Proof.
apply/splitting_galoisField; exists (cyclotomic r n).
split; rewrite ?cyclotomic_over//; last exact: splitting_Fadjoin_cyclotomic.
rewrite /cyclotomic -(big_image _ _ _ (fun x => 'X - x%:P))/=.
rewrite separable_prod_XsubC map_inj_uniq ?enum_uniq// => i j /eqP.
by rewrite (eq_prim_root_expr r_is_nth_root) !modn_small// => /eqP/val_inj.
Qed.

Lemma abelian_cyclotomic : abelian 'Gal(<<E; r>> / E)%g.
Proof.
case: (boolP (r \in E)) => [r_in_E |r_notin_E].
  suff -> : ('Gal(<<E; r>> / E) = 1)%g by apply: abelian1.
  apply/eqP; rewrite -subG1; apply/subsetP => x x_in.
  rewrite inE gal_adjoin_eq ?group1 // (fixed_gal _ x_in r_in_E) ?gal_id //.
  by have /Fadjoin_idP H := r_in_E; rewrite -{1}H subvv.
rewrite card_classes_abelian /classes.
apply/eqP; apply: card_in_imset => f g f_in g_in; rewrite -!orbitJ.
move/orbit_eqP/orbitP => [] h h_in <- {f f_in}; apply/eqP.
rewrite gal_adjoin_eq //= /conjg /= ?groupM ?groupV //.
rewrite ?galM ?memv_gal ?memv_adjoin //.
have hg_gal f : f \in 'Gal(<<E; r>> / E)%g -> ((f r) ^+ n = 1)%R.
  by move=> f_in; apply/prim_expr_order; rewrite fmorph_primitive_root.
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
