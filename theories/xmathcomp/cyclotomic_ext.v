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

(** Very Hard **)
(*     - E(x) is cyclotomic                                                   *)
Lemma minPoly_cyclotomic : r \notin E -> minPoly E r = cyclotomic r n.
Proof.
move=> NEr.
have lt0n : (0 < n)%N by exact: prim_order_gt0 r_is_nth_root.
suff dvd_cyclo_min : cyclotomic r n %| minPoly E r.
  apply/eqP; rewrite -eqp_monic ?monic_minPoly ?cyclotomic_monic//.
  by rewrite /eqp minPoly_dvdp ?root_cyclotomic ?cyclotomic_over.
suff prim_roots z : n.-primitive_root z -> root (minPoly E r) z.
  rewrite /cyclotomic -big_filter; have [s es [uniqs sP /= perms]] := big_enumP.
  pose rs := [seq r ^+ (val i) | i <- s]; set p := (X in X %| _).
  have {p} -> :  p = \prod_(z <- rs) ('X - z%:P) by rewrite /p big_map.
  have uniq_rs : poly.uniq_roots rs.
    rewrite uniq_rootsE /rs map_inj_in_uniq // => j k.
    rewrite !sP => copjn copkn /eqP; rewrite (eq_prim_root_expr r_is_nth_root).
    by rewrite !modn_small ?ltn_ord //; move/eqP; apply/val_inj.
  apply: uniq_roots_dvdp=> //; apply/allP=> x /mapP[[y ltyn]]; rewrite sP /=.
  by move=> copyn ->; apply: prim_roots=> //; rewrite prim_root_exp_coprime.
suff prime_pow_root s p : root (minPoly E r) s ->
     prime p -> ~~ (p %| n)%N -> root (minPoly E r) (s ^+ p).
  case/(primitive_root_pow r_is_nth_root)=> m copmn ->.
  have prime_pow_pow_root p k s : root (minPoly E r) s ->
    prime p -> (0 < k)%N -> ~~(p %| n)%N ->  root (minPoly E r) (s ^+ (p ^ k)).
    move=> primroots primp lt0k Ndvdpn; elim: k lt0k => [|k ihk _] //.
    rewrite expnS mulnC exprM; apply: prime_pow_root=> //.
    case: (posnP k) => [ek0 | lt0k]; last exact: ihk.
    by rewrite ek0 expn0 expr1.
  case: (posnP m)=> [em0 | lt0m].
  move: copmn; rewrite em0 expr0 /coprime gcd0n => /eqP en1.
  suff -> : r = 1 by rewrite root_minPoly.
    by move/prim_expr_order: r_is_nth_root; rewrite en1 expr1.
  move/prod_prime_decomp: lt0m->; move: (@mem_prime_decomp m).
  elim: (prime_decomp m) => [_ | [p k] d ihd dP].
    by rewrite big_nil expr1 root_minPoly.
  rewrite big_cons /= mulnC exprM.
  have /dP [prime_p lt0k pk_dvd_m] : (p, k) \in (p, k) :: d by rewrite inE eqxx.
  have Npdvdn : ~~ (p %| n)%N.
    suff /coprime_dvdl : (p %| m)%N by move/(_ _ copmn); rewrite prime_coprime.
    apply: dvdn_trans pk_dvd_m; rewrite -{1}(expn1 p); exact: dvdn_exp2l.
  apply: prime_pow_pow_root=> //; apply: ihd => q l dql; apply: dP.
  by rewrite inE dql orbT.


(* admit. (* todo: change block above into proof of this *) *)
(* move=> lt0in cop_i_n.          *)
(* have n_gt0 := prim_order_gt0 r_is_nth_root. *)
(* have Dpr := Phi_cyclotomic r_is_nth_root; set pr := cyclotomic r n in Dpr *. *)

(* have mon_pr: pr \is monic by apply: cyclotomic_monic. *)
(* have pr0: root pr r by rewrite root_cyclotomic. *)
(* have /polyOver_subvs[pf Dpf] := minPolyOver E r. *)
(* have mon_pf : pf \is monic. *)
(*   suff : map_poly vsval pf \is monic by rewrite map_monic. *)
(*   by rewrite -Dpf monic_minPoly. *)
(* have dv_pf Q : root (map_poly vsval Q) r = (pf %| Q). *)
(*   set P := map_poly _ _. *)
(*   have Ep : P \is a polyOver E by apply/polyOver_subvs; exists Q. *)
(*   apply/idP/idP=> [/(minPoly_dvdp Ep) | pfdvdq]. *)
(*   - by rewrite Dpf dvdp_map.  *)
(*   - have: minPoly E r %| P by rewrite Dpf dvdp_map. *)
(*     apply/root_dvdp; exact: root_minPoly. *)
(* have pfdvdPhin : pf %| map_poly intr 'Phi_n. *)
(*   rewrite -dv_pf; congr (root _ r): pr0; rewrite -Dpr -map_poly_comp. *)
(*   by apply: eq_map_poly => b; rewrite /= rmorph_int. *)
(* pose P : {poly subvs_of E} := 'X^n - 1. *)
(* have /dvdpP[Q ePQpf]: pf %| P. *)
(*   rewrite -dv_pf; apply/rootP. *)
(*   rewrite /P rmorphB /= map_polyXn hornerD hornerN hornerXn map_polyC /= hornerC. *)
(*   by rewrite algid1 prim_expr_order // subrr. *)
(* suff min_root x q : prime q -> ~~ (q %| n)%N -> *)
(*                       root (minPoly E r) x -> root (minPoly E r) (x ^+ q). *)
(*   move=> {ePQpf Q P dv_pf pfdvdPhin Dpf mon_pf pf pr0 mon_pr Dpr pr NEr}. *)
(*   have hpow q k t : prime q -> ~~ (q %| n)%N -> root (minPoly E r) t -> *)
(*                     root (minPoly E r) (t ^+ (q ^ k)). *)
(*     move=> pprime Npdvdn roots; elim: k => [| k ihk]. *)
(*     - by rewrite expn0 expr1. *)
(*     suff -> : t ^+ (q ^ k.+1) = (t ^+ (q ^ k)) ^+ q by exact: min_root. *)
(*     by rewrite expnS mulnC exprM.  *)
(*   have [a [-> prime_Ndiv]]: exists a : seq (nat * nat), *)
(*         i =  (\prod_(f <- a) f.1 ^ f.2)%N /\ *)
(*         (forall x, x \in a -> prime x.1 /\ (~~ (x.1 %| n))%N). *)
(*     exists (prime_decomp i). *)
(*     have lt0i : (0 < i)%N by case/andP: lt0in. *)
(*     split; first exact: prod_prime_decomp. *)
(*     move=> x; rewrite prime_decompE; case/mapP=> p primesp -> /=. *)
(*     move: primesp; rewrite mem_primes; case/and3P=> pp _ dvdpi; split=> //. *)
(*     rewrite -prime_coprime //; exact: (coprime_dvdl dvdpi). *)
(*   elim: a prime_Ndiv => [_ | p a iha Ndiv]. *)
(*   - by rewrite big_nil expr1 root_minPoly. *)
(*   rewrite big_cons; set P := (\prod_(_ <- _) _)%N. *)
(*   have -> : r ^+ (p.1 ^ p.2 * P)%N =  (r ^+  P) ^+  (p.1 ^ p.2)%N. *)
(*     by rewrite mulnC exprM. *)
(*   have /Ndiv [primep1 Ndvdp1n] : p \in p  :: a by rewrite inE eqxx. *)
(*   by apply: hpow => //; apply: iha => x ax; apply: Ndiv; rewrite inE ax orbT. *)

  (* todo: suff above is quite long... could probably shrink. *)
(* Then see, e.g., Theorem 4 of
http://www.lix.polytechnique.fr/~pilaud/enseignement/agreg/polynomes/polynomes.pdf
some proof patterns will be similar as in the proof of minCpoly_cyclotomic, and it
will then generalize it, hopefully.
*)
Admitted.


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
