From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field polyrcf.
From Abel Require Import various classic_ext map_gal algR.
From Abel Require Import char0 cyclotomic_ext real_closed_ext artin_scheier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section Temp.

(* NB : rpredM and mulrPred uses that 1 is in the subset, which is useless.
  Predicates should be defined for {aspace aT}. *)

Lemma memv_mulr_2closed [K : fieldType] [aT : FalgType K] (U : {aspace aT}) :
  GRing.mulr_2closed U.
Proof.
move: U => [U]/[dup]/andP[_ /subvP UU] Ualg.
move=> u v uU vU; apply/UU/memv_mulP.
exists 1%N, (@Tuple _ _ [:: u] (eqxx _)), (@Tuple _ _ [:: v] (eqxx _)).
split => /=.
- by rewrite uU.
- by rewrite vU.
- by rewrite big_ord1 2!(tnth_nth 1)/=.
Qed.

Lemma polyOver_mulr_2closed [R : ringType] [S : {pred R}]
  [addS : addrPred S] (kS : keyed_pred addS) :
  GRing.mulr_2closed kS -> GRing.mulr_2closed (polyOver kS).
Proof.
move=> SM u vz /polyOverP uS /polyOverP vS; apply/polyOverP => i.
by rewrite coefM rpred_sum // => j _; apply/SM.
Qed.

Lemma ahom_eq_adjoin [F0 : fieldType] [K : fieldExtType F0] [rT : FalgType F0]
  (f g : 'AHom(K, rT)) (U : {subfield K}) (x : K) :
  {in U, f =1 g} -> f x = g x -> {in <<U; x>>%VS, f =1 g}.
Proof.
move=> fgU fgx y /Fadjoin_poly_eq <-.
move: (Fadjoin_poly U x y) (Fadjoin_polyOver U x y) => p /polyOverP pU.
rewrite -(coefK p) horner_poly 2!rmorph_sum/=; apply/eq_bigr => i _.
by rewrite 2!rmorphM /= fgU// 2!rmorphX/= fgx.
Qed.

Lemma ahom_eq_adjoin_seq [F0 : fieldType] [K : fieldExtType F0]
  [rT : FalgType F0] (f g : 'AHom(K, rT)) (U : {aspace K}) (xs : seq K) :
  {in U, f =1 g} -> {in xs, forall x, f x = g x} -> {in <<U & xs>>%VS, f =1 g}.
Proof.
elim: xs U => [|x xs IHxs] U fgU fgxs.
   by rewrite adjoin_nil subfield_closed.
rewrite adjoin_cons.
have ->: <<U; x>>%VS = ASpace (agenv_is_aspace <<U; x>>%VS)
  by rewrite /= agenv_id.
move: fgxs (IHxs (ASpace (agenv_is_aspace <<U; x>>))) => fgxs /=.
rewrite agenv_id; apply.
   by apply/ahom_eq_adjoin/fgxs => //; apply/mem_head.
by move=> a axs; apply/fgxs; rewrite in_cons axs orbT.
Qed.

Lemma agenv_span (K : fieldType) (L : fieldExtType K) (U : {subfield L})
  (X : seq L) : <<X>>%VS = U -> <<1%VS & X>>%VS = U.
Proof.
move=> ->.
suff ->: (1+U)%VS = U by rewrite subfield_closed.
rewrite -{2}(subfield_closed U) (agenvEr U) subfield_closed.
by congr (1 + _)%VS; apply/esym/field_module_eq; rewrite sup_field_module.
Qed.

Lemma gal_ne (F0 : fieldType) (L : splittingFieldType F0) (E : {subfield L})
  (f g : gal_of E) : f = g \/ exists x, x \in E /\ f x != g x.
Proof.
move: (vbasisP E) => /span_basis/agenv_span LE.
case /boolP: (all (fun x => f x == g x) (vbasis E))
  => [/allP fgE | /allPn[x] xE fgx]; [ left | right ].
   2: by exists x; split => //; apply/vbasis_mem.
apply/eqP/gal_eqP.
rewrite -{1}LE; apply/ahom_eq_adjoin_seq => //; last by move=> x /fgE/eqP.
move: (gal1 f)(gal1 g).
rewrite gal_kHom ?sub1v// gal_kHom ?sub1v//.
move=> /andP [_ /subvP f1] /andP [_ /subvP g1].
by move=> x /[dup] /f1/fixedSpaceP -> /g1/fixedSpaceP ->.
Qed.

Lemma tnth_cons (T : Type) (x : T) (l : seq T) (i : 'I_(size l)) :
  tnth (in_tuple (x :: l)) (lift ord0 i) = tnth (in_tuple l) i.
Proof. by rewrite /tnth/=; apply/set_nth_default. Qed.

(* TODO : generalize to independance of characters *)

Lemma gal_free (F0 : fieldType) (L : splittingFieldType F0)
  (E : {subfield L}) (f : seq (gal_of E)) (k : 'I_(size f) -> L) :
  uniq f ->
  (forall i, k i = 0) \/
    (exists a, a \in E /\ \sum_(i < size f) k i * tnth (in_tuple f) i a != 0).
Proof.
move: {1}(size f) (Logic.eq_refl (size f)) => n.
elim: n f k => [|n IHn] f k fsize funiq.
   by left; case; move: k; rewrite -fsize.
case: f => [|s f] in k fsize funiq * => //.
case: f => [|s0 f] in k fsize funiq * => //.
   case /boolP: (k 0 == 0).
      move=> /eqP k0; left => i.
      by move: k0; congr (k _ = 0); apply/val_inj; case i; case.
   move=> /negPf k0; right; exists 1; rewrite big_ord1 /= rmorph1; split.
      by apply/mem1v.
   by apply/negP; rewrite mulr1 k0.
move: funiq; rewrite /= negb_or.
move=> /andP [/andP[ss0 sf]] /[dup] s0f /andP[_ funiq].
case: (gal_ne s s0) => [/eqP ss0E | [x [xE /negPf ss0x]]].
   by move: ss0; rewrite ss0E.
move: fsize => /eqP; rewrite eqSS => /eqP fsize.
case: (IHn [:: s0 & f]
  (fun i => (k (lift ord0 i) * (tnth (in_tuple [:: s0 & f]) i x - s x)))
  fsize s0f).
   move=> /(_ ord0)/=/eqP.
   rewrite mulf_eq0 subr_eq0 [s0 x == _]eq_sym ss0x orbF => k10.
   set k' := fun i : 'I_(size f).+1 => k
      (match splitP (i : 'I_(1 + size f)%N) with
      | SplitLo _ _ => ord0
      | SplitHi _ _ => lift ord0 i
      end).
   move: (IHn [:: s & f] k' fsize).
   have /[swap]/[apply]: uniq (s :: f) by apply/andP; split.
   case => [k0 | [a [aE fne0]]]; [left => i | right; exists a].
      case: i; case.
         move: (k0 ord0); rewrite /k'.
         by case: splitP => // + _ + ilt => _; congr (k _ = 0); apply/val_inj.
      case => [|i] ilt.
         by move: k10 => /eqP; congr (k _ = 0); apply/val_inj.
      have ile: (i.+1 < (size f).+1)%N by rewrite -ltnS.
      move: (k0 (Ordinal ile)); rewrite /k'.
      case: splitP => [[j]/=/[swap]<-// | /= _ _].
      by congr (k _ = 0); apply/val_inj.
   split => //.
   move: k10 fne0 => /eqP k10.
   rewrite 3!big_ord_recl/= k10 mul0r add0r.
   congr (_ * _ + _ != 0).
      by rewrite /k'; case: splitP => // [[i]] /=/(congr1 val).
   apply/eq_bigr => i _.
   rewrite tnth_cons (@tnth_cons _ s (s0 :: f) (lift ord0 i)) tnth_cons.
   congr (_ * _).
      by rewrite /k'; case: splitP => // [[j]]/=/[swap]<-.
move=> [y [yE fne0]]; right.
case /boolP:
  (\sum_(i < (size f).+2) k i * tnth (in_tuple [:: s, s0 & f]) i y == 0)
  => [| yne0]; last by exists y.
rewrite big_ord_recl/= addrC addr_eq0 {2}/tnth/= => /eqP.
under eq_bigr do rewrite (@tnth_cons _ s (s0 :: f)); move=> y0.
exists (x*y); split; first by apply/rpredM.
move: fne0; congr (_ != 0).
under [\sum_(_ < (size f).+1) _]eq_bigr do rewrite mulrBr mulrBl
  [X in _ - X * _]mulrC -mulrA -rmorphM/= -[X in _ - X]mulrA.
rewrite sumrB -mulr_sumr y0 mulrN mulrA opprK [s x * _]mulrC -mulrA -rmorphM/=.
rewrite addrC [in RHS]big_ord_recl {2}/tnth/=.
by under [in RHS]eq_bigr do rewrite (@tnth_cons _ s (s0 :: f)).
Qed.

Lemma big_condT [R : Type] [idx : R] (op : Monoid.com_law idx)
    [I : finType] (A : {pred I}) (F : I -> R) :
    \big[op/idx]_(i in A | true) F i = \big[op/idx]_(i in A) F i.
Proof. by rewrite big_mkcondr. Qed.

Lemma big_setT [R : Type] [idx : R] (op : Monoid.com_law idx)
    [I : finType] (F : I -> R) :
    \big[op/idx]_(i in [set: I]) F i = \big[op/idx]_i F i.
Proof. by under eq_bigl do rewrite inE. Qed.

Lemma galTrace_neq0 (F : fieldType) (L : splittingFieldType F)
  (K E : {subfield L}) : exists a, a \in E /\ galTrace K E a != 0.
Proof.
set l := enum [set: gal_of E].
have [] := gal_free
  (fun i : 'I_(size l) => (tnth (in_tuple l) i \in 'Gal(E / K)%G)%:R%:A)
  (enum_uniq _).
   have /[dup] l1 : 1%g \in l by rewrite mem_enum.
   rewrite -index_mem => lt1 /(_ (Ordinal lt1))/=/eqP.
   by rewrite /tnth (nth_index _ l1) group1/= scaler_eq0 2!oner_eq0.
move=> [x [xE s0]]; exists x; split => //.
move: s0; congr (_ != 0); rewrite /galTrace.
rewrite -(big_tuple _ _ _ xpredT (fun f => (f \in galoisG E K)%:R%:A * f x))/=.
rewrite /l [in RHS]big_mkcond/= big_enum /= big_setT; apply/eq_bigr => i _.
case: (i \in galoisG E K) => /=; first by rewrite mulr1n scale1r mul1r.
by rewrite mulr0n scale0r mul0r.
Qed.

Lemma ffun_sum [T : finType] [R : ringType] [E : vectType R]
  (f : seq (ffun_vectType T E)) (x : T) :
  (\sum_(i <- f) i) x = \sum_(i <- f) i x.
Proof.
elim: f; first by rewrite 2!big_nil ffunE.
move=> a f IHf.
by rewrite 2!big_cons ffunE IHf.
Qed.

(** Alternative: *)
(* Definition Zp_succ n : 'I_n -> 'I_n := if n is n.+1 then +%R ord_max else id. *)

Definition Zp_succ n (i : 'I_n) :=
  match i with
  | @Ordinal _ k klt => Ordinal (
      match n as n0 return (k < n0)%N -> (k.+1 %% n0 < n0)%N with
      | 0 => id
      | n0.+1 => fun=> ltn_pmod k.+1 (is_true_true : 0 < n0.+1)%N
      end klt)
  end.

(* TODO: généraliser sur toutes les définitions par imset. *)
(* Ah non, je change le domaine d'indexation, ce lemme est spécifique aux
 * éléments d'ordre fini d'un groupe. *)
Lemma cycle_imset [gT : finGroupType] (g : gT) :
  (<[g]> = [set g ^+ i | i : 'I_#[g]])%g.
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP => x.
   move=> /cycleP [i ->]; apply/imsetP.
   exists (Ordinal (ltn_pmod i (order_gt0 g))); rewrite ?in_setT//.
   by rewrite expg_mod_order.
by move=> /imsetP [i] _ ->; apply/cycleP; exists i.
Qed.

Lemma cycle_imset_inj [gT : finGroupType] (g : gT) :
  injective (fun i : 'I_#[g] => g ^+ i)%g.
Proof.
move=> [i ilt] [j jlt] /eqP; rewrite eq_expg_mod_order.
rewrite modn_small// modn_small// => /eqP ijE.
by apply/val_inj.
Qed.

Lemma Hilbert's_theorem_90_additive
  [F : fieldType] [L : splittingFieldType F]
    [K E : {subfield L}] [x : gal_of E]
    [a : L] :
  galois K E ->
  generator 'Gal(E / K) x ->
  a \in E ->
  reflect (exists2 b : L, b \in E & a = b - x b)
    (galTrace K E a == 0).
Proof.
move=> Egal /eqP DgalE Ea.
have galEx: x \in 'Gal(E / K)%g by rewrite DgalE cycle_id.
apply: (iffP eqP) => [normEa0 | [b Eb ->]]; last first.
   by rewrite raddfB/= galTrace_gal// subrr.
have [b [bE tb]] := galTrace_neq0 K E.
move Heqn : (\dim_K E) => n.
have ordx: #[x]%g = n by rewrite orderE -DgalE -(galois_dim Egal).
have xXn : (x ^+ n = 1)%g by rewrite -ordx orderE expg_order.
move: (Egal) => /galois_subW/field_dimS/ltn_divRL/[dup]/(_ 0%N).
rewrite mul0n adim_gt0 => dimgt0 /(_ 1%N); rewrite mul1n => dimgt1.
case: n => [|n] in Heqn ordx xXn *; first by move: dimgt0; rewrite Heqn.
have trE d : d \in E -> galTrace K E d = \sum_(0 <= i < n.+1) (x ^+ i)%g d.
   move=> dE; rewrite /galTrace DgalE cycle_imset => /=.
   by rewrite (big_imset _ (in2W (@cycle_imset_inj _ x))) /= ordx big_mkord.
have trI d : d \in E -> \sum_(0 <= i < n) (x ^+ i.+1)%g d = galTrace K E d - d.
  by move=> dE; rewrite trE// [in RHS]big_nat_recl//= expg0 gal_id addrC addKr.
pose c : L := (galTrace K E b)^-1
  * \sum_(0 <= i < n) (\sum_(0 <= j < i.+1) (x ^+ j)%g a) * (x ^+ i.+1)%g b.
have tr_b_E : galTrace K E b \in E by rewrite rpred_sum// => * /[!memv_gal].
exists c.
   rewrite rpredM// ?rpredV// ?rpred_sum// => i _.
   by rewrite rpredM//= ?memv_gal// rpred_sum// => j _; rewrite memv_gal.
rewrite rmorphM/= rmorphV/= ?unitfE//.
rewrite (fixedFieldP _ (galTrace_fixedField K bE))// -mulrBr rmorph_sum/=.
pose f i := (\sum_(1 <= j < i.+1) (x ^+ j)%g a) * (x ^+ i.+1)%g b.
have := @telescope_sumr _ 0 n f isT.
rewrite /f (@big_geq _ _ _ 1 1)// mul0r subr0 sumrB => /(canRL (addrK _)).
rewrite big_add1/= trI// normEa0 sub0r opprK addrC.
under eq_bigr => i.
  rewrite big_add1; under eq_bigr => j do rewrite expgSr galM//.
  by rewrite expgSr galM// -rmorph_sum/= -rmorphM /=; over.
move->; rewrite opprD addrA -sumrB xXn gal_id mulNr opprK.
under eq_bigr do rewrite big_nat_recl// expg0 gal_id big_add1/= mulrDl addrK.
by rewrite -mulr_sumr trI// mulrBr addrNK mulrCA mulVf ?mulr1.
Qed.

Lemma natf_partn_ne0 (R : idomainType) n :
  (n`_[char R]^')%:R != 0 :> R.
Proof.
have n_gt0 := (part_gt0 [char R]^' n).
apply/negP; rewrite /partn natr_prod prodf_seq_eq0 => /hasP [i] i0n.
rewrite unfold_in/= natrX expf_eq0 logn_gt0 mem_primes => /andP[/negP ichar].
move=> /andP[/andP[iprim _] i0]; apply/ichar; rewrite unfold_in/=.
by apply/andP.
Qed.

Lemma natf0_partn (R : idomainType) n : (0 < n)%N ->
  (n%:R == 0 :> R) = (n`_[char R] != 1)%N.
Proof.
move=> n_gt0.
apply/idP/idP => [n0 |].
   apply/negP => /eqP nchar1.
   move: n0; rewrite -(partnC [char R] n_gt0) nchar1 mul1n => n0.
   by move: (natf_partn_ne0 R n); rewrite n0.
rewrite partn_eq1// /pnat n_gt0/= => /allPn [p].
rewrite mem_primes => /andP [pprim /andP [_ pn]].
rewrite /negn/mem/= 2!unfold_in negbK /= => pchar.
by rewrite -(dvdn_charf pchar).
Qed.

Lemma primes_dvdn (m n : nat) :
  (0 < n)%N -> (m %| n)%N -> primes m = [seq p <- primes n | p \in primes m].
Proof.
move=> n0 mn; apply/(irr_sorted_eq ltn_trans ltnn (sorted_primes _)).
  by rewrite sorted_filter ?sorted_primes//; apply: ltn_trans.
move=> p; rewrite mem_filter; case: (boolP (_ \in _)) => //.
rewrite !mem_primes => /and3P[p_prime m_gt0 dvd_pm]/=.
by rewrite p_prime n0//= (dvdn_trans dvd_pm).
Qed.

Lemma dvdn_leq_logP (m n : nat) : (0 < m)%N -> (0 < n)%N ->
  reflect (forall p, prime p -> logn p m <= logn p n)%N (m %| n)%N.
Proof.
move=> m0 n0; apply/(iffP idP) => [mn p prim | vp_le]; first exact/dvdn_leq_log.
apply/dvdn_partP => // p /[!(inE, mem_primes)]/and3P[p_prime _ pm].
by rewrite p_part pfactor_dvdn// vp_le.
Qed.

Lemma logn_prod [I : Type] (r : seq I) (P : pred I) (F : I -> nat) (p : nat) :
  (forall n,  P n -> (0 < F n)%N) ->
  (logn p (\prod_(n <- r | P n) F n) = \sum_(n <- r | P n) logn p (F n))%N.
Proof.
move=> F_gt0; elim/(big_load (fun n => (n > 0)%N)): _.
elim/big_rec2: _; first by rewrite logn1.
by move=> i m n Pi [n_gt0 <-]; rewrite muln_gt0 lognM ?F_gt0.
Qed.

Lemma logn_partn (p n : nat) (pi : nat_pred) :
  logn p (n`_pi)%N = ((p \in pi) * logn p n)%N.
Proof.
have [p_prime|pNprime] := boolP (prime p); last first.
  by rewrite /logn !ifN// muln0.
have [ppi|pNpi] := boolP (p \in pi); last first.
  by rewrite mul0n logn_coprime// (@p'nat_coprime pi) ?part_pnat// pnatE.
by rewrite mul1n -logn_part partn_part ?logn_part// => i /eqP->.
Qed.

End Temp.
