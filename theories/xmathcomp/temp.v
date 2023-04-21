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

Lemma ord_S_split n (i: 'I_n.+1): {j: 'I_n | i = lift ord0 j} + {i = ord0}.
Proof.
case: i; case=>[| i] ilt.
   by right; apply val_inj.
by left; exists (Ordinal (ltnSE ilt)); apply val_inj.
Qed.

(* NB : rpredM and mulrPred uses that 1 is in the subset, which is useless. Predicates should be defined for {aspace aT}. *)

Lemma memv_mulr_2closed [K : fieldType] [aT : FalgType K] (U : {aspace aT}) : GRing.mulr_2closed U.
Proof.
move: U => [U]/[dup]/andP[_ /subvP UU] Ualg.
move=> u v uU vU; apply/UU/memv_mulP; exists 1%N, (@Tuple _ _ [:: u] (eqxx _)), (@Tuple _ _ [:: v] (eqxx _)); split => /=.
- by rewrite uU.
- by rewrite vU.
- by rewrite big_ord1 2!(tnth_nth 1)/=.
Qed.

Lemma polyOver_mulr_2closed [R : ringType] [S : {pred R}] [addS : addrPred S] (kS : keyed_pred addS) : GRing.mulr_2closed kS -> GRing.mulr_2closed (polyOver kS).
Proof.
move=>SM u vz /polyOverP uS /polyOverP vS; apply/polyOverP => i.
by rewrite coefM rpred_sum // => j _; apply SM.
Qed.

Lemma ahom_eq_adjoin [F0 : fieldType] [K : fieldExtType F0] [rT : FalgType F0] (f g : 'AHom(K, rT))
  (U : {subfield K}) (x : K) :
  {in U, f =1 g} -> f x = g x -> {in <<U; x>>%VS, f =1 g}.
Proof.
move=>fgU fgx y /Fadjoin_poly_eq <-.
move:(Fadjoin_polyOver U x y); generalize (Fadjoin_poly U x y) => p /polyOverP pU.
rewrite -(coefK p) horner_poly 2!rmorph_sum/=; apply eq_bigr => i _.
by rewrite 2!rmorphM /= fgU// 2!rmorphX/= fgx.
Qed.

Lemma ahom_eq_adjoin_seq [F0 : fieldType] [K : fieldExtType F0] [rT : FalgType F0] (f g : 'AHom(K, rT))
  (U : {aspace K}) (xs : seq K) :
  {in U, f =1 g} -> all (fun x => f x == g x) xs -> {in <<U & xs>>%VS, f =1 g}.
Proof.
elim: xs U => [|x xs IHxs] U fgU fgxs.
   by rewrite adjoin_nil subfield_closed.
rewrite adjoin_cons.
have ->: <<U; x>>%VS = ASpace (agenv_is_aspace <<U; x>>%VS) by rewrite /= agenv_id.
move: fgxs (IHxs (ASpace (agenv_is_aspace <<U; x>>))) => /andP[/eqP fgx fgxs] /=.
by rewrite agenv_id => /(_ (ahom_eq_adjoin fgU fgx) fgxs).
Qed.

Lemma agenv_span (K : fieldType) (L : fieldExtType K) (U : {subfield L}) (X : seq L) : <<X>>%VS = U -> <<1%VS & X>>%VS = U.
Proof.
move=>->. 
suff ->: (1+U)%VS = U by rewrite subfield_closed.
rewrite -{2}(subfield_closed U) (agenvEr U) subfield_closed.
by congr (1 + _)%VS; apply/esym/field_module_eq; rewrite sup_field_module.
Qed.

Lemma gal_ne (F0 : fieldType) (L : splittingFieldType F0) (E : {subfield L}) (f g : FinGroup.finType (gal_finGroupType E)) : f = g \/ exists x, x \in E /\ f x != g x.
Proof.
move:(vbasisP E)=>/span_basis/agenv_span LE.
case/boolP: (all (fun x => f x == g x) (vbasis E)) => [fgE | /allPn[x] xE fgx]; [ left | right ].
   2: by exists x; split=>//; apply vbasis_mem.
apply/eqP/gal_eqP.
rewrite -{1}LE; apply ahom_eq_adjoin_seq=>//.
move:(gal1 f)(gal1 g).
rewrite gal_kHom ?sub1v// gal_kHom ?sub1v// => /andP [_ /subvP f1] /andP [_ /subvP g1].
by move=>x /[dup] /f1/fixedSpaceP -> /g1/fixedSpaceP ->.
Qed.

Lemma tnth_cons (T : Type) (x : T) (l : seq T) (i : 'I_(size l)): tnth (in_tuple (x :: l)) (lift ord0 i) = tnth (in_tuple l) i.
Proof. by rewrite/tnth/=; apply set_nth_default. Qed.

Lemma gal_free (F0 : fieldType) (L : splittingFieldType F0) (E : {subfield L}) (f : seq (FinGroup.finType (gal_finGroupType E))) (k : 'I_(size f) -> L) : uniq f -> (forall i, k i = 0) \/ (exists a, a \in E /\ \sum_(i < size f) k i * tnth (in_tuple f) i a != 0).
Proof.
move:(Logic.eq_refl (size f)); generalize (size f) at 1 => n.
elim: n f k => [|n IHn] f k fsize funiq.
   by left; case; move: k; rewrite -fsize.
destruct f as [| s f] => //.
destruct n; destruct f as [| s0 f] => //.
   case/boolP: (k 0 == 0).
      move=>/eqP k0; left => i.
      by move: k0; congr (k _ = 0); apply val_inj; case i; case.
   move=>/negPf k0; right; exists 1; rewrite big_ord1 /= rmorph1; split.
      by apply mem1v.
   by apply/negP; rewrite mulr1 k0.
move: funiq => /=; rewrite negb_or => /andP [/andP[ss0 sf]] /[dup] s0f /andP[_ funiq].
case: (gal_ne s s0) => [/eqP ss0E | [x [xE /negPf ss0x]]].
   by move: ss0; rewrite ss0E.
move:fsize=>/eqP; rewrite eqSS=>/eqP fsize.
case: (IHn [:: s0 & f] (fun i => (k (lift ord0 i) * (tnth (in_tuple [:: s0 & f]) i x - s x))) fsize s0f).
   move=>/(_ ord0)/=/eqP; rewrite mulf_eq0 subr_eq0 [s0 x == _]eq_sym ss0x orbF => k10.
   set k' := fun i : 'I_(size f).+1 => k (if ord_S_split i then lift ord0 i else ord0).
   move: (IHn [:: s & f] k' fsize).
   have /[swap]/[apply]: uniq (s :: f) by apply/andP; split.
   case => [k0 | [a [aE fne0]]]; [left => i | right; exists a].
      case: i; case.
         move: (k0 ord0); rewrite/k'.
         case: (ord_S_split _) => [[i /=/(congr1 val)//] | /= _ /[swap] ilt].
         by congr (k _ = 0); apply val_inj.
      case => [|i] ilt.
         by move: k10 => /eqP; congr (k _ = 0); apply val_inj.
      have ile: (i.+1 < (size f).+1)%N by rewrite -ltnS.
      move:(k0 (Ordinal ile)); rewrite/k'.
      case: (ord_S_split _) => [/= _| /[dup]/(congr1 val)//].
      by congr (k _ = 0); apply val_inj.
   split=>//.
   move:k10 fne0 => /eqP k10.
   rewrite 3!big_ord_recl/= k10 mul0r add0r.
   congr (_ * _ + _ != 0).
      by rewrite/k'; case: (ord_S_split _) => // [[i]] /=/(congr1 val).
   apply eq_bigr => i _; rewrite tnth_cons (@tnth_cons _ s (s0 :: f) (lift ord0 i)) tnth_cons; congr (_ * _).
      by rewrite/k'; case: (ord_S_split _).
move=>[y [yE fne0]]; right.
case /boolP: (\sum_(i < (size f).+2) k i * tnth (in_tuple [:: s, s0 & f]) i y == 0)  => [| yne0].
   2: by exists y.
rewrite big_ord_recl/= addrC addr_eq0 {2}/tnth/= => /eqP.
under eq_bigr do rewrite (@tnth_cons _ s (s0 :: f)); move=> y0.
exists (x*y); split; first by apply rpredM.
move: fne0; congr (_ != 0).
under [\sum_(_ < (size f).+1) _]eq_bigr do rewrite mulrBr mulrBl [X in _ - X * _]mulrC -mulrA -rmorphM/= -[X in _ - X]mulrA.
rewrite sumrB -mulr_sumr y0 mulrN mulrA opprK [s x * _]mulrC -mulrA -rmorphM/= addrC [in RHS]big_ord_recl {2}/tnth/=.
by under [in RHS]eq_bigr do rewrite (@tnth_cons _ s (s0 :: f)).
Qed.

Lemma galTrace_ne_0 (F : fieldType) (L : splittingFieldType F) (K E : {subfield L}) : exists a, a \in E /\ galTrace K E a != 0.
Proof.
set l := index_enum (FinGroup.finType (gal_finGroupType E)).
case: (gal_free (fun i : 'I_(size l) => (1 *+ ((tnth (in_tuple l) i) \in (galoisG E K) : nat))%:A) (index_enum_uniq _)).
   have /[dup] l1: 1%g \in l by apply mem_index_enum.
   rewrite -index_mem => lt1.
   by move=>/(_ (Ordinal lt1))/=/eqP; rewrite /tnth (nth_index _ l1) group1/= scaler_eq0 2!oner_eq0.
move=>[x [xE s0]]; exists x; split=>//; move:s0; congr (_ != 0).
rewrite/galTrace -(big_tuple _ _ _ xpredT (fun f => (f \in galoisG E K)%:R%:A * f x))/=/l.
rewrite [in RHS]big_mkcond/=; apply eq_bigr => i _.
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


Definition Zp_succ n (i : 'I_n) := Ordinal (
  match n with
  | 0 => fun i0 : 'I_0 => match i0 with | @Ordinal _ _ i0 => i0 end
  | n0.+1 => fun i0 => (ltn_pmod i0.+1 (is_true_true : (is_true (0 < n0.+1)%N)))
  end i).

Lemma cycle_imset [gT : finGroupType] (g : gT) : <[g]>%g = @Imset.imset (ordinal_finType #[g]%g) (FinGroup.finType gT) (fun i => (g ^+ (val i))%g) (mem setT).
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP => x.
   move=>/cycleP [i ->]; apply/imsetP.
   exists (Ordinal (ltn_pmod i (order_gt0 g))); rewrite ?in_setT//.
   by rewrite expg_mod_order.
by move=>/imsetP [i] _ ->; apply/cycleP; exists i.
Qed.

Lemma cycle_imset_inj [gT : finGroupType] (g : gT) : {in setT &, injective (fun i : 'I_(#[g]%g) => (g ^+ i)%g)}.
Proof.
move=>[i ilt] [j jlt]/= _ _ /eqP; rewrite eq_expg_mod_order.
rewrite modn_small// modn_small// => /eqP ijE.
by apply val_inj.
Qed.

Lemma big_condT [R : Type] [idx : R] (op : Monoid.com_law idx) 
    [I : finType] (A : {pred I}) (F : I -> R) :
    \big[op/idx]_(i in A | true) F i = \big[op/idx]_(i in A) F i.
Proof. by apply congr_big => // i; rewrite andbT. Qed.

Lemma big_setT [R : Type] [idx : R] (op : Monoid.com_law idx) 
    [I : finType] (F : I -> R) :
    \big[op/idx]_(i in [set: I]) F i = \big[op/idx]_i F i.
Proof. by apply congr_big => // i; rewrite in_setT. Qed.

Lemma Hilbert's_theorem_90_additive
  [F : fieldType] [L : splittingFieldType F] 
    [K E : {subfield L}] [x : gal_finGroupType E] 
    [a : L] :
  galois K E ->
  generator 'Gal(E / K) x ->
  a \in E ->
  reflect (exists2 b : L, b \in E & a = b - x b)
    (galTrace K E a == 0).
Proof.
move=>Egal /(_ =P <[x]>%g) DgalE Ea.
have galEx: x \in 'Gal(E / K)%g by rewrite DgalE cycle_id.
apply: (iffP eqP) => [normEa1 | [b Eb ->]]; last first.
  by rewrite galTrace_is_additive galTrace_gal// subrr.
move:(galTrace_ne_0 K E) => [b [bE tb]].
remember (\dim_K E) as n.
have ordx: #[x]%g = n by rewrite orderE -DgalE -(galois_dim Egal).
move:(expg_order x); rewrite ordx => xord.
move:(Egal) => /galois_subW/field_dimS/ltn_divRL/[dup]/(_ 0%N). 
rewrite mul0n adim_gt0 => dimgt0 /(_ 1%N); rewrite mul1n => dimgt1.
destruct n; first by move:dimgt0; rewrite -Heqn.
destruct n.
   move:dimgt1; rewrite -Heqn ltnn => /esym/negbT; rewrite -leqNgt => dimEK.
   move:(eqEdim K E); rewrite dimEK (galois_subW Egal) => /=/eqP KE.
   move:normEa1; rewrite/galTrace.
   have ->: \sum_(x0 in ('Gal(E / K))%g) x0 a = \sum_(x0 in ('Gal(E / K))%g) a.
      apply eq_bigr => f fgal.
      move:Egal=>/galois_fixedField Kfix.
      by move:(Ea); rewrite -{1}KE -Kfix => /fixedFieldP => /(_ Ea f fgal).
   rewrite sumr_const; rewrite -(galois_dim Egal) -Heqn mulr1n => a0.
   by exists a => //; rewrite a0 rmorph0 subr0.
set c := (galTrace K E b)^-1 * \sum_(i < n.+1) (\sum_(j < i.+1) (x ^+ j)%g a) * (x ^+ i.+1)%g b. 
have tbE: galTrace K E b \in E by rewrite /galTrace rpred_sum// => f _; apply memv_gal.
exists c.
   apply rpredM; first by rewrite rpredV.
   rewrite rpred_sum// => i _.
   apply rpredM; last by apply memv_gal.
   by rewrite rpred_sum// => j _; apply memv_gal.
rewrite/c rmorphM/= rmorphV/= ?unitfE//.
move:(galTrace_fixedField K bE) => /fixedFieldP => /(_ tbE x galEx) ->.
rewrite -mulrBr rmorph_sum/=.
rewrite big_ord_recl big_ord1 expg0 gal_id expg1 big_ord_recr/=.
rewrite opprD addrAC [_ - x _]addrC addrA -addrA [- _ + _]addrC -sumrB.
have ->: \sum_(i < n) ((\sum_(j < (bump 0 i).+1) (x ^+ j)%g a) * (x ^+ (bump 0 i).+1)%g b -
     x ((\sum_(j < i.+1) (x ^+ j)%g a) * (x ^+ i.+1)%g b)) =
     \sum_(i < n) a * (x ^+ i.+2)%g b.
   apply eq_bigr; case => i ilt _ /=.
   rewrite/bump/= add1n rmorphM/= rmorph_sum/= expgSr galM// -mulrBl; congr (_ * _).
   rewrite big_ord_recl/= -addrA -sumrB expg0 gal_id -[in RHS](addr0 a); congr (a + _).
   transitivity (\sum_(j < i.+1) (0 : L)); last by rewrite sumr_const mul0rn.
   by apply eq_bigr => j _; rewrite/bump/= add1n expgSr galM// subrr.
rewrite -mulr_sumr rmorphM/= rmorph_sum/=.
have tE: forall d, d \in E -> galTrace K E d = \sum_(i < n.+2) (x ^+ i)%g d.
   move=>d dE.
   rewrite/galTrace DgalE cycle_imset => /=.
   rewrite -big_condT/=.
   rewrite (big_imset_cond _ _ _ (@cycle_imset_inj _ x)).
   by rewrite big_condT /= ordx big_setT/= big_ord_recl expg0 gal_id.
move:normEa1; rewrite tE// big_ord_recl expg0 gal_id => /eqP.
under [in X in X -> _]eq_bigr do rewrite /=/bump/=add1n expgSr galM//.
rewrite addrC addr_eq0 => /eqP ->.
rewrite mulNr opprK -2!mulrDr mulrCA -(galM _ x bE) -expgSr xord gal_id [x b + b]addrC.
have <-: galTrace K E b = b + x b + \sum_(i < n) (x ^+ i.+2)%g b.
   rewrite (tE b bE) big_ord_recl/= expg0 gal_id big_ord_recl/= expg1 addrA.
   by under eq_bigr do rewrite /bump/= 2!add1n.
by rewrite mulVf// mulr1.
Qed.

Lemma natf_partn_ne0 (R : idomainType) n :
  (n`_[char R]^')%:R != 0 :> R.
Proof.
have n_gt0 := (part_gt0 [char R]^' n).
apply/negP; rewrite/partn natr_prod prodf_seq_eq0 => /hasP [i] i0n.
rewrite unfold_in/= natrX expf_eq0 logn_gt0 mem_primes => /andP[/negP ichar].
move=>/andP[/andP[iprim _] i0]; apply ichar; rewrite unfold_in/=.
by apply/andP.
Qed.

Lemma natf0_partn (R : idomainType) n : (0 < n)%N -> (n%:R == 0 :> R) = (n`_[char R] != 1)%N.
Proof.
move=>n_gt0.
apply/idP/idP => [n0 |].
   apply/negP => /eqP nchar1.
   move:n0; rewrite -(partnC [char R] n_gt0) nchar1 mul1n => n0.
   by move:(natf_partn_ne0 R n); rewrite n0.
rewrite partn_eq1// /pnat n_gt0/= => /allPn [p].
rewrite mem_primes => /andP [pprim /andP [_ pn]].
rewrite /negn/mem/= 2!unfold_in negbK /= => pchar.
by rewrite -(dvdn_charf pchar).
Qed.

Lemma primes_dvdn (m n : nat) :
  (0 < n)%N -> (m %| n)%N -> primes m = [seq p <- primes n | p \in primes m].
Proof.
move=>n0 mn.
apply Order.POrderTheory.lt_sorted_eq.
- apply sorted_primes.
- apply sorted_filter.
   apply Order.POrderTheory.lt_trans.
apply sorted_primes.
- move=>p; rewrite mem_filter; apply/idP/idP => [/[dup] + -> /= | /andP[->//]].
rewrite 2!mem_primes => /andP[->/=]/andP[m0 pm].
by rewrite n0/=; apply (dvdn_trans pm).
Qed.

Lemma dvdn_leq_logP (m n : nat) :
  (0 < n)%N -> (0 < m)%N -> reflect (forall p, prime p -> logn p m <= logn p n)%N (m %| n)%N.
Proof.
move=>n0 m0; apply (iffP idP) => [mn p prim | vp_leq].
   by apply dvdn_leq_log.
apply/dvdnP; exists (\prod_(p <- primes n) p ^ (logn p n - logn p m))%N.
rewrite {1}(prod_prime_decomp n0) {2}(prod_prime_decomp m0) 2!prime_decompE 2!big_map/=.
have ->: primes m = [seq i <- primes n | i \in primes m].
   apply Order.POrderTheory.lt_sorted_eq.
   - apply sorted_primes.
   - apply sorted_filter.
      apply Order.POrderTheory.lt_trans.
   apply sorted_primes.
   - move=>p; rewrite mem_filter; apply/idP/idP => [/[dup] + -> /= | /andP[->//]].
     move=>/[dup]; rewrite {1}mem_primes => /andP[pprim _].
     rewrite -2!logn_gt0 => pm.
     apply (leq_trans pm (vp_leq p pprim)).
rewrite big_filter [in X in (_ * X)%N]big_mkcond/= -big_split/= 2!big_seq.
apply eq_bigr => p; rewrite mem_primes => /andP[pprim _].
have ->: ((if p \in primes m then p ^ logn p m else 1) = p ^ logn p m)%N.
   case/boolP: (p \in primes m) => //.
   by rewrite -logn_gt0 lt0n negbK => /eqP ->; rewrite expn0.
by rewrite -expnD subnK// vp_leq.
Qed.

Lemma muln_gt0 [I : Type] (r : seq I) (P : pred I) (F : I -> nat) (p : nat) :
  all (fun n : I => P n ==> (0 < F n)%N) r ->
  (0 < \prod_(n <- r | P n) F n)%N.
Proof.
elim: r => [|n r IHn /andP[Fn0 Fr0]]; first by rewrite big_nil.
rewrite big_cons; case /boolP: (P n) => Pn; last by apply IHn.
rewrite muln_gt0.
by move:Fn0; rewrite Pn/= IHn ?andbT.
Qed.

Lemma logn_prod [I : Type] (r : seq I) (P : pred I) (F : I -> nat) (p : nat) :
  all (fun n : I => P n ==> (0 < F n)%N) r ->
  (logn p (\prod_(n <- r | P n) F n) = \sum_(n <- r | P n) logn p (F n))%N.
Proof.
elim: r => [|n r IHn /andP[Fn0 Fr0]]; first by rewrite 2!big_nil logn1.
rewrite 2!big_cons; case /boolP: (P n) => Pn; last by apply IHn.
move:Fn0; rewrite Pn => /= Fn0.
by rewrite lognM// ?muln_gt0// IHn.
Qed.

Lemma logn_partn (p n : nat) (pi : nat_pred) :
  logn p (n`_pi)%N = ((p \in pi) * logn p n)%N.
Proof.
rewrite/partn logn_prod; last by apply/allP => i _; rewrite pfactor_gt0 implybT.
under eq_bigr do rewrite lognX.
have logp (i : nat): (i == p) || (logn i n * logn p i == 0)%N.
   case /boolP: (i == p) => //= /negPf ip.
   case /boolP: (prime i) => [|/negPf] iprim; last first.
      by rewrite/logn iprim mul0n.
   by rewrite (logn_prime _ iprim) [p == i]eq_sym ip muln0.
case /boolP: (p < n.+1)%N => [plt |]; last first.
   rewrite -leqNgt => np.
   suff ->: (\sum_(0 <= i < n.+1 | i \in pi) logn i n * logn p i = \sum_(0 <= i < n.+1 | i \in pi) 0)%N. 
      by rewrite big_const_seq iter_addn_0 mul0n ltn_log0// muln0.
   apply eq_bigr => i _.
   move: (logp i) => /orP [|]/eqP ->//.
   by rewrite ltn_log0// mul0n.
suff ->: (\sum_(0 <= i < n.+1 | i \in pi) logn i n * logn p i = \sum_(i < n.+1 | pred1 (Ordinal plt) i) (p \in pi) * logn i n)%N. 
   by rewrite (big_pred1 (Ordinal plt)).
rewrite big_mkord big_mkcond/= [in RHS]big_mkcond/=.
apply eq_bigr => i _.
have ->: (i == Ordinal plt = (val i == p)).
   by apply/eqP/eqP => [/(congr1 val)// | ] ip; apply val_inj.
move: (logp i); case /boolP: (val i == p)%N => /= [|_] /eqP ->.
   2: by case: (val i \in pi).
move=>_; case: (p \in pi); last by rewrite mul0n.
rewrite mul1n.
case /boolP: (prime p) => [| /negPf] pprim; last by rewrite/logn pprim.
by rewrite -{3}(expn1 p) pfactorK// muln1.
Qed.

End Temp.
