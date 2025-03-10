From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*********************)
(* package ssreflect *)
(*********************)

(***********)
(* ssrbool *)
(***********)

Lemma classicPT (P : Type) : classically P <-> ((P -> False) -> False).
Proof.
split; first by move=>/(_ false) PFF PF; suff: false by []; apply: PFF => /PF.
by move=> PFF []// Pf; suff: False by []; apply: PFF => /Pf.
Qed.

Lemma classic_sigW T (P : T -> Prop) :
  classically (exists x, P x) <-> classically (sig P).
Proof. by split; apply: classic_bind => -[x Px]; apply/classicW; exists x. Qed.

Lemma classic_ex T (P : T -> Prop) :
   ~ (forall x, ~ P x) -> classically (ex P).
Proof.
move=> NfNP; apply/classicPT => exPF; apply: NfNP => x Px.
by apply: exPF; exists x.
Qed.

(*********)
(* bigop *)
(*********)

Lemma big_rcons_idx (R : Type) (idx : R) (op : R -> R -> R) (I : Type)
    (i : I) (r : seq I) (P : pred I) (F : I -> R)
    (idx' := if P i then op (F i) idx else idx) :
  \big[op/idx]_(j <- rcons r i | P j) F j = \big[op/idx']_(j <- r | P j) F j.
Proof. by elim: r => /= [|j r]; rewrite ?(big_nil, big_cons)// => ->. Qed.

Lemma big_change_idx (R : Type) (idx : R) (op : Monoid.law idx) (I : Type)
    (x : R)  (r : seq I) (P : pred I) (F : I -> R) :
   op (\big[op/idx]_(j <- r | P j) F j) x = \big[op/x]_(j <- r | P j) F j.
Proof.
elim: r => [|i r]; rewrite ?(big_nil, big_cons, Monoid.mul1m)// => <-.
by case: ifP => // Pi; rewrite Monoid.mulmA.
Qed.
Lemma big_rcons (R : Type) (idx : R) (op : Monoid.law idx) (I : Type)
   i r (P : pred I) F :
  \big[op/idx]_(j <- rcons r i | P j) F j =
  op (\big[op/idx]_(j <- r | P j) F j) (if P i then F i else idx).
Proof. by rewrite big_rcons_idx -big_change_idx Monoid.mulm1. Qed.

(********)
(* path *)
(********)

Lemma sortedP T x (s : seq T) (r : rel T) :
  reflect (forall i, i.+1 < size s -> r (nth x s i) (nth x s i.+1)) (sorted r s).
Proof.
elim: s => [|y [|z s]//= IHs]/=; do ?by constructor.
apply: (iffP andP) => [[ryz rzs] [|i]// /IHs->//|rS].
by rewrite (rS 0); split=> //; apply/IHs => i /(rS i.+1).
Qed.

(*********)
(* tuple *)
(*********)

Section tnth_shift.
Context {T : Type} {n1 n2} (t1 : n1.-tuple T) (t2 : n2.-tuple T).

Lemma tnth_lshift i : tnth [tuple of t1 ++ t2] (lshift n2 i) = tnth t1 i.
Proof.
have x0 := tnth_default t1 i; rewrite !(tnth_nth x0).
by rewrite nth_cat size_tuple /= ltn_ord.
Qed.

Lemma tnth_rshift j : tnth [tuple of t1 ++ t2] (rshift n1 j) = tnth t2 j.
Proof.
have x0 := tnth_default t2 j; rewrite !(tnth_nth x0).
by rewrite nth_cat size_tuple ltnNge leq_addr /= addKn.
Qed.
End tnth_shift.

(*********)
(* prime *)
(*********)

Lemma primeNsig (n : nat) : ~~ prime n -> (2 <= n)%N ->
  { d : nat | (1 < d < n)%N & (d %| n)%N }.
Proof.
move=> primeN_n le2n; case/pdivP: {+}le2n => d /primeP[lt1d prime_d] dvd_dn.
exists d => //; rewrite lt1d /= ltn_neqAle dvdn_leq 1?andbT //; last first.
  by apply: (leq_trans _ le2n).
by apply: contra primeN_n => /eqP <-; apply/primeP.
Qed.

Lemma totient_gt1 n : (totient n > 1)%N = (n > 2)%N.
Proof.
case: n => [|[|[|[|n']]]]//=; set n := n'.+4; rewrite [RHS]isT.
have [pn2|/allPn[p]] := altP (@allP _ (eq_op^~ 2%N) (primes n)); last first.
  rewrite mem_primes/=; move: p => [|[|[|p']]]//; set p := p'.+3.
  move=> /andP[p_prime dvdkn].
  have [//|[|k]// cpk ->] := (@pfactor_coprime _ n p_prime).
  rewrite totient_coprime ?coprimeXr 1?coprime_sym//.
  rewrite totient_pfactor ?logn_gt0 ?mem_primes ?p_prime// mulnCA.
  by rewrite (@leq_trans p.-1) ?leq_pmulr ?muln_gt0 ?expn_gt0 ?totient_gt0.
have pnNnil : primes n != [::].
  apply: contraTneq isT => pn0.
  by have := @prod_prime_decomp n isT; rewrite prime_decompE pn0/= big_nil.
have := @prod_prime_decomp n isT; rewrite prime_decompE.
case: (primes n) pnNnil pn2 (primes_uniq n) => [|p [|p' r]]//=; last first.
  move=> _ eq2; rewrite !inE [p](eqP (eq2 _ _)) ?inE ?eqxx//.
  by rewrite [p'](eqP (eq2 _ _)) ?inE ?eqxx// orbT.
move=> _ /(_ _ (mem_head _ _))/eqP-> _; rewrite big_cons big_nil muln1/=.
case: (logn 2 n) => [|[|k]]// ->.
by rewrite totient_pfactor//= expnS mul1n leq_pmulr ?expn_gt0.
Qed.

(********************)
(* package fingroup *)
(********************)

(*************)
(* gproduct? *)
(*************)

Section ExternalNDirProd.

Variables (n : nat) (gT : 'I_n -> finGroupType).
Notation gTn := {dffun forall i, gT i}.

Definition extnprod_mulg (x y : gTn) : gTn := [ffun i => (x i * y i)%g].
Definition extnprod_invg (x : gTn) : gTn := [ffun i => (x i)^-1%g].

Lemma extnprod_mul1g : left_id [ffun=> 1%g] extnprod_mulg.
Proof. by move=> x; apply/ffunP => i; rewrite !ffunE mul1g. Qed.

Lemma extnprod_mulVg : left_inverse [ffun=> 1%g] extnprod_invg extnprod_mulg.
Proof. by move=> x; apply/ffunP => i; rewrite !ffunE mulVg. Qed.

Lemma extnprod_mulgA : associative extnprod_mulg.
Proof. by move=> x y z; apply/ffunP => i; rewrite !ffunE mulgA. Qed.

HB.instance Definition _ := isMulGroup.Build gTn
  extnprod_mulgA extnprod_mul1g extnprod_mulVg.

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

(********)
(* perm *)
(********)

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
have [<-|Nxz] := eqVneq x z; first by rewrite tpermC mem_gen ?imset_f.
by rewrite -(tpermJt Nxz Nyz) groupJ ?mem_gen ?imset_f.
Qed.

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

(*******************)
(* package algebra *)
(*******************)

Import GRing.Theory.
Local Open Scope ring_scope.
Notation has_char0 L := ([char L] =i pred0).

(**********)
(* ssralg *)
(**********)

Lemma iter_addr (V : zmodType) n x y : iter n (+%R x) y = x *+ n + y :> V.
Proof. by elim: n => [|n ih]; rewrite ?add0r //= ih mulrS addrA. Qed.

Lemma prodrMl {R : comRingType} {I : finType} (A : pred I) (x : R) F :
  \prod_(i in A) (x * F i) = x ^+ #|A| * \prod_(i in A) F i.
Proof.
rewrite -sum1_card; elim/big_rec3: _; first by rewrite expr0 mulr1.
by move=> i y p z iA ->; rewrite mulrACA exprS.
Qed.

Lemma expr_sum {R : ringType} {T : Type} (x : R) (F : T -> nat) P s :
  x ^+ (\sum_(i <- s | P i) F i) = \prod_(i <- s | P i) x ^+ (F i).
Proof. by apply: big_morph; [exact: exprD | exact: expr0]. Qed.

Lemma prim_root_natf_neq0 (F : fieldType) n (w : F) :
  n.-primitive_root w -> (n%:R != 0 :> F).
Proof.
have [->//|n_gt0] := posnP n => x_prim; apply/negPf/negP => nFneq0.
have /natf0_char[//|p char_p] := nFneq0.
have p_prime : prime p := charf_prime char_p.
move: nFneq0; rewrite -(dvdn_charf char_p) => dvdpn.
have [k cpk nE] := pfactor_coprime p_prime n_gt0.
have k_gt0 : (k > 0)%N by move: n_gt0; rewrite nE muln_gt0 => /andP[].
have /prim_expr_order/eqP := x_prim; rewrite nE exprM.
elim: (logn p n) => [|i IHi]; last first.
  rewrite expnSr exprM -subr_eq0 -Frobenius_autE -(Frobenius_aut1 char_p).
  by rewrite -rmorphB fmorph_eq0 subr_eq0.
rewrite -(prim_order_dvd x_prim) nE mulnC Gauss_dvd ?coprimeXl//.
rewrite pfactor_dvdn// ltn_geF// -[k]muln1 logn_Gauss ?logn1//.
by rewrite logn_gt0 mem_primes p_prime dvdpn n_gt0.
Qed.

(**********)
(* ssrnum *)
(**********)

Section ssrnum.
Import Num.Theory.

Lemma CrealJ (C : numClosedFieldType) :
  {mono (@Num.conj_op C) : x / x \is Num.real}.
Proof.
suff realK : {homo (@Num.conj_op C) : x / x \is Num.real}.
  by move=> x; apply/idP/idP => /realK//; rewrite conjCK.
by move=> x xreal; rewrite conj_Creal.
Qed.
End ssrnum.

(**********)
(* ssrint *)
(**********)

Lemma dvdz_charf (R : ringType) (p : nat) :
  p \in [char R] -> forall n : int, (p %| n)%Z = (n%:~R == 0 :> R).
Proof.
move=> charRp [] n; rewrite [LHS](dvdn_charf charRp)//.
by rewrite NegzE abszN rmorphN// oppr_eq0.
Qed.

(********)
(* poly *)
(********)

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

Lemma irredp_XaddC (F : fieldType) (x : F) : irreducible_poly ('X + x%:P).
Proof. by rewrite -[x]opprK rmorphN; apply: irredp_XsubC. Qed.

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

Lemma map_polyXsubC (aR rR : ringType) (f : {rmorphism aR -> rR}) x :
   map_poly f ('X - x%:P) = 'X - (f x)%:P.
Proof. by rewrite rmorphB/= map_polyX map_polyC. Qed.

Lemma poly_XsubC_over {R : ringType} c (S : subringClosed R) :
  c \in S -> 'X - c%:P \is a polyOver S.
Proof. by move=> cS; rewrite rpredB ?polyOverC ?polyOverX. Qed.

Lemma poly_XnsubC_over {R : ringType} n c (S : subringClosed R) :
  c \in S -> 'X^n - c%:P \is a polyOver S.
Proof. by move=> cS; rewrite rpredB ?rpredX ?polyOverX ?polyOverC. Qed.

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
by apply: (big_morph (fun p : {poly R} => p`_0));
   [apply: coef0M | rewrite coefC eqxx].
Qed.

Lemma map_prod_XsubC (aR rR : ringType) (f : {rmorphism aR -> rR}) rs :
  map_poly f (\prod_(x <- rs) ('X - x%:P)) =
  \prod_(x <- map f rs) ('X - x%:P).
Proof.
by rewrite rmorph_prod big_map; apply/eq_bigr => x /=; rewrite map_polyXsubC.
Qed.

Lemma eq_in_map_poly_id0 (aR rR : ringType) (f g : aR -> rR)
    (S : addrClosed aR) :
  f 0 = 0 -> g 0 = 0 ->
  {in S, f =1 g} -> {in polyOver S, map_poly f =1 map_poly g}.
Proof.
move=> f0 g0 eq_fg p pP; apply/polyP => i.
by rewrite !coef_map_id0// eq_fg// (polyOverP _).
Qed.

Lemma eq_in_map_poly (aR rR : ringType) (f g : {additive aR -> rR})
    (S : addrClosed aR) :
  {in S, f =1 g} -> {in polyOver S, map_poly f =1 map_poly g}.
Proof. by move=> /eq_in_map_poly_id0; apply; rewrite //?raddf0. Qed.

Lemma mapf_root (F : fieldType) (R : ringType) (f : {rmorphism F -> R})
    (p : {poly F}) (x : F) :
  root (p ^^ f) (f x) = root p x.
Proof. by rewrite !rootE horner_map fmorph_eq0. Qed.

Section multiplicity.
Variable (L : fieldType).

Definition mup (x : L) (p : {poly L}) :=
  [arg max_(n > (0 : 'I_(size p).+1) | ('X - x%:P) ^+ n %| p) n] : nat.

Lemma mup_geq x q n : q != 0 -> (n <= mup x q)%N = (('X - x%:P) ^+ n %| q).
Proof.
move=> q_neq0; rewrite /mup; symmetry.
case: arg_maxnP; rewrite ?expr0 ?dvd1p//= => i i_dvd gti.
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
by rewrite dvd1p dvdp_XsubCl /root !hornerE ?horner_exp ?hornerE expf_neq0// subr_eq0.
(* FIXME: remove ?horner_exp ?hornerE when requiring MC >= 1.16.0 *)
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

Lemma prod_XsubC_eq (s t : seq L) :
  \prod_(x <- s) ('X - x%:P) = \prod_(x <- t) ('X - x%:P) -> perm_eq s t.
Proof.
move=> eq_prod; apply/allP => x _ /=; apply/eqP.
by have /(congr1 (mup x)) := eq_prod; rewrite !mu_prod_XsubC.
Qed.

End multiplicity.

Lemma primitive_root_eq0 (F : fieldType) n (w : F) :
  n.-primitive_root w -> (w == 0) = (n == 0%N).
Proof.
move=> wp; apply/eqP/idP => [w0|/eqP p0]; move: wp; rewrite ?w0 ?p0; last first.
  by move=> /prim_order_gt0//.
move=> /prim_expr_order/esym/eqP.
by rewrite expr0n; case: (n =P 0%N); rewrite ?oner_eq0.
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
have [/eqP/size_poly1P[c cN0 ->]|gN1] := eqVneq (size g) 1%N.
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

(***********)
(* polydiv *)
(***********)

Lemma eqpW (R : idomainType) (p q : {poly R}) : p = q -> p %= q.
Proof. by move->; rewrite eqpxx. Qed.

Lemma horner_mod (R : fieldType) (p q : {poly R}) x : root q x ->
  (p %% q).[x] = p.[x].
Proof.
by move=> /eqP qx0; rewrite [p in RHS](divp_eq p q) !hornerE qx0 mulr0 add0r.
Qed.

Lemma root_dvdp (F : idomainType) (p q : {poly F}) (x : F) :
  root p x -> p %| q -> root q x.
Proof. rewrite -!dvdp_XsubCl; exact: dvdp_trans. Qed.

(**********)
(* vector *)
(**********)

Lemma SubvsE (F0 : fieldType) (L : vectType F0) (k : {vspace L}) x (xk : x \in k) :
  Subvs xk = vsproj k x.
Proof. by apply/val_inj; rewrite /= vsprojK. Qed.

(*****************)
(* package field *)
(*****************)

(************)
(* falgebra *)
(************)

Lemma adjoin_cat (K : fieldType) (aT : falgType K) (V : {vspace aT})
    (rs1 rs2 : seq aT) :
  <<V & rs1 ++ rs2>>%VS = <<<<V & rs1>> & rs2>>%VS.
Proof.
elim: rs1 => /= [|r rs1 ih] in V *.
- by rewrite adjoin_nil agenv_add_id.
- by rewrite !adjoin_cons ih.
Qed.

Lemma eq_adjoin (K : fieldType) (aT : falgType K) (U : {vspace aT})
    (rs1 rs2 : seq aT) : rs1 =i rs2 ->
  <<U & rs1>>%VS = <<U & rs2>>%VS.
Proof.
by move=> rs12; apply/eqP; rewrite eqEsubv !adjoin_seqSr// => x; rewrite rs12.
Qed.

Lemma memv_mulP (K : fieldType) (aT : falgType K) (U V : {vspace aT}) w :
  reflect (exists n (us vs : n.-tuple aT),
             [/\ all (mem U) us, all (mem V) vs &
                 w = \sum_(i < n) tnth us i * tnth vs i])
          (w \in (U * V)%VS).
Proof.
apply: (iffP idP) => [|[b [us [vs [usU vsV ->]]]]]; last first.
  by rewrite rpred_sum// => i _; rewrite memv_mul//; apply/all_tnthP.
rewrite unlock span_def big_tuple => /memv_sumP[/= w_ w_mem ->].
have wP_ i : exists2 uv, (uv.1 \in U) && (uv.2 \in V) & w_ i = uv.1 * uv.2.
  have /vlineP[k ->] := w_mem i isT; set UV := (X in tnth X _).
  have /allpairsP[[u v] [uP vP ->]] := mem_tnth i UV.
  by exists (k *: u, v); rewrite /= ?rpredZ ?vbasis_mem// scalerAl.
pose d := (\dim U * \dim V)%N; pose uv i := (projT1 (sig2_eqW (wP_ i))).
exists d, [tuple (uv i).1 | i < _], [tuple (uv i).2 | i < _]; rewrite /uv.
split; do ?by apply/allP => _/mapP[i _ ->]; case: sig2_eqW => /= ? /andP[].
by apply: eq_bigr => i; rewrite !tnth_map/= tnth_ord_tuple; case: sig2_eqW.
Qed.

Lemma big_prodv_seqP (I : eqType) (r : seq I)  (P : {pred I})
  (K : fieldType) (aT : falgType K) (U : {vspace aT})
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
apply: (iffP idP) => [+ u v uU vV|WP]; rewrite !big_rcons_idx.
  by move=> /IHr; apply => //; case: ifP => Pi//; rewrite memv_mul// vV.
case: ifP => Pi; last first.
  by apply/IHr => // u v uU vV; have := WP _  _ uU vV; rewrite big_rcons_idx Pi.
apply/IHr => //w v /memv_mulP[n [vs [us [/allP/= vsP /allP/= usP ->]]]] vV.
rewrite -big_change_idx/= mulr_sumr rpred_sum// => j _; rewrite big_change_idx.
have := WP (tnth us j) (fun k : I => if k == i then tnth vs j else v k).
rewrite big_rcons_idx Pi eqxx big_seq_cond.
under eq_bigr => k /andP[kr]
   do [rewrite ifN; last by apply: contraNneq iNr => <-].
rewrite -big_seq_cond; apply; first by rewrite usP ?mem_tnth.
by move=> k Pk; case: eqP => [->|]; rewrite ?vV ?vsP ?mem_tnth.
Qed.

(************)
(* fieldext *)
(************)

Lemma dim_aimg (F : fieldType) (L L' : fieldExtType F) (iota : 'AHom(L, L'))
  (E : {subfield L}) : \dim (iota @: E) = \dim E.
Proof.
suff /size_basis -> : basis_of (iota @: E) (map iota (vbasis E)) by [].
by rewrite limg_basis_of// ?vbasisP// ?(eqP (AHom_lker0 _)) capv0.
Qed.

Lemma Fadjoin_seq_idP (F0 : fieldType) (L : fieldExtType F0) (K : {subfield L})
    (xs : seq L) :
  reflect (<<K & xs>>%VS = K) (all (mem K) xs).
Proof.
apply: (iffP idP) => [|<-]; last by apply/allP => x ?; apply: seqv_sub_adjoin.
elim: xs => /= [|x xs ih]; first by  rewrite Fadjoin_nil.
by case/andP=> xK {}/ih ih; rewrite adjoin_cons (Fadjoin_idP _).
Qed.
Arguments Fadjoin_seq_idP {F0 L K xs}.


Lemma big_prod_subfield_seqP (I : eqType) (r : seq I) (r_uniq : uniq r)
    (P : {pred I}) (K : fieldType) (aT : fieldExtType K)
    (U : I -> {vspace aT}) (W : {subfield aT}) :
  reflect (forall u : I -> aT, (forall i, P i -> u i \in U i) ->
                               \prod_(i <- r | P i) u i \in W)
          (\big[@prodv _ _/1%VS]_(i <- r | P i) U i <= W)%VS.
Proof.
apply: (iffP (big_prodv_seqP _ _ _ _ _)) => // [WP u uU|WP u v uU vV].
  by apply: WP; rewrite ?mem1v.
by rewrite -big_change_idx/= memvM ?WP//; apply/subvP: uU; rewrite sub1v.
Qed.

Lemma big_prod_subfieldP (I : finType) (D : {pred I}) (K : fieldType)
    (aT : fieldExtType K) (U : I -> {vspace aT}) (W : {subfield aT}) :
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

Section canonicals.
Variables  (F0 : fieldType) (L : fieldExtType F0).
Lemma vsproj_is_multiplicative : multiplicative (vsproj {:L}).
by split => [v w|]; apply/val_inj; rewrite /= !vsprojK ?memvf ?algid1.
Qed.
HB.instance Definition _ :=
  GRing.isMultiplicative.Build L (subvs_of {:L}) (vsproj {:L})
    vsproj_is_multiplicative.

Definition vssub (k K : {vspace L}) of (k <= K)%VS :
  subvs_of k -> subvs_of K := vsproj _ \o vsval.

Variables (k K : {subfield L}) (kK : (k <= K)%VS).

Lemma vssub_is_multiplicative : multiplicative (vssub kK).
split => [v w|]; apply/val_inj => /=; last first.
  by rewrite vsprojK ?algid1 ?rmorph1 ?rpred1//.
by rewrite /= !vsprojK/= ?rpredM//= (subvP kK _ (subvsP _)) .
Qed.
HB.instance Definition _ := GRing.Linear.on (vssub kK).
HB.instance Definition _ :=
  GRing.isMultiplicative.Build (subvs_of k) (subvs_of K) (vssub kK)
    vssub_is_multiplicative.

Lemma vsval_sub (v : subvs_of k) : vsval (vssub kK v) = vsval v.
Proof. by rewrite vsprojK// (subvP kK)// subvsP. Qed.

End canonicals.

Lemma splitting_ahom (F0 : fieldType) (L L' : fieldExtType F0)
    (p : {poly F0}) (E' : {subfield L'}) :
    splittingFieldFor 1 (p ^^ in_alg L) fullv ->
    splittingFieldFor 1 (p ^^ in_alg L') E' ->
  {iota : 'AHom(L, L') | limg iota = E'}.
Proof.
do [suff init (p : {poly L}) (k : {subfield L})
    (K := subvs_of k : falgType F0) (f : 'AHom(K, L')) :
    p \is a polyOver k ->  splittingFieldFor k p fullv ->
    splittingFieldFor (limg f) (p ^^ (f \o vsproj k)) E' ->
      {g : 'AHom(L, L') | limg g = E'}] in p *.
  move=> pf pE'; pose K : falgType F0 := subvs_of (1%VS : {vspace L}).
  have [idF0 idF0E] : {f : 'AHom(K, L') | forall x : F0, f x%:A = x%:A}.
    pose f (v : K) := in_alg L' (projT1 (sig_eqW (vlineP _ _ (valP v)))).
    have fa : additive f.
      move=> ? ?; rewrite /f.
      case: sig_eqW => x; case: sig_eqW => /= v->; case: sig_eqW => /= w->.
      by rewrite -!in_algE -raddfB => /fmorph_inj<-//; rewrite raddfB.
    have fm : multiplicative f.
      split=> [? ?|]; rewrite /f.
      - case: sig_eqW => x; case: sig_eqW => /= v->; case: sig_eqW => /= w->.
        by rewrite -!in_algE -rmorphM => /fmorph_inj<-//; rewrite rmorphM.
      - case: sig_eqW => /= one /esym/eqP; rewrite algid1.
        by rewrite -[X in X == _]in_algE fmorph_eq1 => /eqP->; rewrite scale1r.
    have fl : scalable f.
      move=> a ? /=; rewrite /f.
      case: sig_eqW => x; case: sig_eqW => /= v->.
      rewrite -[_ *: _]mulr_algl -in_algE -rmorphM => /fmorph_inj<-.
      by rewrite -in_algE rmorphM mulr_algl.
    pose faM := GRing.isAdditive.Build _ _ _ fa.
    pose fmM := GRing.isMultiplicative.Build _ _ _ fm.
    pose flM := GRing.isScalable.Build _ _ _ _ _ fl.
    pose fLRM : {lrmorphism _ -> _} := HB.pack f faM fmM flM.
    exists (linfun_ahom fLRM) => v; rewrite lfunE/= /f.
    case: sig_eqW => /= x.
    by rewrite algid1 -[in X in X -> _]in_algE => /fmorph_inj->.
  apply: (init (p ^^ in_alg L) 1%AS idF0) => //.
    by apply/polyOver1P; exists p.
  suff -> : limg idF0 = 1%VS.
    rewrite -!map_poly_comp/= (@eq_map_poly _ _ _ (in_alg L'))//.
    move=> v /=; rewrite -[RHS]idF0E; congr (idF0 _).
    by apply/val_inj; rewrite /= algid1 vsprojK ?rpredZ ?rpred1//.
  apply/eqP; rewrite eqEsubv sub1v andbT; apply/subvP => _/memv_imgP[v _ ->].
  suff [u ->] : exists u : F0, v = in_alg K u.
      by rewrite idF0E; apply/vlineP; exists u.
  case: v => u u1; rewrite SubvsE; move: u1 => /vlineP[{}u ->]; exists u.
  by apply/val_inj; rewrite /= vsprojK ?algid1// rpredZ ?rpred1.
move=> /polyOver_subvs/sig_eqW[/= {}p ->]; rewrite map_poly_comp/=.
rewrite -(map_poly_comp _ vsval) (eq_map_poly vsvalK) map_poly_id//.
move=> /sig2_eqW[rs prs rsf] /sig2_eqW [rs' prs' <-]{E'}; apply/sig_eqW.
elim: rs => [|x rs IHrs]//= in k @K f p rs' prs rsf prs' *.
  rewrite ?Fadjoin_nil ?big_nil/= in rsf prs.
  move=> /(@val_inj _ _ _ k) in rsf; rewrite {k}rsf in K f p prs prs' *.
  have: p %= 1 by rewrite -(eqp_map vsval) rmorph1.
  rewrite -(eqp_map f) rmorph1 (eqp_ltrans prs')//.
  move=> /eqp_size; rewrite size_prod_XsubC size_poly1 => -[].
  case: {+}rs' => // _; rewrite Fadjoin_nil/=.
  exists (linfun_ahom (f \o vsproj _)).
  apply/vspaceP => v; apply/memv_imgP/memv_imgP => -[u _ ->]/=.
    by exists (vsproj fullv u); rewrite ?memvf//= lfunE/=.
  by exists (val u); rewrite ?memvf//= lfunE/= ?vsvalK.
have [xk|xNk] := boolP (x \in k).
  do [rewrite -[x]/(val (Subvs xk)); move: (Subvs xk) => {xk}x] in prs rsf.
  rewrite adjoin_cons (Fadjoin_idP _) ?subvsP//= in rsf.
  have xrs' : f x \in rs'.
    rewrite -root_prod_XsubC -(eqp_root prs') mapf_root.
    rewrite -(mapf_root vsval) (eqp_root prs).
    by rewrite root_prod_XsubC mem_head.
  have -> : <<limg f & rs'>>%VS = <<limg f & rem (f x) rs'>>%VS.
    rewrite (eq_adjoin _ (perm_mem (perm_to_rem xrs'))).
    by rewrite adjoin_cons (Fadjoin_idP _)//= memv_img ?memvf.
  apply: (IHrs k f (p %/ ('X - x%:P))) => //.
    rewrite map_divp/= (eqp_trans (eqp_divl _ prs))//.
    by rewrite map_polyXsubC/= big_cons mulKp ?polyXsubC_eq0// eqpxx.
  rewrite map_divp/= (eqp_trans (eqp_divl _ prs'))// (big_rem _ xrs').
  by rewrite map_polyXsubC/= mulKp ?polyXsubC_eq0// eqpxx.
have /polyOver_subvs[q eq_q] := minPolyOver k x.
have rpx : root (p ^^ vsval) x.
  by rewrite (eqp_root prs) root_prod_XsubC mem_head.
pose psize := [fun p : {poly _} => size p].
have q_monic : q \is monic.
  by have /(congr1 (mem monic))/= := eq_q; rewrite map_monic monic_minPoly.
have size_q : (size q > 1)%N.
  have /(congr1 (psize _))/= := eq_q; rewrite size_minPoly size_map_poly => <-.
  by rewrite ltnS adjoin_degreeE divn_gt0 ?adim_gt0 ?dimvS ?subv_adjoin.
have [x' x'rs qx'0] : exists2 x', x' \in rs' & root (q ^^ f) x'.
  have : q ^^ vsval %| p ^^ vsval.
    by rewrite -eq_q minPoly_dvdp//; apply/polyOver_subvs; exists p.
  rewrite dvdp_map -(dvdp_map f) (eqp_dvdr _ prs').
  move=> /dvdp_prod_XsubC[m]; rewrite eqp_monic ?map_monic ?monic_prod_XsubC//.
  move=> /eqP; case rs'_eq : mask => [|x' rs'x].
    move=> /(congr1 (psize _))/=.
    by rewrite big_nil size_map_poly size_poly1 => /eqP; rewrite gtn_eqF.
  rewrite big_cons => q_eq; exists x'.
    by rewrite (@mem_mask _ _ m)// rs'_eq mem_head.
  by rewrite q_eq rootE !hornerE subrr mul0r.
have rpx' : root (p ^^ f) x' by rewrite (eqp_root prs') root_prod_XsubC.
pose Kx : fieldExtType F0 := subvs_of <<k; x>>.
pose mpsI := map_inj_poly subvs_inj (rmorph0 _).
pose x0 := Subvs (memv_adjoin k x).
pose KKx :=  vssub (subv_adjoin k x).
have KxE : forall (v : Kx), exists p, v = (p ^^ KKx).[x0].
  move=> [u ukx]; have /Fadjoin_polyP[_ /polyOver_subvs[p' -> ueq]] := ukx.
  exists p'; apply/val_inj; rewrite /= -horner_map/=.
  by rewrite -map_poly_comp (eq_map_poly (vsval_sub (subv_adjoin _ _))).
suff [h hx0 hC] : {h : 'AHom(Kx, L') | h x0 = x' & h \o KKx =1 f}.
  have imgfx' : <<limg f; x'>>%VS = limg h.
    apply/vspaceP => v; apply/idP/idP => [/Fadjoin_polyP|/memv_imgP] [u uP ->].
      rewrite rpred_horner//=; last by rewrite -hx0 ?memv_img ?memvf.
      by apply/polyOverS: uP => _/memv_imgP[a _ ->]; rewrite -hC memv_img ?memvf.
    have [{uP}u->] := KxE u; rewrite -horner_map -map_poly_comp (eq_map_poly hC).
    rewrite rpred_horner//= ?hx0 ?memv_adjoin//; apply/polyOverP => i.
    by rewrite coef_map/= (subvP (subv_adjoin _ _))// memv_img ?memvf.
  rewrite (eq_adjoin _ (perm_mem (perm_to_rem x'rs))) adjoin_cons imgfx'.
  apply: (IHrs <<k; x>>%AS h (p ^^ vssub (subv_adjoin k x) %/ ('X - x0%:P))).
  - rewrite map_divp -map_poly_comp (eq_map_poly (vsval_sub _)).
    rewrite map_polyXsubC/= (eqp_trans (eqp_divl _ prs))// big_cons.
    by rewrite mulKp ?polyXsubC_eq0// eqpxx.
  - by rewrite -adjoin_cons.
  rewrite map_divp -map_poly_comp map_polyXsubC/= hx0 (eq_map_poly hC).
  rewrite (eqp_trans (eqp_divl _ prs'))// (big_rem _ x'rs)/=.
  by rewrite mulKp ?polyXsubC_eq0// eqpxx.
have /(_ _)/polyOver_subvs/sig_eqW/=-/all_sig[pol polE] := Fadjoin_polyOver k x.
have polB (v w : L) : pol (v - w) = pol v - pol w.
  by apply: mpsI; rewrite raddfB/= -!polE raddfB.
have polZ (c : F0) (v : L) : pol (c *: v) = c%:A *: pol v.
  by apply: mpsI; rewrite linearZ/= -!polE linearZ/= algid1.
have polC (c : K) : pol (val c) = c%:P.
  by apply: mpsI; rewrite -polE/= Fadjoin_polyC ?subvsP// map_polyC.
have pol1 : pol 1 = 1 by rewrite -[RHS]polC/= algid1.
have polX : pol x = 'X by apply: mpsI; rewrite map_polyX -polE Fadjoin_polyX.
have polM (v w : Kx) : pol (val v * val w) = pol (val v) * pol (val w) %% q.
  apply: mpsI; rewrite map_modp rmorphM/= -!polE/= -eq_q.
  apply: Fadjoin_poly_unique.
  - by rewrite modp_polyOver// ?minPolyOver// rpredM ?Fadjoin_polyOver.
  - by rewrite -ltnS -size_minPoly ltn_modp ?monic_neq0 ?monic_minPoly//.
  rewrite -Fadjoin_poly_mod ?rpredM ?Fadjoin_polyOver//.
  by rewrite hornerM !Fadjoin_poly_eq//= ?rpredM ?subvsP.
pose h (v : Kx) := (pol (val v) ^^ f).[x'].
have ha : additive h.
  by move=> v w; rewrite /h/= -raddfB/= polB raddfB !hornerE.
have hm : multiplicative h.
  split=> [v w|].
  - by rewrite /h /= -rmorphM/= polM map_modp/= horner_mod// rmorphM hornerE.
  - by rewrite /h /= algid1 pol1 rmorph1 hornerE.
have hl : scalable h.
  by move=> ? ?; rewrite /h /= polZ linearZ/= rmorph_alg hornerE mulr_algl.
pose haM := GRing.isAdditive.Build _ _ _ ha.
pose hmM := GRing.isMultiplicative.Build _ _ _ hm.
pose hlM := GRing.isScalable.Build _ _ _ _ _ hl.
pose hLRM : {lrmorphism _ -> _} := HB.pack h haM hmM hlM.
exists (linfun_ahom hLRM); first by rewrite lfunE/= /h polX map_polyX hornerX.
by move=> v; rewrite /comp lfunE/= /h/= vsval_sub/= polC map_polyC hornerC.
Qed.

Lemma lker0_img_cap (K : fieldType) (aT rT : vectType K) (f : 'Hom(aT, rT))
    (U V : {vspace aT}) : lker f == 0%VS ->
  (f @: (U :&: V) = f @: U :&: f @: V)%VS.
Proof.
move=> kf0; apply/eqP; rewrite eqEsubv limg_cap/=; apply/subvP => x.
rewrite memv_cap => /andP[/memv_imgP[u uU ->]] /memv_imgP[v vV].
by move=> /(lker0P kf0) eq_uv; rewrite memv_img// memv_cap uU eq_uv vV.
Qed.

Lemma aimg_cap (K : fieldType) (aT rT : fieldExtType K) (f : 'AHom(aT, rT))
    (U V : {vspace aT}) : (f @: (U :&: V) = f @: U :&: f @: V)%VS.
Proof. exact/lker0_img_cap/AHom_lker0. Qed.

Lemma sub_aimgP (F0 : fieldType) (L L' : splittingFieldType F0)
  (iota : 'AHom(L, L')) (F : {subfield L'}) :
  reflect (exists E : {subfield L}, (iota @: E)%VS = F) (F <= iota @: fullv)%VS.
Proof.
apply: (iffP idP) => [Fiota|[E <-]]; last by rewrite limgS ?subvf.
suff F_is_aspace : is_aspace (iota @^-1: F)%VS.
  by exists (ASpace F_is_aspace); apply/eqP; rewrite eqEsubv/= lpreimK ?subvv.
apply/andP => /=; split.
  by apply/has_algid1; rewrite -memv_preim rmorph1 rpred1.
by apply/prodvP => u v; rewrite -!memv_preim => uF vF; rewrite rmorphM rpredM.
Qed.

Lemma polyOver_aimg (K : fieldType) (L L' : fieldExtType K)
    (E : {vspace L}) (f : 'AHom(L, L')) (p' : {poly L'}) :
  reflect (exists2 p, p \is a polyOver E & p' = p ^^ f)
          (p' \is a polyOver (f @: E)%VS).
Proof.
apply: (iffP polyOverP) => [|[p pE -> i]]; last first.
  by rewrite coef_map memv_img ?(polyOverP pE).
move=> /(_ _)/memv_imgP/sig2_eqW-/all_sig[p_ pP].
exists (\poly_(i < size p') p_ i).
  apply/polyOverP => i; rewrite coef_poly; case: ifP => _; rewrite ?rpred0//.
  by case: (pP i).
apply/polyP => i; rewrite coef_map/= coef_poly.
by case: ltnP => ip'; [case: (pP i) | rewrite nth_default ?rmorph0].
Qed.
Arguments polyOver_aimg {K L L' E f p'}.

Lemma mapf_polyOver (K : fieldType) (L L' : fieldExtType K)
    (E : {vspace L}) (f : 'AHom(L, L')) (p : {poly L}) :
  (p ^^ f \is a polyOver (f @: E)%VS) = (p \is a polyOver E).
Proof.
apply/polyOverP/polyOverP => piE i; last by rewrite coef_map/= memv_img.
by have := piE i; rewrite coef_map/= memvE -limg_line limg_ker0 ?AHom_lker0.
Qed.

Lemma separable_aimg  (F0 : fieldType) (L L' : fieldExtType F0)
  (E F : {subfield L}) (f : 'AHom(L, L')) :
   separable (f @: E) (f @: F) = separable E F.
Proof.
apply/separableP/separableP => [sepEF x xF|sepEF _ /memv_imgP[x xF ->]].
  have /separable_elementP[_ [/polyOver_aimg[p pE ->]]] :=
    sepEF (f x) (memv_img f xF).
  rewrite mapf_root separable_map => root_p sep_p.
  by apply/separable_elementP; exists p; split.
have /(_ _ xF)/separable_elementP[p [pE rpx sepp]] := sepEF.
apply/separable_elementP; exists (p ^^ f).
by rewrite ?mapf_polyOver ?rmorph_root ?separable_map.
Qed.

Lemma subset_limgP (F0 : fieldType) (L L' : fieldExtType F0)
    (E : {subfield L}) (f : 'AHom(L, L')) (r' : seq L') :
  {subset r' <= (f @: E)%VS} <-> (exists2 r, all (mem E) r & r' = map f r).
Proof.
split => [|[r /allP/= rE ->] _ /mapP[x xr ->]]; last by rewrite memv_img ?rE.
move=> /(_ _ _)/memv_imgP/sig2_eqW-/(all_sig_cond (0 : L))[f' f'P].
exists (map f' r'); first by apply/allP => _ /mapP [x /f'P[? ?] ->].
by symmetry; rewrite -map_comp; apply: map_id_in => x /f'P[].
Qed.

Lemma splittingFieldFor_aimg  (F0 : fieldType) (L L' : fieldExtType F0)
  (E F : {subfield L}) p (f : 'AHom(L, L')) :
   splittingFieldFor (f @: E) (p ^^ f) (f @: F) <-> splittingFieldFor E p F.
Proof.
split=> -[rs' pE EF]; last first.
  by exists (map f rs'); rewrite -?map_prod_XsubC ?eqp_map -?aimg_adjoin_seq ?EF.
have /subset_limgP[rs _ rs'E] : {subset rs' <= (f @: F)%VS}.
  by rewrite -EF; apply: seqv_sub_adjoin.
exists rs; first by have := pE; rewrite rs'E -map_prod_XsubC ?eqp_map.
have := EF; rewrite rs'E -aimg_adjoin_seq => /eqP.
by rewrite eq_limg_ker0 ?AHom_lker0// => /eqP.
Qed.

(********************)
(* package solvable *)
(********************)

(*******************)
(* new sym library *)
(*******************)

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

(************)
(* solvable *)
(************)

Lemma sol_setXn n (gT : 'I_n -> finGroupType) (G : forall i, {group gT i}) :
  (forall i, solvable (G i)) -> solvable (setXn G).
Proof.
elim: n => [|n IHn] in gT G * => solG; first by rewrite setX0 solvable1.
pose gT' (i : 'I_n) := gT (lift ord0 i).
pose prod_group_gT := [the finGroupType of {dffun forall i, gT i}].
pose prod_group_gT' := [the finGroupType of {dffun forall i, gT' i}].
pose f (x : prod_group_gT) : prod_group_gT' := [ffun i => x (lift ord0 i)].
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
  pose w := [ffun i : 'I_n.+1 =>
             match unliftP ord0 i return (gT i) : Type with
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
pose k (x : gT ord0) : prod_group_gT :=
  [ffun i : 'I_n.+1 =>
     match (ord0 =P i) return (gT i) : Type with
     | ReflectT P => ecast i (gT i) P x
     | _ => 1%g
     end].
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

Section Perm_solvable.
Local Open Scope nat_scope.

Variable T : finType.

Lemma solvable_AltF : 4 < #|T| -> solvable 'Alt_T = false.
Proof.
move=> card_T; apply/negP => Alt_solvable.
have/simple_Alt5 Alt_simple := card_T.
have := simple_sol_prime Alt_solvable Alt_simple.
have lt_T n : n <= 4 -> n < #|T| by move/leq_ltn_trans; apply.
have -> : #|('Alt_T)%G| = #|T|`! %/ 2 by rewrite -card_Alt ?mulKn ?lt_T.
move/even_prime => [/eqP|]; apply/negP.
  rewrite neq_ltn leq_divRL // mulnC -[2 * 3]/(3`!).
  by apply/orP; right; apply/ltnW/ltn_fact/lt_T.
by rewrite -dvdn2 dvdn_divRL dvdn_fact //=; apply/ltnW/lt_T.
Qed.

Lemma solvable_SymF : 4 < #|T| -> solvable 'Sym_T = false.
Proof. by rewrite (series_sol (Alt_normal T)) => /solvable_AltF->. Qed.

End Perm_solvable.
