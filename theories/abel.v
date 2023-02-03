From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field polyrcf.
From Abel Require Import various classic_ext map_gal algR.
From Abel Require Import char0 cyclotomic_ext real_closed_ext.

(*****************************************************************************)
(* We work inside a enclosing splittingFieldType L over a base field F0      *)
(*                                                                           *)
(*     radical U x n := x is a radical element of degree n over U            *)
(*    pradical U x p := x is a radical element of prime degree p over U      *)
(*   r.-tower U e pw := e is a chain of elements of L such that              *)
(*                      forall i, r <<U & take i e>> e`_i pw`_i              *)
(*        r.-ext U V := there exists e and pw such that <<U & e>> = V        *)
(*                      and r.-tower U e p  w.                               *)
(* solvable_by r E F := there is a field K, such that F <= K and r.-ext E K  *)
(*                      if p has roots rs, solvable_by radicals E <<E, rs>>  *)
(* solvable_ext_poly p := the Galois group of p is solvable in any splitting *)
(*                      field L for p. (i.e. p has roots rs in a splitting   *)
(*                      then, 'Gal(<<1 & rs>>/1) is solbable.                *)
(*                      This is equivalent to general classical existence    *)
(*                      or constructive existence over rat, of a splitting   *)
(*                      field for p, in which its  Galois group is solvable  *)
(* solvable_by_radical_poly p := solvable_by radical 1 <<1; rs>> in L        *)
(*                      L being any splitting field L where p has roots rs   *)
(*                      and which contains a n nth primitive root of unity,  *)
(*                      (we me make n explicit in ext_solvable_by_radical)   *)
(*                      This is equivalent to general classical existence    *)
(*                      or constructive existence over rat, of a splitting   *)
(*                      field for p, in which the roots of p are rs, and in  *)
(*                      which solvable_by radical 1 <<1; rs>> in L.          *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").
Local Notation "2" := 2%:R : ring_scope.
Local Notation "3" := 3%:R : ring_scope.
Local Notation "4" := 4%:R : ring_scope.
Local Notation "5" := 5%:R : ring_scope.

CoInductive unsplit_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | UnsplitLo (j : 'I_m) of i = lshift _ j : unsplit_spec i (inl _ j) true
  | UnsplitHi (k : 'I_n) of i = rshift _ k : unsplit_spec i (inr _ k) false.

Lemma unsplitP m n (i : 'I_(m + n)) : unsplit_spec i (split i) (i < m)%N.
Proof. by case: splitP=> j eq_j; constructor; apply/val_inj. Qed.

Section RadicalExtension.

Variables (F0 : fieldType) (L : splittingFieldType F0).

Section Defs.

Implicit Types (U V : {vspace L}).

Definition radical U x n := [||
  [&& n%:R != 0 :> F0 & x ^+ n \in U] |
  [&& n \in [char L] & x ^+ n - x \in U]].
Definition pradical U x p := [||
  [&& prime p, p%:R != 0 :> F0 & x ^+ p \in U] |
  [&& p \in [char L] & x ^+ p - x \in U]].

Lemma radicalP U x n : reflect  [\/
  [/\ n%:R != 0 :> F0 & x ^+ n \in U] |
  [/\ n \in [char L] & x ^+ n - x \in U]]
                                (radical U x n).
Proof. by apply(iffP orP); (case=>/andP h; [ left | right ]). Qed.

Lemma pradicalP U x p : reflect  [\/
  [/\ prime p, p%:R != 0 :> F0 & x ^+ p \in U] |
  [/\ p \in [char L] & x ^+ p - x \in U]]
                                (pradical U x p).
Proof.
by apply(iffP orP); (case=> h; [ left; apply/and3P | right; apply/andP ]).
Qed.

Implicit Types r : {vspace L} -> L -> nat -> bool.

Definition tower r n U (e : n.-tuple L) (pw : n.-tuple nat) :=
  [forall i : 'I_n, r << U & take i e >>%VS (tnth e i) (tnth pw i)].

Lemma towerP r n U (e : n.-tuple L) (pw : n.-tuple nat) :
  reflect (forall i : 'I_n, r << U & take i e >>%VS (tnth e i) (tnth pw i))
          (tower r U e pw).
Proof. exact/forallP. Qed.

Local Notation "r .-tower" := (@tower r _)
  (at level 2, format "r .-tower") : ring_scope.

Record ext_data := ExtData { ext_size : nat;
                             ext_ep : ext_size.-tuple L;
                             ext_pw : ext_size.-tuple nat }.
Arguments ExtData [ext_size].

Definition trivExt := ExtData [tuple] [tuple].

Definition extension_of r U V :=
  exists2 e : ext_data,
    r.-tower U (ext_ep e) (ext_pw e)
    & << U & ext_ep e >>%VS = V.

Local Notation "r .-ext" := (extension_of r)
  (at level 2, format "r .-ext") : ring_scope.

Definition solvable_by r (U V : {vspace L}) :=
  exists2 E : {subfield L}, r.-ext U E & (V <= E)%VS.

End Defs.

Local Notation "r .-tower" := (@tower r _)
  (at level 2, format "r .-tower") : ring_scope.
Local Notation "r .-ext" := (extension_of r)
  (at level 2, format "r .-ext") : ring_scope.

Section Properties.

Implicit Types r : {vspace L} -> L -> nat -> bool.
Implicit Types (U V : {subfield L}).

(* TODO: rename and move to the proper place *)
Lemma prim_root_natf_neq0 (w : L) (n : nat) :
  n.-primitive_root w -> n%:R != (0 : F0).
Proof.
case: n => // n /andP[_ /forallP w1].
rewrite natf_neq0; apply/andP; split=>//.
rewrite -(negbK (all _ _)) -has_predC.
apply/negP => /hasP[p]; rewrite mem_primes => /and3P[p_prime _ /dvdnP][].
case=>// m nE.
rewrite /negn inE negbK => /andP [_ p0].
have: p \in [char L] by rewrite (char_lalg L) inE; apply/andP; split=>//.
move=> {p0} p_char.
move:(w1 (Ordinal (ltnSn n))) => /= /eqP.
rewrite eqxx /root_of_unity /root !hornerE ?hornerXn.
  (* FIXME: remove ?hornerXn when requiring MC >= 1.16.0 *)
rewrite nE exprM -(@expr1n _ p).
rewrite -(Frobenius_autE p_char (w ^+ m.+1)) -(Frobenius_autE p_char 1) subr_eq0=>/eqP/fmorph_inj wm1.
have mn: (m.+1 < n.+1)%N.
  by rewrite nE; apply ltn_Pmulr=>//; apply prime_gt1.
  have: ((Ordinal (ltn_trans (ltnSn m) mn)).+1).-unity_root w.
  by rewrite /root_of_unity /root/= !hornerE ?hornerXn wm1 subrr.
  (* FIXME: remove ?hornerXn when requiring MC >= 1.16.0 *)
move:(w1 (Ordinal (ltn_trans (ltnSn m) mn))) => /eqP -> /= /eqP mnE.
by move:mn; rewrite mnE ltnn.
Qed.

Lemma rext_refl r (E : {subfield L}) : r.-ext E E.
Proof. by exists trivExt; rewrite ?Fadjoin_nil//=; apply/towerP => -[]. Qed.

Lemma rext_r r n (U : {subfield L}) x : r U x n -> r.-ext U << U; x >>%VS.
Proof.
move=> rUxn; exists (ExtData [tuple x] [tuple n]); last by rewrite adjoin_seq1.
by apply/towerP => /= i; rewrite ord1/= !tnth0 Fadjoin_nil.
Qed.

Lemma rext_trans r (F E K : {subfield L}) :
  r.-ext E F -> r.-ext F K -> r.-ext E K.
Proof.
move=> [[/= n1 e1 pw1] Ee FE] [[/= n2 e2 pw2] Fe KE].
exists (ExtData [tuple of e1 ++ e2] [tuple of pw1 ++ pw2]) => /=; last first.
  by rewrite adjoin_cat FE.
apply/towerP => /= i; case: (unsplitP i) => [j eq_ij|k eq_i_n1Dk].
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
Proof. by case=> [[/= n e pw] _ <-]; apply: subv_adjoin_seq. Qed.

Lemma solvable_by_radicals_radicalext (E F : {subfield L}) :
  radical.-ext E F -> solvable_by radical E F.
Proof. by move=> extEF; exists F. Qed.

Lemma radical_Fadjoin1 (n : nat) (x : L) (E : {subfield L}) :
  n%:R != 0 :> F0 -> x ^+ n \in E -> radical E x n.
Proof. by move=> ? ?; apply/radicalP; left. Qed.

Lemma radical_Fadjoin2 (n : nat) (x : L) (E : {subfield L}) :
  n \in [char L] -> x ^+ n - x \in E -> radical E x n.
Proof. by move=> ? ?; apply/radicalP; right. Qed.

Lemma pradical_Fadjoin1 (n : nat) (x : L) (E : {subfield L}) :
  prime n -> n%:R != 0 :> F0 -> x ^+ n \in E -> pradical E x n.
Proof. by move=> ? ? ?; apply/pradicalP; left. Qed.

Lemma pradical_Fadjoin2 (n : nat) (x : L) (E : {subfield L}) :
  n \in [char L] -> x ^+ n - x \in E -> pradical E x n.
Proof. by move=> ? ?; apply/pradicalP; right. Qed.

Lemma radical_ext_Fadjoin1 (n : nat) (x : L) (E : {subfield L}) :
  n%:R != 0 :> F0 -> x ^+ n \in E -> radical.-ext E <<E; x>>%VS.
Proof.  move=> n_gt0 xnE; apply/rext_r/(radical_Fadjoin1 n_gt0 xnE). Qed.

Lemma radical_ext_Fadjoin2 (n : nat) (x : L) (E : {subfield L}) :
  n \in [char L] -> x ^+ n - x \in E-> radical.-ext E <<E; x>>%VS.
Proof. by move=> nL xnE; apply/rext_r/(radical_Fadjoin2 nL xnE). Qed.

Lemma pradical_ext_Fadjoin1 (n : nat) (x : L) (E : {subfield L}) :
  prime n -> n%:R != 0 :> F0 -> x ^+ n \in E -> pradical.-ext E <<E; x>>%VS.
Proof.
by move=> n_prime n0 xnE; apply/rext_r/(pradical_Fadjoin1 n_prime n0 xnE).
Qed.

Lemma pradical_ext_Fadjoin2 (n : nat) (x : L) (E : {subfield L}) :
  n \in [char L] -> x ^+ n - x \in E-> pradical.-ext E <<E; x>>%VS.
Proof. by move=> nL xnE; apply/rext_r/(pradical_Fadjoin2 nL xnE). Qed.

Lemma pradicalext_radical n (x : L) (E : {subfield L}) :
  radical E x n -> pradical.-ext E << E; x >>%VS.
Proof.
move=> /radicalP; case=>[[n_gt0] | [nL]] xnE; last first.
  by apply (pradical_ext_Fadjoin2 nL xnE).
have [k] := ubnP n.
elim: k => // k IHk in n x E n_gt0 xnE *; rewrite ltnS => lenk.
have [prime_n|primeN_n] := boolP (prime n).
  by apply: (@pradical_ext_Fadjoin1 n).
case/boolP: (2 <= n)%N; last first.
  case: n {lenk primeN_n} => [|[]]// in xnE n_gt0 * => _.
    by move:n_gt0; rewrite eqxx.
  suff ->:  <<E; x>>%VS = E by apply: rext_refl.
  by rewrite (Fadjoin_idP _).
move: primeN_n => /primePn[|[d /andP[d_gt1 d_ltn] dvd_dn n_gt1]].
  by case: ltngtP.
have [m n_eq_md]: {k : nat | n = (k * d)%N}.
  by exists (n %/ d)%N; rewrite [LHS](divn_eq _ d) (eqP dvd_dn) addn0.
have m_gt0 : m%:R != 0 :> F0.
  by move: n_gt0; rewrite n_eq_md natrM; apply: contra_neq => ->; rewrite mul0r.
apply: (@rext_trans _ <<E; x ^+ d>>) => //.
  apply: (@IHk m (x ^+ d)) => //.
    by rewrite -exprM mulnC -n_eq_md//.
  rewrite (leq_trans _ lenk)// n_eq_md ltn_Pmulr// lt0n.
  by move: m_gt0; apply: contra_neq => ->.
suff -> : <<E; x>>%AS = <<<<E; x ^+ d>>; x>>%AS.
  apply: (IHk d) => //.
  - by move: n_gt0; rewrite n_eq_md natrM; apply: contra_neq => ->;
      rewrite mulr0.
  - by rewrite memv_adjoin.
  - by rewrite (leq_trans _ lenk).
apply/val_inj; rewrite /= adjoinC [<<_; x ^+ d>>%VS](Fadjoin_idP _)//.
by rewrite rpredX// memv_adjoin.
Qed.

Lemma tower_sub r1 r2 n E (e : n.-tuple L) (pw : n.-tuple nat) :
  (forall U x n, r1 U x n -> r2 U x n) ->
    r1.-tower E e pw -> r2.-tower E e pw.
Proof. by move=> sub_r /forallP /= h; apply/forallP=> /= i; apply/sub_r/h. Qed.

Lemma radical_pradical U x p : pradical U x p -> radical U x p.
Proof.
move=>/pradicalP x_rad; apply/radicalP.
case:x_rad=>x_rad; last by right.
by case:x_rad=> prime_p xpU; left; split.
Qed.

Lemma radicalext_pradicalext (E F : {subfield L}) :
  pradical.-ext E F -> radical.-ext E F.
Proof.
case=> [[n e pw] Ee FE]; exists (ExtData e pw) => //.
by apply: (tower_sub radical_pradical).
Qed.

Lemma pradicalext_radicalext (E F : {subfield L}) :
  radical.-ext E F -> pradical.-ext E F.
Proof.
case=> [[/= n e pw]]; elim: n e pw E => [|n ih] e pw E Ee FE.
  by rewrite -FE tuple0 /= Fadjoin_nil; apply: rext_refl.
apply: (@rext_trans _ << E; tnth e 0 >>).
  apply: (@pradicalext_radical (tnth pw 0)).
  by move/forallP/(_ ord0): Ee; rewrite take0 Fadjoin_nil.
apply: (ih [tuple of behead e] [tuple of behead pw]) => /=; last first.
  by rewrite -adjoin_cons -drop1 (tnth_nth 0) -drop_nth 1?(drop0, size_tuple).
apply/forallP=> /= i; move/forallP/(_ (rshift 1 i)): Ee => /=.
rewrite !(tnth_nth 0, tnth_nth 0%N) !nth_behead [_ (rshift 1 i)]/=.
by rewrite -adjoin_cons takeD drop1 (take_nth 0) 1?size_tuple // take0.
Qed.

Lemma solvable_by_radical_pradical (E F : {subfield L}) :
  solvable_by pradical E F -> solvable_by radical E F.
Proof. by case=> [R /radicalext_pradicalext ERe FR]; exists R. Qed.

Lemma solvable_by_pradical_radical (E F : {subfield L}) :
  solvable_by radical E F -> solvable_by pradical E F.
Proof. by case=> [R /pradicalext_radicalext ERe FR]; exists R. Qed.

Lemma radicalext_Fadjoin_cyclotomic (E : {subfield L}) (w : L) (n : nat) :
  n.-primitive_root w -> radical.-ext E <<E; w>>%AS.
Proof.
move=> wprim; apply: (@radical_ext_Fadjoin1 n w E).
   exact: (prim_root_natf_neq0 wprim).
by rewrite (prim_expr_order wprim) mem1v.
Qed.

End Properties.
End RadicalExtension.

Arguments tower {F0 L}.
Arguments extension_of {F0 L}.
Arguments radical {F0 L}.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.
Local Notation "r .-ext" := (extension_of r)
  (at level 2, format "r .-ext") : ring_scope.

(* Following the french wikipedia proof :
https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_d%27Abel_(alg%C3%A8bre)#D%C3%A9monstration_du_th%C3%A9or%C3%A8me_de_Galois
*)

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
Variables (F0 : fieldType) (L : splittingFieldType F0).
Implicit Types (E F K : {subfield L}) (w : L) (n : nat).
Let radical := @radical F0 L.

Lemma cyclic_radical_ext w E F (n := \dim_E F) :
    n.-primitive_root w -> w \in E -> galois E F ->
  cyclic 'Gal(F / E) -> radical.-ext E F.
Proof.
set G := (X in cyclic X) => w_root wE galois_EF /cyclicP[g GE].
have EF := galois_subW galois_EF.
move: (prim_root_natf_neq0 w_root) => n_ne0.
have n_gt0: (0 < n)%N.
   by rewrite lt0n; move: n_ne0; apply: contra_neq => ->.
have Gg : generator G g by rewrite GE generator_cycle.
have gG : g \in G by rewrite GE cycle_id.
have HT90g := Hilbert's_theorem_90 Gg (subvP EF _ wE).
have /eqP/HT90g[x [xF xN0]] : galNorm E F w = 1.
  rewrite /galNorm; under eq_bigr => g' g'G. rewrite (fixed_gal EF g'G)//. over.
  by rewrite prodr_const -galois_dim// (prim_expr_order w_root).
have gxN0 : g x != 0 by rewrite fmorph_eq0.
have wN0 : w != 0. rewrite (primitive_root_eq0 w_root) -lt0n //.
move=> /(canLR (mulfVK gxN0))/(canRL (mulKf wN0)) gx.
have gXx i : (g ^+ i)%g x = w ^- i * x.
  elim: i =>  [|i IHi].
    by rewrite expg0 expr0 invr1 mul1r gal_id.
  rewrite expgSr exprSr invfM galM// IHi rmorphM/= gx mulrA.
  by rewrite (fixed_gal EF gG) ?rpredV ?rpredX.
have ExF : (<<E; x>> <= F)%VS by exact/FadjoinP.
suff -> : F = <<E; x>>%AS.
  apply: radical_ext_Fadjoin1 n_ne0 _.
  rewrite -(galois_fixedField galois_EF) -/G GE.
  apply/fixedFieldP; first by rewrite rpredX.
  move=> _ /cycleP[i ->]; rewrite rmorphX/= gXx exprMn exprVn exprAC.
  by rewrite (prim_expr_order w_root)// expr1n invr1 mul1r.
apply/val_inj/eqP => /=.
have -> : F = fixedField (1%g : {set gal_of F}) :> {vspace L}.
  by apply/esym/eqP; rewrite -galois_eq ?galvv ?galois_refl//.
rewrite -galois_eq; last by apply: galoisS galois_EF; rewrite subv_adjoin.
rewrite -subG1; apply/subsetP => g' g'G'.
have /cycleP[i g'E]: g' \in <[g]>%g.
  rewrite -GE gal_kHom//; apply/kAHomP => y yE.
  by rewrite (fixed_gal _ g'G') ?subvP_adjoin.
rewrite g'E in g'G' *.
have : (g ^+ i)%g x = x by rewrite (fixed_gal _ g'G') ?memv_adjoin.
rewrite gXx => /(canRL (mulfK xN0))/eqP; rewrite divff// invr_eq1.
rewrite -(prim_order_dvd w_root) => dvdni.
have /exponentP->// : (exponent G %| i)%N.
by rewrite GE exponent_cycle orderE -GE -galois_dim.
Qed.

Lemma solvableWradical_ext w E F (n := \dim_E F) :
    n.-primitive_root w -> w \in E -> galois E F ->
  solvable 'Gal(F / E) -> radical.-ext E F.
Proof.
move=> + + galEF; have [k] := ubnP n; elim: k => // k IHk in w E F n galEF *.
rewrite ltnS => le_nk; have subEF : (E <= F)%VS by case/andP: galEF.
move=> /[dup]/prim_root_natf_neq0 n_ne0.
have n_gt0: (0 < n)%N.
   by rewrite lt0n; move: n_ne0; apply: contra_neq => ->.
move=> wn Ew solEF; have [n_le1|n_gt1] := leqP n 1%N.
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
have Ewm : w ^+ (n %/ d) \in E by rewrite rpredX.
move=> /prime_cyclic/cyclic_radical_ext-/(_ _ _ Ewm galEH)/=.
rewrite dvdn_prim_root// => [/(_ isT)|]; last by rewrite n_eq dvdn_mull.
move=> /rext_trans; apply; apply: (IHk (w ^+ (n %/ p))) => /=.
- exact: fixedField_galois.
- rewrite (leq_trans _ le_nk)// -dim_fixedField /n galois_dim// proper_card//.
  by rewrite properEneq H_neq normal_sub.
- by rewrite dvdn_prim_root// n_eq dvdn_mulr.
- by rewrite rpredX//; apply: subvP Ew.
- by rewrite gal_fixedField (solvableS (normal_sub Hnormal)).
Qed.

Lemma galois_solvable_by_radical w E F (n := \dim_E F) :
    n.-primitive_root w -> galois E F ->
  solvable 'Gal(F / E) -> solvable_by radical E F.
Proof.
move=> w_root galEF solEF; have [EF Ew] := (galois_subW galEF, subv_adjoin E w).
exists (F * <<E; w>>)%AS; last by rewrite field_subvMr.
apply: rext_trans (radicalext_Fadjoin_cyclotomic _ w_root) _.
have galEwFEw: galois <<E; w>> (F * <<E; w>>) by apply: galois_prodvr galEF.
pose m := \dim_<<E; w>> (F * <<E; w>>); pose w' := w ^+ (n %/ m).
have w'Ew : w' \in <<E; w>>%VS by rewrite rpredX ?memv_adjoin.
have w'prim : m.-primitive_root w'.
  rewrite dvdn_prim_root // /m /n !galois_dim//.
  by rewrite (card_isog (galois_isog galEF _)) ?cardSg ?galS ?subv_cap ?EF//.
apply: (@solvableWradical_ext w'); rewrite // (isog_sol (galois_isog galEF _))//.
by rewrite (solvableS _ solEF) ?galS// subv_cap EF.
Qed.

(* Main lemma of part 1 *)
Lemma ext_solvable_by_radical w E F (n := \dim_E (normalClosure E F)) :
  n.-primitive_root w -> solvable_ext E F -> solvable_by radical E F.
Proof.
move=> wprim /andP[sepEF]; have galEF := normalClosure_galois sepEF.
move=> /(galois_solvable_by_radical wprim galEF) [M EM EFM]; exists M => //.
by rewrite (subv_trans _ EFM) ?normalClosureSr.
Qed.

End Part1.

(******************************************************************************)
(*                                                                            *)
(* Part 2 : solvable_by_radicals -> solvable                                  *)
(*                                                                            *)
(******************************************************************************)

Section RadicalRoots.
Variables (F : fieldType) (n : nat) (x w : F).
Hypothesis w_root : (n.-primitive_root w)%R.
Notation ws := [seq x * w ^+ val i | i : 'I_n].

Lemma uniq_roots_Xn_sub_xn : x != 0 -> uniq ws.
Proof using w_root.
move=> xN0; rewrite /image_mem (map_comp (fun i => x * w ^+ i)) val_enum_ord.
apply/(uniqP 0) => i j; rewrite !inE size_map size_iota/= => ip jp.
rewrite !(nth_map 0%N) ?size_iota// ?nth_iota// => /(mulfI xN0).
by move/eqP; rewrite (eq_prim_root_expr w_root) !modn_small// => /eqP.
Qed.

Lemma Xn_sub_xnE : (n > 0)%N ->
 'X^n - (x ^+ n)%:P = \prod_(i < n) ('X - (x * w ^+ i)%:P).
Proof using w_root.
move=> n_gt0; have [->|xN0] := eqVneq x 0.
  under eq_bigr do rewrite mul0r subr0.
  by rewrite expr0n gtn_eqF// subr0 prodr_const card_ord.
rewrite [LHS](@all_roots_prod_XsubC _ _ ws).
- by rewrite (monicP _) ?monic_XnsubC// scale1r big_map big_enum.
- by rewrite size_XnsubC// size_map size_enum_ord.
- rewrite all_map; apply/allP => i _ /=; rewrite /root !hornerE ?hornerXn.
  (* FIXME: remove ?hornerXn when requiring MC >= 1.16.0 *)
  by rewrite exprMn exprAC [w ^+ _]prim_expr_order// expr1n mulr1 subrr.
- by rewrite uniq_rootsE uniq_roots_Xn_sub_xn.
Qed.

End RadicalRoots.

Section galois_pradical.
Variables (p : nat) (F0 : fieldType) (L : splittingFieldType F0).
Variables (w : L) (x : L).
Hypothesis w_root : (p.-primitive_root w)%R.
Implicit Types (E : {subfield L}).

Lemma dvdp_minpoly_Xn_subn E :
  (x ^+ p)%R \in E -> minPoly E x %| ('X^p - (x ^+ p)%:P).
Proof using.
move=> xpE; have [->|p_gt0] := posnP p; first by rewrite !expr0 subrr dvdp0.
by rewrite minPoly_dvdp /root ?poly_XnsubC_over// !hornerE ?hornerXn subrr.
(* FIXME: remove ?hornerXn when requiring MC >= 1.16.0 *)
Qed.

Lemma galois_cyclo_radical E : (p > 0)%N -> x ^+ p \in E ->
   galois E <<<<E; w>>; x>>.
Proof.
move=> p_gt0 xpE; have [xE|xNE] := boolP (x \in E).
  rewrite (Fadjoin_idP _) ?(galois_Fadjoin_cyclotomic _ w_root)//.
  by rewrite (subvP (subv_adjoin _ _)).
have [x0|xN0] := eqVneq x 0; first by rewrite x0 rpred0 in xNE.
have [pB1_eq0|pB1_gt0] := posnP p.-1.
  by case: {+}p p_gt0 pB1_eq0 xpE xNE => [|[]]//=; rewrite expr1 => _ _ ->.
apply/splitting_galoisField; exists ('X^p - (x ^+ p)%:P)%R.
split; first by rewrite rpredB ?rpredX ?polyOverX ?polyOverC//.
  rewrite (Xn_sub_xnE _ w_root)// -(big_map _ predT (fun x => 'X - x%:P)).
  rewrite separable_prod_XsubC -[index_enum _]enumT.
  by rewrite (uniq_roots_Xn_sub_xn w_root).
exists [seq x * w ^+ val i | i : 'I_p].
  by rewrite (Xn_sub_xnE _ w_root)// big_map big_enum//= eqpxx.
apply/eqP; rewrite /image_mem (map_comp (fun i => x * w ^+ i)) val_enum_ord.
rewrite -[p]prednK//= mulr1 -[p.-1]prednK//= expr1 !adjoin_cons.
have -> : <<<<E; x>>; x * w>>%VS = <<<<E; w>>; x>>%VS.
  apply/eqP; rewrite [X in _ == X]adjoinC eqEsubv/= !Fadjoin_sub//.
    by rewrite -(@fpredMl _ _ _ _ x)// ?memv_adjoin//= adjoinC memv_adjoin.
  by rewrite rpredM// ?memv_adjoin//= adjoinC memv_adjoin.
rewrite (Fadjoin_seq_idP _)// all_map; apply/allP => i _/=.
by rewrite rpredM ?rpredX//= ?memv_adjoin// adjoinC memv_adjoin.
Qed.

Lemma galois_radical E : w \in E -> (p > 0)%N -> x ^+ p \in E ->
  galois E <<E; x>>.
Proof. by move=> + pp /(galois_cyclo_radical pp) => /(@Fadjoin_idP _)->. Qed.

Variable (E : {subfield L}).
Hypothesis p_prime : prime p.
Hypothesis wE : w \in E.
Hypothesis xNE : x \notin E.
Hypothesis xpE : x ^+ p \in E.
Let p_gt0 := prime_gt0 p_prime.

Lemma minPoly_pradical :  minPoly E x = 'X^p - (x ^+ p)%:P.
Proof using w_root p_prime wE xNE xpE p_gt0.
have xN0 : x != 0 by apply: contraNneq xNE => ->; rewrite rpred0.
have := dvdp_minpoly_Xn_subn xpE; rewrite (Xn_sub_xnE _ w_root)// -big_enum/=.
move=> /dvdp_prod_XsubC[m]; rewrite eqp_monic ?monic_minPoly//; last first.
  by rewrite monic_prod// => i _; rewrite monic_XsubC.
have [{}m sm ->] := resize_mask m (enum 'I_p); set s := mask _ _ => /eqP mEx.
have [|smp_gt0] := posnP (size s).
  case: s mEx => // /(congr1 (horner^~x))/esym/eqP.
  by rewrite minPolyxx big_nil hornerC oner_eq0.
suff leq_pm : (p <= size s)%N.
  move: mEx; suff /eqP->: s == enum 'I_p by [].
  by rewrite -(geq_leqif (size_subseq_leqif _)) ?mask_subseq// size_enum_ord.
have xXE (i : nat) : x ^+ i \in E -> (p %| i)%N.
  move=> xiE; apply: contraNT xNE; rewrite -prime_coprime// => /coprimeP[]// u.
  have [/eqP->//|uip] := leqP (u.1 * p)%N (u.2 * i)%N; rewrite -[x]expr1 => <-.
  by rewrite expfB// rpredM ?rpredV// mulnC exprM rpredX.
have /polyOverP/(_ 0%N) := minPolyOver E x; rewrite {}mEx coef0_prod.
under eq_bigr do rewrite coefB coefX coefC add0r -mulrN/=.
have w_neq0 : w != 0 by rewrite (primitive_root_eq0 w_root) -lt0n.
rewrite big_split/= fpredMr; last first.
- by rewrite prodf_seq_eq0; apply/hasPn => i _/=; rewrite oppr_eq0 expf_neq0.
- by rewrite rpred_prod// => i _/=; rewrite rpredN rpredX.
by rewrite big_tnth prodr_const cardT/= size_enum_ord => /xXE; apply: dvdn_leq.
Qed.

Lemma size_minPoly_pradical: size (minPoly E x) = p.+1.
Proof. by rewrite minPoly_pradical ?size_XnsubC. Qed.

Local Notation G := 'Gal(<<E; x>> / E)%g.

(* - Gal(E(x) / E) has order n *)
Lemma order_galois_pradical : #|G| = p.
Proof.
rewrite -galois_dim 1?galois_radical// -adjoin_degreeE.
by have := size_minPoly E x; rewrite size_minPoly_pradical// => -[].
Qed.

Lemma pradical_cyclic : cyclic G.
Proof. by apply/prime_cyclic; rewrite order_galois_pradical. Qed.

Lemma pradical_abelian : abelian G.
Proof. exact/cyclic_abelian/pradical_cyclic. Qed.

Lemma pradical_solvable : solvable G.
Proof. by rewrite abelian_sol ?pradical_abelian/= ?subvv. Qed.

End galois_pradical.

Lemma pradical_solvable_ext (p : nat)
   (F0 : fieldType) (L : splittingFieldType F0)
   (E : {subfield L}) (x : L) : prime p ->
   p%:R != 0 :> F0 -> x ^+ p \in E -> solvable_ext E <<E; x>>.
Proof.
move=> p_prime p_neq0 xpE; have p_gt0 := prime_gt0 p_prime.
wlog [w w_root] : L E x xpE / {w : L | p.-primitive_root w} => [hwlog|].
  apply: (@classic_cycloSplitting _ L p p_neq0) => -[L' [w [f wf rw]]].
  rewrite -(solvable_ext_aimg f) aimg_adjoin hwlog -?rmorphX ?memv_img//.
  by exists w.
have galEw := galois_Fadjoin_cyclotomic E w_root.
have solEw := solvable_Fadjoin_cyclotomic E w_root.
have [xEw|xNEw] := boolP (x \in <<E; w>>%VS).
  by apply/solvable_extP; exists <<E; w>>%AS; rewrite galEw solEw Fadjoin_sub.
have xpEw : x ^+ p \in <<E; w>>%VS by rewrite (subvP (subv_adjoin _ _)).
have galEwx : galois E <<<<E; w>>; x>> by rewrite (@galois_cyclo_radical p).
apply/solvable_extP; exists <<<<E; x>>; w>>%AS; rewrite subv_adjoin/= adjoinC.
rewrite galEwx (@series_sol _ _ ('Gal(<<<<E; w>>; x>> / <<E; w>>)));
  last by rewrite normalField_normal ?subv_adjoin ?galois_normalW.
rewrite (@pradical_solvable p _ _ w)// ?memv_adjoin//.
by rewrite (isog_sol (normalField_isog _ _ _)) ?galois_normalW ?subv_adjoin.
Qed.

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

Lemma ArtinSchreier_solvable_ext :
  x \notin E -> solvable_ext E <<E; x>>.
Proof.
move=> xE.
apply/solvable_extP; exists <<E; x>>%AS; rewrite subvv/=.
rewrite ArtinSchreier_galois/=.
apply/abelian_sol/cyclic_abelian/prime_cyclic.
rewrite -(galois_dim ArtinSchreier_galois) -adjoin_degreeE.
rewrite (pred_Sn (adjoin_degree E x)) -size_minPoly minPoly_ArtinSchreier//.
by rewrite -addrA -opprD size_addl size_polyXn// size_opp size_XaddC ltnS.
Qed.

End ArtinSchreier.

Lemma radical_ext_solvable_ext (F0 : fieldType) (L : splittingFieldType F0)
    (E F : {subfield L}) : (E <= F)%VS ->
  solvable_by radical E F -> solvable_ext E F.
Proof.
move=> EF.
move=> [_ /pradicalext_radicalext[[/= n e pw] /towerP epwP <- FK]].
pose k := n; suff {FK} : solvable_ext E <<E & take k e>>.
  by rewrite take_oversize ?size_tuple//; apply: sub_solvable_ext.
elim: k => /= [|k IHsol]; first by rewrite take0 Fadjoin_nil.
have [kn|nk] := ltnP k n; last first.
  by move: IHsol; rewrite !take_oversize ?size_tuple// leqW.
rewrite (take_nth 0) ?size_tuple// adjoin_rcons.
apply: solvable_ext_trans IHsol _.
  by rewrite /= subv_adjoin_seq subv_adjoin.
have := epwP (Ordinal kn); rewrite (tnth_nth 0) (tnth_nth 0%N)/=.
move=> /pradicalP; case=>[[pwk_prime] | [pwkL]] epwEk.
  by apply: (pradical_solvable_ext pwk_prime).
case /boolP: (e`_k \in <<E & take k e>>%VS).
  move=> /Fadjoin_idP ->; exact: solvable_ext_refl.
by apply (ArtinSchreier_solvable_ext pwkL).
Qed.

(******************************************************************************)
(*                                                                            *)
(* Abel/Galois Theorem                                                        *)
(*                                                                            *)
(******************************************************************************)

(** Ok **)
Lemma AbelGalois  (F0 : fieldType) (L : splittingFieldType F0) (w : L)
  (E F : {subfield L}) : (E <= F)%VS ->
  (\dim_E (normalClosure E F)).-primitive_root w ->
  solvable_by radical E F <-> solvable_ext E F.
Proof.
move=> EF wprim; split; first exact: radical_ext_solvable_ext.
exact: (ext_solvable_by_radical wprim).
Qed.

End Abel.

Definition solvable_by_radical_poly (F : fieldType) (p : {poly F}) :=
  forall (L : splittingFieldType F) (rs : seq L),
    p ^^ in_alg L %= \prod_(x <- rs) ('X - x%:P) ->
    forall w : L, (\dim <<1 & rs>>%VS).-primitive_root w ->
    solvable_by radical 1 <<1 & rs>>.

Definition solvable_ext_poly (F : fieldType) (p : {poly F}) :=
  forall (L : splittingFieldType F) (rs : seq L),
    p ^^ in_alg L %= \prod_(x <- rs) ('X - x%:P) ->
    solvable 'Gal(<<1 & rs>> / 1).

Lemma galois_solvable (F0 : fieldType) (L : splittingFieldType F0)
      (E F : {subfield L}) :
  galois E F -> solvable_ext E F = solvable 'Gal(F / E).
Proof.
by move=> /and3P[EF sEF nEF]; rewrite /solvable_ext sEF normalClosure_id.
Qed.

Lemma normal_solvable  (F0 : fieldType) (L : splittingFieldType F0)
      (E F : {subfield L}) : has_char0 L ->
  (E <= F)%VS -> normalField E F -> solvable_ext E F = solvable 'Gal(F / E).
Proof. by move=> charL EF /(char0_galois charL EF)/galois_solvable. Qed.

Lemma AbelGaloisPoly (F : fieldType) (p : {poly F}) : has_char0 F ->
  solvable_ext_poly p <-> solvable_by_radical_poly p.
Proof.
move=> charF; split=> + L rs pE => [/(_ L rs pE) + w w_prim|solrs]/=.
  have charL : has_char0 L by move=> i; rewrite char_lalg.
  have normal_rs : normalField 1 <<1 & rs>>.
    apply/splitting_normalField; rewrite ?sub1v//.
    by exists (p ^^ in_alg _); [apply/polyOver1P; exists p | exists rs].
  by move=> solrs; apply/(@AbelGalois _ _ w);
     rewrite ?char0_solvable_extE ?normalClosure_id ?sub1v ?dimv1 ?divn1.
have charL : has_char0 L by move=> i; rewrite char_lalg.
have seprs: separable 1 <<1 & rs>> by apply/char0_separable.
have normal_rs : normalField 1 <<1 & rs>>.
  apply/splitting_normalField; rewrite ?sub1v//.
  by exists (p ^^ in_alg _); [apply/polyOver1P; exists p | exists rs].
pose n := \dim <<1 & rs>>.
have nFN0 : n%:R != 0 :> F by have /charf0P-> := charF; rewrite -lt0n adim_gt0.
apply: (@classic_cycloSplitting _ L _ nFN0) => - [L' [w [iota wL' w_prim]]].
suff: solvable_ext 1 <<1 & rs>>.
  by rewrite /solvable_ext seprs normalClosure_id ?sub1v.
rewrite -(solvable_ext_aimg iota).
have charL' : [char L'] =i pred0 by move=> i; rewrite char_lalg.
apply/(@AbelGalois _ _ w) => //.
- by rewrite limgS// sub1v.
- rewrite -aimg_normalClosure //= aimg1 dimv1 divn1 dim_aimg/=.
  by rewrite normalClosure_id ?dimv1 ?divn1 ?sub1v//.
have /= := solrs L' (map iota rs) _ w.
rewrite -(aimg1 iota) -!aimg_adjoin_seq dim_aimg.
apply => //; have := pE; rewrite -(eqp_map [rmorphism of iota]).
by rewrite -map_poly_comp/= (eq_map_poly (rmorph_alg _)) map_prod_XsubC.
Qed.

Lemma solvable_ext_polyP (F : fieldType) (p : {poly F}) : p != 0 ->
    has_char0 F ->
  solvable_ext_poly p <->
  classically (exists (L : splittingFieldType F) (rs : seq L),
                p ^^ in_alg L %= \prod_(x <- rs) ('X - x%:P) /\
                solvable 'Gal(<<1 & rs>> / 1)).
Proof.
move=> p_neq0 charF; split => sol_p.
have FoE (v : F^o) : v = in_alg F^o v by rewrite /= /(_%:A)/= mulr1.
apply: classic_bind (@classic_fieldExtFor _ _ (p : {poly F^o}) p_neq0).
  move=> [L [rs [iota rsf p_eq]]]; apply/classicW.
  have iotaF : iota =1 in_alg L by move=> v; rewrite [v in LHS]FoE rmorph_alg.
  have splitL : SplittingField.axiom L.
    exists (p ^^ iota).
      by apply/polyOver1P; exists p; apply: eq_map_poly.
    exists rs => //; suff <- : limg iota = 1%VS by [].
    apply/eqP; rewrite eqEsubv sub1v andbT; apply/subvP => v.
    by move=> /memv_imgP[u _ ->]; rewrite iotaF/= rpredZ// rpred1.
  pose S := SplittingFieldType F L splitL.
  exists S, rs; split => //=; first by rewrite -(eq_map_poly iotaF).
  by apply: (sol_p S rs); rewrite -(eq_map_poly iotaF).
move=> L rs prs; apply: sol_p => -[M [rs' [prs']]].
have charL : has_char0 L by move=> n; rewrite char_lalg charF.
have charM : has_char0 M by move=> n; rewrite char_lalg charF.
pose K := [fieldExtType F of subvs_of <<1 & rs>>%VS].
pose rsK := map (vsproj <<1 & rs>>%VS) rs.
have pKrs : p ^^ in_alg K %= \prod_(x <- rsK) ('X - x%:P).
  rewrite -(eqp_map [rmorphism of vsval])/= map_prod_XsubC/= -map_poly_comp/=.
  rewrite -map_comp (@eq_map_poly _ _ _ (in_alg L)); last first.
    by move=> v; rewrite /= algid1.
  have /eq_in_map-> : {in rs, cancel (vsproj <<1 & rs>>%VS) vsval}.
    by move=> x xrs; rewrite vsprojK// seqv_sub_adjoin.
  by rewrite big_map.
have splitK : splittingFieldFor 1 (p ^^ in_alg K) fullv.
  exists rsK => //; apply/eqP; rewrite eqEsubv subvf/=.
  rewrite -(@limg_ker0 _ _ _ (linfun vsval)) ?AHom_lker0//.
  rewrite aimg_adjoin_seq/= aimg1 -map_comp/=.
  have /eq_in_map-> : {in rs, cancel (vsproj <<1 & rs>>%VS) (linfun vsval)}.
    by move=> x xrs; rewrite lfunE/= vsprojK// seqv_sub_adjoin.
  rewrite map_id; apply/subvP => _/memv_imgP[v _ ->].
  by rewrite lfunE subvsP.
have sfK : SplittingField.axiom K.
  by exists (p ^^ in_alg K) => //; apply/polyOver1P; exists p.
pose S := SplittingFieldType F K sfK.
have splitS : splittingFieldFor 1 (p ^^ in_alg S) fullv by [].
have splitM : splittingFieldFor 1 (p ^^ in_alg M) <<1 & rs'>> by exists rs'.
have splitL : splittingFieldFor 1 (p ^^ in_alg L) <<1 & rs>> by exists rs.
have [f imgf] := splitting_ahom splitS splitM.
have [g imgg] := splitting_ahom splitS splitL.
rewrite -imgf -(aimg1 f)/= -img_map_gal injm_sol ?map_gal_inj ?subsetT//.
by rewrite -imgg -(aimg1 g)/= -img_map_gal injm_sol ?map_gal_inj ?subsetT//.
Qed.

Lemma solvable_by_radical_polyP (F : fieldType) (p : {poly F}) : p != 0 ->
    has_char0 F ->
  solvable_by_radical_poly p <->
  classically (exists (L : splittingFieldType F) (rs : seq L),
                p ^^ in_alg L %= \prod_(x <- rs) ('X - x%:P) /\
                solvable_by radical 1 <<1 & rs>>).
Proof.
move=> p_neq0 charF0;
split => sol_p; last first.
  apply/AbelGaloisPoly => //; apply/solvable_ext_polyP => //.
  apply: classic_bind sol_p => -[L [rs [prs sol_p]]]; apply/classicW.
  exists L, rs; split => //; rewrite -galois_solvable.
    apply: radical_ext_solvable_ext; rewrite ?sub1v// => v.
  have charL : has_char0 L by move=> n; rewrite char_lalg charF0.
  rewrite char0_galois// ?sub1v//.
  apply/splitting_normalField; rewrite ?sub1v//.
  by exists (p ^^ in_alg _); [apply/polyOver1P; exists p | exists rs].
have FoE (v : F^o) : v = in_alg F^o v by rewrite /= /(_%:A)/= mulr1.
apply: classic_bind (@classic_fieldExtFor _ _ (p : {poly F^o}) p_neq0).
move=> [L [rs [f rsf p_eq]]].
have fF : f =1 in_alg L by move=> v; rewrite [v in LHS]FoE rmorph_alg.
have splitL : SplittingField.axiom L.
  exists (p ^^ f); first by apply/polyOver1P; exists p; apply: eq_map_poly.
  exists rs => //; suff <- : limg f = 1%VS by [].
  apply/eqP; rewrite eqEsubv sub1v andbT; apply/subvP => v.
  by move=> /memv_imgP[u _ ->]; rewrite fF/= rpredZ// rpred1.
pose S := SplittingFieldType F L splitL.
pose d := \dim  <<1 & (rs : seq S)>>.
have /classic_cycloSplitting-/(_ S) : d%:R != 0 :> F.
  by have /charf0P-> := charF0; rewrite -lt0n adim_gt0.
apply/classic_bind => -[C [w [g wg w_prim]]]; apply/classicW.
have gf : g \o f =1 in_alg C by move=> v /=; rewrite fF rmorph_alg.
have pgrs : p ^^ in_alg C %= \prod_(x <- [seq g i | i <- rs]) ('X - x%:P).
  by rewrite -(eq_map_poly gf) map_poly_comp/= -map_prod_XsubC eqp_map//.
exists C, (map g rs); split => //=; apply: (sol_p C (map g rs) _ w) => //.
by rewrite -(aimg1 g) -aimg_adjoin_seq dim_aimg.
Qed.

Import GRing.Theory Order.Theory Num.Theory.

Lemma solvable_poly_rat (p : {poly rat}) : p != 0 ->
  solvable_by_radical_poly p ->
  {L : splittingFieldType rat & {iota : {rmorphism L -> algC} & { rs : seq L |
   p ^^ in_alg L %= \prod_(x <- rs) ('X - x%:P) /\
   solvable_by radical 1 <<1 & rs>>}}}.
Proof.
move=> p_neq0 p_sol.
have [/= rsalg pE] := closed_field_poly_normal (p ^^ (ratr : _ -> algC)).
have {}pE : p ^^ ratr %= \prod_(z <- rsalg) ('X - z%:P).
  rewrite pE (eqp_trans (eqp_scale _ _)) ?eqpxx//.
  by rewrite lead_coef_map//= fmorph_eq0 lead_coef_eq0.
have [L [iota [rs iota_rs rsf]]] := num_field_exists rsalg.
have prs : p ^^ in_alg L %= \prod_(z <- rs) ('X - z%:P).
  rewrite -(eqp_map iota) map_prod_XsubC iota_rs -map_poly_comp.
  by rewrite (eq_map_poly (fmorph_eq_rat _)).
have splitL : SplittingField.axiom L.
  by exists (p ^^ in_alg L); [by apply/polyOver1P; exists p | exists rs].
pose S := SplittingFieldType rat L splitL.
pose d := \dim <<1 & (rs : seq S)>>.
have d_gt0 : (d > 0)%N by rewrite adim_gt0.
have [ralg ralg_prim] := C_prim_root_exists d_gt0.
have [L' [iota' [[]//= w rs' [iotaw iota_rs' wrsf]]]] :=
  num_field_exists (ralg :: rsalg).
have prs' : p ^^ in_alg L' %= \prod_(z <- rs') ('X - z%:P).
  rewrite -(eqp_map iota') map_prod_XsubC iota_rs' -map_poly_comp.
  by rewrite (eq_map_poly (fmorph_eq_rat _)).
have w_prim : d.-primitive_root w.
  by move: ralg_prim; rewrite -iotaw fmorph_primitive_root.
have splitL' : SplittingField.axiom L'.
  exists (cyclotomic w d * p ^^ in_alg L').
    by rewrite rpredM ?cyclotomic_over//; apply/polyOver1P; exists p.
  have [us cycloE usw] := splitting_Fadjoin_cyclotomic 1%AS w_prim.
  exists (us ++ rs'); last by rewrite adjoin_cat usw -adjoin_cons.
  by rewrite big_cat/= (eqp_trans (eqp_mulr _ cycloE))// eqp_mull//.
pose S' := SplittingFieldType rat L' splitL'.
have splitS : splittingFieldFor 1 (p ^^ in_alg S) fullv by exists rs.
have splitS' : splittingFieldFor 1 (p ^^ in_alg S') <<1 & rs'>> by exists rs'.
have [f /= imgf] := splitting_ahom splitS splitS'.
exists S', iota', rs'; split => //.
by apply: (p_sol S' rs' prs' w); rewrite -imgf dim_aimg/= -rsf.
Qed.

Lemma splitting_num_field (p : {poly rat}) :
  {L : splittingFieldType rat & { LtoC : {rmorphism L -> algC} |
    (p != 0 -> splittingFieldFor 1 (p ^^ in_alg L) {:L})
    /\ (p = 0 -> L = [splittingFieldType rat of rat^o]) }}.
Proof.
have [->|p_neq0] := eqVneq p 0.
  by exists [splittingFieldType rat of rat^o], [rmorphism of ratr]; split.
have [/= rsalg pE] := closed_field_poly_normal (p ^^ (ratr : _ -> algC)).
have {}pE : p ^^ ratr %= \prod_(z <- rsalg) ('X - z%:P).
  by rewrite pE (eqp_trans (eqp_scale _ _)) ?eqpxx// lead_coef_eq0 map_poly_eq0.
have [L' [L'toC [rs' rs'E rs'f]]] := num_field_exists rsalg.
have splitL' : splittingFieldFor 1 (p ^^ in_alg L') {: L'}%AS.
  exists rs' => //; rewrite -(eqp_map L'toC).
  by rewrite -map_poly_comp map_prod_XsubC rs'E (eq_map_poly (fmorph_eq_rat _)).
have splitaxL' : SplittingField.axiom L'.
  by exists (p ^^ in_alg L'); first by apply/polyOver1P; exists p.
exists (SplittingFieldType rat L' splitaxL'), L'toC; split => //.
by move=> p_eq0; rewrite p_eq0 eqxx in p_neq0.
Qed.

Lemma solvable_poly_ratP (p : {poly rat}) : p != 0 ->
  solvable_by_radical_poly p <->
  exists L : splittingFieldType rat, exists2 K : {subfield L},
    splittingFieldFor 1 (p ^^ in_alg L) K & solvable_by radical 1 K.
Proof.
move=> p_neq0; split.
  move=> /(solvable_poly_rat p_neq0)[L [_ [rs [prs rssol]]]].
  by exists L, <<1 & rs>>%AS; first by exists rs.
have charrat : [char rat] =i pred0 by exact: char_num.
move=> [L [K [rs prs <-] solK]]; apply/solvable_by_radical_polyP => //.
by apply/classicW; exists L, rs.
Qed.

Definition numfield (p : {poly rat}) : splittingFieldType rat :=
  projT1 (splitting_num_field p).

Lemma numfield0 : numfield 0 = [splittingFieldType rat of rat^o].
Proof. by rewrite /numfield; case: splitting_num_field => //= ? [? [_ ->]]. Qed.

Definition numfield_inC (p : {poly rat}) :
    {rmorphism numfield p -> algC} :=
  projT1 (projT2 (splitting_num_field p)).

Lemma numfieldP (p : {poly rat}) : p != 0 ->
  splittingFieldFor 1 (p ^^ in_alg (numfield p)) fullv.
Proof. by rewrite /numfield; case: splitting_num_field => //= ? [? []]. Qed.

Lemma char_numfield (p : {poly rat}) : [char (numfield p)] =i pred0.
Proof. exact: char_ext. Qed.
#[global] Hint Resolve char_numfield : core.

Lemma normal_numfield (p : {poly rat}) : normalField 1 {: numfield p}.
Proof.
have [{p}->|p_neq0] := eqVneq p 0.
  by rewrite numfield0 regular_fullv normalField_refl.
apply/splitting_normalField; rewrite ?sub1v//.
exists (p ^^ in_alg _); last exact: numfieldP.
by apply/polyOver1P; exists p.
Qed.

Lemma galois_numfield (p : {poly rat}) : galois 1 {: numfield p}.
Proof.
by apply/char0_galois; [exact/char_ext|rewrite sub1v|exact: normal_numfield].
Qed.

Theorem AbelGaloisPolyRat (p : {poly rat}) :
  reflect (solvable_by_radical_poly p) (solvable 'Gal({: numfield p} / 1)).
Proof.
have [{p}->|p_neq0] := eqVneq p 0.
  rewrite numfield0 regular_fullv galvv solvable1; constructor.
  move=> L rs; rewrite eqp_sym rmorph0 eqp0 prodf_seq_eq0.
  by move=> /hasP[x _ /=]; rewrite polyXsubC_eq0.
have charrat : [char rat] =i pred0 by exact: char_num.
pose charnumfield := char_ext (numfield p).
apply: (equivP idP); rewrite -AbelGaloisPoly//.
have [rs prs <-] := numfieldP p_neq0.
split; last by move=> /(_ (numfield p) rs prs).
move=> solp; apply/solvable_ext_polyP => //.
by apply/classicW; exists (numfield p); exists rs; split.
Qed.

Definition numfield_roots (p : {poly rat}) :=
  if (p != 0) =P true isn't ReflectT p_neq0 then [::]
  else projT1 (sig2_eqW (numfieldP p_neq0)).

Lemma poly_numfield_eqp (p : {poly rat}) : p != 0 ->
  p ^^ in_alg _ %= \prod_(x <- numfield_roots p) ('X - x%:P).
Proof.
by move=> p_neq0; rewrite /numfield_roots; case: eqP => //= ?; case: sig2_eqW.
Qed.

Lemma adjoin_numfield_roots (p : {poly rat}) :
  (<<1 & numfield_roots p>> = fullv)%VS.
Proof.
rewrite /numfield_roots; case: eqP => [p0|/negP]; first by case: sig2_eqW.
by rewrite negbK => /eqP->; rewrite numfield0 regular_fullv Fadjoin_nil.
Qed.

Open Scope ring_scope.

Module PrimeDegreeTwoNonRealRoots.
Section PrimeDegreeTwoNonRealRoots.

Variables (p : {poly rat}).

Let L := numfield p.
Let charL : has_char0 L := char_numfield p.
Let iota : {rmorphism L -> algC} := numfield_inC p.
Let rp' : seq L := numfield_roots p.

Hypothesis p_irr : irreducible_poly p.

Let p_neq0 : p != 0.
Proof.
have := p_irr; rewrite /irreducible_poly => -[+ _].
by apply: contraTneq => ->; rewrite size_poly0.
Qed.

Let ratr_p' : map_poly ratr p %= \prod_(x <- rp') ('X - x%:P).
Proof.
by have := poly_numfield_eqp p_neq0; rewrite (eq_map_poly (fmorph_eq_rat _)).
Qed.

Let rp'_uniq : uniq rp'.
Proof.
rewrite -separable_prod_XsubC -(eqp_separable ratr_p').
rewrite -char0_ratrE separable_map.
apply/coprimepP => d; have [sp_gt1 eqp] := p_irr => /eqp.
rewrite size_poly_eq1; have [//|dN1 /(_ isT)] := boolP (d %= 1).
move=> /eqp_dvdl-> /dvdp_leq; rewrite -size_poly_eq0 polyorder.size_deriv.
by case: (size p) sp_gt1 => [|[|n]]//= _; rewrite ltnn; apply.
Qed.

Let d := (size p).-1.
Hypothesis d_prime : prime d.
Hypothesis count_rp' : count [pred x | iota x \isn't Num.real] rp' = 2%N.

Let rp := [seq x <- rp' | iota x \isn't Num.real]
          ++ [seq x <- rp' | iota x \is Num.real].

Let rp_perm : perm_eq rp rp'. Proof. by rewrite perm_catC perm_filterC. Qed.
Let rp_uniq : uniq rp. Proof. by rewrite (perm_uniq rp_perm). Qed.
Let ratr_p : map_poly ratr p %= \prod_(x <- rp) ('X - x%:P).
Proof.
rewrite (eqp_trans ratr_p')// eqp_monic ?monic_prod_XsubC//.
exact/eqP/esym/perm_big.
Qed.

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

Let p_sep : separable_poly p.
Proof.
rewrite -(separable_map [rmorphism of char0_ratr charL]).
by rewrite (eqp_separable ratr_p) separable_prod_XsubC.
Qed.

Let d_gt0 : (d > 0)%N.
Proof. by rewrite prime_gt0. Qed.

Let d_gt1 : (d > 1)%N.
Proof. by rewrite prime_gt1. Qed.

Lemma size_rp : size rp = d.
Proof.
have /eqp_size := ratr_p; rewrite -char0_ratrE size_map_poly.
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

Lemma root_p : root (p ^^ ratr) =i rp.
Proof. by move=> x; rewrite -topredE/= (eqp_root ratr_p) root_prod_XsubC. Qed.

Lemma rp_roots : all (root (map_poly ratr p)) rp.
Proof. by apply/allP => x; rewrite -root_p. Qed.

Lemma ratr_p_rp i : (i < d)%N -> (map_poly ratr p).[rp`_i] = 0.
Proof. by move=> ltid; apply/eqP; rewrite [_ == _]root_p mem_nth ?size_rp. Qed.

Lemma rpK i : (i < d)%N -> rp`_i \in K.
Proof. by move=> ltid; rewrite [_ \in _](allP all_rpK) ?mem_nth ?size_rp. Qed.

Lemma eq_size_rp : size rp == d. Proof. exact/eqP/size_rp. Qed.
Let trp := Tuple eq_size_rp.

Lemma gal_perm_eq (g : gal_of K) : perm_eq [seq g x | x <- trp] trp.
Proof.
apply: prod_XsubC_eq; apply/eqP; rewrite -eqp_monic ?monic_prod_XsubC//.
rewrite -(eqp_rtrans ratr_p) big_map.
apply: (@eqp_trans _ (map_poly (g \o ratr) p)); last first.
  apply/eqpW/eq_map_poly => x /=; rewrite (fixed_gal _ (gal1 g)) ?sub1v//.
  by rewrite -alg_num_field rpredZ ?mem1v.
rewrite map_poly_comp/=; have := ratr_p; rewrite -(eqp_map [rmorphism of g])/=.
move=> /eqp_rtrans/=->; apply/eqpW; rewrite rmorph_prod.
by apply: eq_bigr => x; rewrite rmorphB/= map_polyX map_polyC/=.
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

Lemma minPoly_rp x : x \in rp -> minPoly 1%VS x %= map_poly ratr p.
Proof.
move=> xrp; have : minPoly 1 x %| map_poly ratr p.
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
  rewrite -size_minPoly (eqp_size (minPoly_rp _)) ?mem_nth ?size_rp//.
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
by rewrite gen_subG; apply/subsetP => s /set2P[]->;
   rewrite -?galJ_tperm ?mem_morphim ?gal1.
Qed.

Lemma isog_gal_perm : 'Gal (K / 1%AS) \isog 'Sym_('I_d).
Proof.
apply/isogP; exists gal_perm_morphism; first exact: injm_gal_perm.
exact: surj_gal_perm.
Qed.

Lemma isog_gal : 'Gal ({:numfield p} / 1%AS) \isog 'Sym_('I_d).
Proof. by rewrite -adjoin_numfield_roots isog_gal_perm. Qed.

End PrimeDegreeTwoNonRealRoots.
End PrimeDegreeTwoNonRealRoots.
Module PDTNRR := PrimeDegreeTwoNonRealRoots.

Section Example1.

Definition poly_example_int : {poly int} := 'X^5 - 4 *: 'X + 2.
Definition poly_example : {poly rat} := 'X^5 - 4 *: 'X + 2.

Local Definition pesimp := (coefD, coefN, coefB, coefZ, coefXn, coefX, coefC,
  hornerD, hornerN, hornerC, hornerZ, hornerX, hornerXn, rmorph_nat).

Lemma polyCn (R : ringType) n : n%:R%:P = n%:R :> {poly R}.
Proof. by rewrite rmorph_nat. Qed.

Lemma poly_exampleEint : poly_example = map_poly intr poly_example_int.
Proof.
pose simp := (rmorphB, rmorphD, map_polyZ, map_polyXn, map_polyX, map_polyC).
by do !rewrite [map_poly _ _]simp/= ?natz.
Qed.

Lemma size_poly_example_int : size poly_example_int = 6%N.
Proof.
rewrite /poly_example_int -addrA size_addl ?size_polyXn//.
by rewrite size_addl ?size_opp ?size_scale ?size_polyX -?polyCn ?size_polyC.
Qed.

Lemma size_poly_example : size poly_example = 6%N.
Proof.
rewrite /poly_example -addrA size_addl ?size_polyXn//.
by rewrite size_addl ?size_opp ?size_scale ?size_polyX -?polyCn ?size_polyC.
Qed.

Lemma poly_example_int_neq0 : poly_example_int != 0.
Proof. by rewrite -size_poly_eq0 size_poly_example_int. Qed.

Lemma poly_example_neq0 : poly_example != 0.
Proof. by rewrite -size_poly_eq0 size_poly_example. Qed.
#[local] Hint Resolve poly_example_neq0 : core.

Lemma poly_example_monic : poly_example \is monic.
Proof. by rewrite monicE lead_coefE !pesimp size_poly_example. Qed.
#[local] Hint Resolve poly_example_monic : core.

Lemma irreducible_example : irreducible_poly poly_example.
Proof.
rewrite poly_exampleEint; apply: (@eisenstein 2) => // [|||i];
  rewrite ?lead_coefE ?size_poly_example_int ?pesimp//.
by move: i; do 6!case=> //.
Qed.
#[local] Hint Resolve irreducible_example : core.

Lemma separable_example : separable_poly poly_example.
Proof.
apply/coprimepP => q /(irredp_XsubCP irreducible_example) [//| eqq].
have size_deriv_example : size poly_example^`() = 5%N.
  rewrite !derivCE addr0 alg_polyC -scaler_nat addr0.
  by rewrite size_addl ?size_scale ?size_opp ?size_polyXn ?size_polyC.
rewrite gtNdvdp -?size_poly_eq0 ?size_deriv_example//.
by rewrite (eqp_size eqq) ?size_poly_example.
Qed.
#[local] Hint Resolve separable_example : core.

Lemma prime_example : prime (size poly_example).-1.
Proof. by rewrite size_poly_example. Qed.

(* Using the package real_closed, we should be able to monitor the sign of    *)
(* the derivative, and find that the polynomial has exactly three real roots. *)
Definition example_roots : seq algC :=
  map (numfield_inC poly_example) (numfield_roots poly_example).

Lemma ratr_example_poly :
  poly_example ^^ ratr = \prod_(x <- example_roots) ('X - x%:P).
Proof.
rewrite /example_roots -map_prod_XsubC/=.
have := poly_numfield_eqp poly_example_neq0.
rewrite eqp_monic ?monic_prod_XsubC ?monic_map// => /eqP<-.
by rewrite -map_poly_comp [in RHS](eq_map_poly (fmorph_eq_rat _)).
Qed.

Lemma size_example_roots : size example_roots = 5%N.
Proof.
have /(congr1 (fun p : {poly _} => size p)) := ratr_example_poly.
by rewrite size_map_poly size_poly_example size_prod_XsubC => -[].
Qed.

Lemma example_roots_uniq : uniq example_roots.
Proof.
rewrite -separable_prod_XsubC -ratr_example_poly.
by rewrite separable_map separable_example.
Qed.

Lemma deriv_poly_example : poly_example^`() = 5%:R *: 'X^4 - 4%:R%:P.
Proof. by rewrite /poly_example !derivE addr0 alg_polyC scaler_nat ?addr0. Qed.

Lemma deriv_poly_example_neq0 : poly_example^`() != 0.
Proof.
apply/eqP => /(congr1 (fun p => p.[0])).
by rewrite deriv_poly_example !pesimp => /eqP; compute.
Qed.
#[local] Hint Resolve deriv_poly_example_neq0 : core.

Definition alpha : algR := Num.sqrt (2%:R / Num.sqrt 5%:R).

Lemma alpha_gt0 : alpha > 0.
Proof. by rewrite sqrtr_gt0 mulr_gt0 ?invr_gt0 ?sqrtr_gt0 ?ltr0n. Qed.

Lemma rootsR_deriv_poly_example :
  rootsR (poly_example^`() ^^ ratr) = [:: - alpha; alpha].
Proof.
apply: lt_sorted_eq; rewrite ?sorted_roots//.
 by rewrite /= andbT -subr_gt0 opprK ?addr_gt0 ?alpha_gt0.
move=> x; rewrite mem_rootsR ?map_poly_eq0// !inE -topredE/= orbC.
rewrite deriv_poly_example /root.
rewrite rmorphB linearZ/= map_polyC/= map_polyXn !pesimp.
rewrite -[5%:R]sqr_sqrtr ?ler0n// (exprM _ 2 2) -exprMn (natrX _ 2 2) subr_sqr.
rewrite mulf_eq0 [_ + 2%:R == 0]gt_eqF ?orbF; last first.
  by rewrite ltr_spaddr ?ltr0n// mulr_ge0 ?sqrtr_ge0// exprn_even_ge0.
have sqrt5N0 : Num.sqrt (5%:R : algR) != 0 by rewrite gt_eqF// sqrtr_gt0 ?ltr0n.
rewrite subr_eq0 (can2_eq (mulKf _) (mulVKf _))// mulrC -subr_eq0.
rewrite -[X in _ - X]sqr_sqrtr; last first.
  by rewrite mulr_ge0 ?invr_ge0 ?sqrtr_ge0 ?ler0n.
by rewrite subr_sqr mulf_eq0 subr_eq0 addr_eq0.
Qed.

Lemma count_roots_ex : count [predC Creal] example_roots = 2%N.
Proof.
rewrite -!sum1_count; pose pR : {poly algR} := poly_example ^^ ratr.
have pR0 : pR != 0 by rewrite map_poly_eq0.
suff cR : (\sum_(j <- example_roots | j \is Num.real) 1)%N = 3%N.
  have := size_example_roots; rewrite -sum1_size (bigID (mem Num.real))/=.
  by rewrite cR => -[->].
rewrite -big_filter (perm_big (map algRval (rootsR pR))); last first.
  rewrite uniq_perm ?filter_uniq ?example_roots_uniq//.
    by rewrite (map_inj_uniq (fmorph_inj _)) uniq_roots.
  move=> x; rewrite mem_filter -root_prod_XsubC -ratr_example_poly.
  rewrite -(eq_map_poly (fmorph_eq_rat [rmorphism of algRval \o ratr]))/=.
  rewrite map_poly_comp/=.
  apply/andP/mapP => [[xR xroot]|[y + ->]].
    exists (in_algR xR); rewrite // mem_rootsR// -topredE/=.
    by rewrite -(mapf_root algRval_rmorphism)/=.
  rewrite mem_rootsR// -[y \in _]topredE/=.
  by split; [apply/algRvalP|rewrite mapf_root].
apply/eqP; rewrite sum1_size size_map eqn_leq.
rewrite (leq_trans (size_root_leSderiv _))//=; last first.
  by rewrite deriv_map rootsR_deriv_poly_example.
have pRE x : Num.sg pR.[x%:~R] = locked ratr (Num.sg poly_example.[x%:~R]).
  by rewrite -lock ratr_sg -horner_map/= ratr_int.
have pN2 : Num.sg pR.[(- 2%:Z)%:~R] = - 1 by rewrite pRE !pesimp -lock rmorphN1.
have pN1 : Num.sg pR.[(- 1%:Z)%:~R] =   1 by rewrite pRE !pesimp -lock rmorph1.
have p1  : Num.sg pR.[1%:~R]        = - 1 by rewrite pRE !pesimp -lock rmorphN1.
have p2  : Num.sg pR.[2%:~R]        =   1 by rewrite pRE !pesimp -lock rmorph1.
have simp := (pN2, pN1, p1, p2, mulN1r, mulrN1).
have [||x0 /andP[_ x0N1] rx0] := @ivt_sign _ pR (- 2%:R) (- 1); rewrite ?simp//.
  by rewrite -subr_ge0 opprK addKr ler01.
have [||x1 /andP[x10 x11] rx1] := @ivt_sign _ pR (-1) 1; rewrite ?simp//.
  by rewrite -subr_ge0 opprK addr_ge0 ?ler01.
have [||x2 /andP[/= x21 _] rx2] := @ivt_sign _ pR 1 2%:R; rewrite ?simp//.
  by rewrite -subr_ge0 addrK ler01.
have: sorted <%R [:: x0; x1; x2] by rewrite /= (lt_trans x0N1) ?(lt_trans x11).
rewrite lt_sorted_uniq_le => /andP[uniqx012 _].
apply: (@uniq_leq_size _ [:: x0; x1; x2]) => //.
by move=> x; rewrite !inE => /or3P[]/eqP->/=; rewrite mem_rootsR.
Qed.

Lemma example_not_solvable_by_radicals :
  ~ solvable_by_radical_poly ('X^5 - 4 *: 'X + 2 : {poly rat}).
Proof.
move=> /AbelGaloisPolyRat; pose sol_gal := isog_sol (PDTNRR.isog_gal _ _ _).
rewrite sol_gal ?size_poly_example ?solvable_SymF ?card_ord//.
by rewrite -(count_map _ [predC Creal]) count_roots_ex.
Qed.

End Example1.

Section Formula.
Definition prim1root_ n := projT1 (@C_prim_root_exists n.-1.+1 isT).

Lemma prim1rootP n : (n > 0)%N -> n.-primitive_root (prim1root_ n).
Proof.
by case: n => [|n]// _; rewrite /prim1root_; case: C_prim_root_exists.
Qed.

Inductive const := Zero | One | URoot of nat.
Inductive binOp := Add | Mul.
Inductive unOp := Opp | Inv | Exp of nat | Root of nat.
Inductive algterm (F : Type) : Type :=
| Base of F
| Const of const
| UnOp of unOp & algterm F
| BinOp of binOp & algterm F & algterm F.
Arguments Const {F}.

Definition encode_const (c : const) : nat :=
   match c with Zero => 0 | One => 1 | URoot n => n.+2 end.
Definition decode_const (n : nat) : const :=
   match n with 0 => Zero | 1 => One | n.+2 => URoot n end.
Lemma code_constK : cancel encode_const decode_const.
Proof. by case. Qed.
Definition const_eqMixin := CanEqMixin code_constK.
Canonical const_eqType := EqType const const_eqMixin.
Definition const_choiceMixin := CanChoiceMixin code_constK.
Canonical const_choiceType := ChoiceType const const_choiceMixin.
Definition const_countMixin := CanCountMixin code_constK.
Canonical const_countType := CountType const const_countMixin.

Definition encode_binOp (c : binOp) : bool :=
   match c with Add => false | Mul => true end.
Definition decode_binOp (b : bool) : binOp :=
   match b with false => Add | _ => Mul end.
Lemma code_binOpK : cancel encode_binOp decode_binOp.
Proof. by case. Qed.
Definition binOp_eqMixin := CanEqMixin code_binOpK.
Canonical binOp_eqType := EqType binOp binOp_eqMixin.
Definition binOp_choiceMixin := CanChoiceMixin code_binOpK.
Canonical binOp_choiceType := ChoiceType binOp binOp_choiceMixin.
Definition binOp_countMixin := CanCountMixin code_binOpK.
Canonical binOp_countType := CountType binOp binOp_countMixin.

Definition encode_unOp (c : unOp) : nat + nat :=
   match c with Opp => inl _ 0%N | Inv => inl _ 1%N
           | Exp n => inl _ n.+2 | Root n => inr _ n end.
Definition decode_unOp (n : nat + nat) : unOp :=
   match n with inl 0 => Opp | inl 1 => Inv
           | inl n.+2 => Exp n | inr n => Root n end.
Lemma code_unOpK : cancel encode_unOp decode_unOp.
Proof. by case. Qed.
Definition unOp_eqMixin := CanEqMixin code_unOpK.
Canonical unOp_eqType := EqType unOp unOp_eqMixin.
Definition unOp_choiceMixin := CanChoiceMixin code_unOpK.
Canonical unOp_choiceType := ChoiceType unOp unOp_choiceMixin.
Definition unOp_countMixin := CanCountMixin code_unOpK.
Canonical unOp_countType := CountType unOp unOp_countMixin.

Fixpoint encode_algT F (f : algterm F) : GenTree.tree (F + const) :=
  let T_ isbin := if isbin then binOp else unOp in
  match f with
  | Base x => GenTree.Leaf (inl x)
  | Const c => GenTree.Leaf (inr c)
  | UnOp u f1 => GenTree.Node (pickle (inl u : unOp + binOp))
                              [:: encode_algT f1]
  | BinOp b f1 f2 => GenTree.Node (pickle (inr b : unOp + binOp))
                                  [:: encode_algT f1; encode_algT f2]
  end.
Fixpoint decode_algT F (t : GenTree.tree (F + const)) : algterm F :=
  match t with
  | GenTree.Leaf (inl x) => Base x
  | GenTree.Leaf (inr c) => Const c
  | GenTree.Node n fs =>
    match locked (unpickle n), fs with
    | Some (inl u), f1 :: _ => UnOp u (decode_algT f1)
    | Some (inr b), f1 :: f2 :: _ => BinOp b (decode_algT f1) (decode_algT f2)
    | _, _ => Const Zero
    end
  end.
Lemma code_algTK F : cancel (@encode_algT F) (@decode_algT F).
Proof.
by elim => // [u f IHf|b f IHf f' IHf']/=; rewrite pickleK -lock ?IHf ?IHf'.
Qed.
Definition algT_eqMixin (F : eqType) := CanEqMixin (@code_algTK F).
Canonical algT_eqType (F : eqType) := EqType (algterm F) (@algT_eqMixin F).
Definition algT_choiceMixin (F : choiceType) := CanChoiceMixin (@code_algTK F).
Canonical algT_choiceType (F : choiceType) :=
  ChoiceType (algterm F) (@algT_choiceMixin F).
Definition algT_countMixin (F : countType) := CanCountMixin (@code_algTK F).
Canonical algT_countType (F : countType) :=
  CountType (algterm F) (@algT_countMixin F).

Declare Scope algT_scope.
Delimit Scope algT_scope with algT.
Bind Scope algT_scope with algterm.
Local Notation "0" := (Const Zero) : algT_scope.
Local Notation "1" := (Const One) : algT_scope.
Local Notation "- x" := (UnOp Opp x) : algT_scope.
Local Notation "- 1" := (- (1)) : algT_scope.
Local Infix "+" := (BinOp Add) : algT_scope.
Local Notation "x ^-1" := (UnOp Inv x) : algT_scope.
Local Infix "*" := (BinOp Mul) : algT_scope.
Local Notation "x ^+ n" := (UnOp (Exp n) x) : algT_scope.
Local Notation "n '.+1-root'" := (UnOp (Root n))
  (at level 2, format "n '.+1-root'") : algT_scope.
Local Notation "n '.+1-prim1root'" := (Const (URoot n))
  (at level 2, format "n '.+1-prim1root'") : algT_scope.

Section eval.
Variables (F : fieldType) (iota : F -> algC).
Fixpoint algT_eval (f : algterm F) : algC :=
  match f with
  | Base x                => iota x
  | 0%algT                => 0
  | 1%algT                => 1
  | (f1 + f2)%algT        => algT_eval f1 + algT_eval f2
  | (- f1)%algT           => - algT_eval f1
  | (f1 * f2)%algT        => algT_eval f1 * algT_eval f2
  | (f1 ^-1)%algT         => (algT_eval f1)^-1
  | (f1 ^+ n)%algT        => (algT_eval f1) ^+ n
  | (n.+1-root f1)%algT   => n.+1.-root (algT_eval f1)
  | (j.+1-prim1root)%algT => prim1root_ j.+1
  end.

Fixpoint subeval (f : algterm F) : seq algC :=
  algT_eval f :: match f with
  | UnOp _ f1 => subeval f1
  | BinOp _ f1 f2 => subeval f1 ++ subeval f2
  | _ => [::]
  end.

Lemma subevalE f : subeval f = algT_eval f :: behead (subeval f).
Proof. by case: f => *. Qed.

End eval.

Lemma solvable_formula (p : {poly rat}) : p != 0 ->
  solvable_by_radical_poly p <->
  {in root (p ^^ ratr), forall x,
     exists f : algterm rat, algT_eval ratr f = x}.
Proof.
have Cchar := Cchar => p_neq0; split.
  move=> /solvable_poly_rat[]// L [iota [rs [prs [E rE KE]]]] x.
  have pirs : p ^^ ratr %= \prod_(x <- map iota rs) ('X - x%:P).
    have := prs; rewrite -(eqp_map iota) map_prod_XsubC => /eqp_rtrans<-.
    by rewrite -map_poly_comp (eq_map_poly (fmorph_eq_rat _)) eqpxx.
  rewrite -topredE/= (eqp_root pirs) root_prod_XsubC => /mapP[{}r rrs ->].
  suff [f <- /=]: exists f : algterm (subvs_of (1%VS : {vspace L})),
      algT_eval (iota \o vsval) f = iota r.
    elim: f => //= [[/= _/vlineP[s ->]]|cst|op|op].
    - exists (Base s) => /=.
      by rewrite [RHS](fmorph_eq_rat [rmorphism of iota \o in_alg L]).
    - by exists (Const cst).
    - by move=> _ [f1 <-]; exists (UnOp op f1).
    - by move=> _ [f1 <-] _ [f2 <-]; exists (BinOp op f1 f2).
  have: r \in E by rewrite (subvP KE)// seqv_sub_adjoin.
  case: rE => -[/= n e pw] epw <-.
  rewrite -[1%VS]/(1%AS : {vspace _}) in epw *.
  elim: n 1%AS => [|n IHn] k /= in e pw epw *.
    by rewrite tuple0 Fadjoin_nil => rk; exists (Base (Subvs rk)).
  case: (tupleP e) (tupleP pw) epw => [u e'] [i pw']/= epw.
  rewrite adjoin_cons => /IHn-/(_ pw')[].
    apply/towerP => j /=.
    have /towerP/(_ (lift ord0 j))/= := epw.
    by rewrite !tnthS/= adjoin_cons.
  move=> f <-; elim: f => //= [s|cst|op|op]; last 3 first.
  - by exists (Const cst).
  - by move=> _ [f1 <-]; exists (UnOp op f1).
  - by move=> _ [f1 <-] _ [f2 <-]; exists (BinOp op f1 f2).
  have /Fadjoin_polyP[q qk ->] := subvsP s.
  have /towerP/(_ ord0) := epw; rewrite !tnth0/= Fadjoin_nil.
  move=> /radicalP[][]; last by rewrite char_ext.
  case: i => // i in epw * => _ uik.
  pose v := i.+1.-root (iota (u ^+ i.+1)).
  have : ('X ^+ i.+1 - (v ^+ i.+1)%:P).[iota u] == 0.
    by rewrite !hornerE ?hornerXn rootCK// rmorphX subrr.
    (* FIXME: remove ?hornerXn when requiring MC >= 1.16.0 *)
  have /Xn_sub_xnE->// := prim1rootP (isT : 0 < i.+1)%N.
  rewrite horner_prod prodf_seq_eq0/= => /hasP[/= l _].
  rewrite hornerXsubC subr_eq0 => /eqP u_eq.
  pose fu := (i.+1-root (Base (Subvs uik)) * (i.+1-prim1root ^+ l))%algT.
  rewrite -horner_map; have -> : iota u = algT_eval (iota \o vsval) fu by [].
  move: fu => fu; elim/poly_ind: q qk => //= [|q c IHq] qXDck.
    by exists 0%algT; rewrite rmorph0 horner0.
  have ck : c \in k.
    by have /polyOverP/(_ 0%N) := qXDck; rewrite coefD coefMX coefC/= add0r.
  have qk : q \is a polyOver k.
    apply/polyOverP => j; have /polyOverP/(_ j.+1) := qXDck.
    by rewrite coefD coefMX coefC/= addr0.
  case: IHq => // fq fq_eq.
  exists (fq * fu + Base (Subvs ck))%algT => /=.
  by rewrite rmorphD rmorphM/= map_polyX map_polyC !hornerE fq_eq.
move=> mkalg; apply/solvable_by_radical_polyP => //=; first exact: char_num.
have [/= rsalg pE] := closed_field_poly_normal (p ^^ (ratr : _ -> algC)).
have {}pE : p ^^ ratr %= \prod_(z <- rsalg) ('X - z%:P).
  rewrite pE (eqp_trans (eqp_scale _ _)) ?eqpxx//.
  by rewrite lead_coef_map//= fmorph_eq0 lead_coef_eq0.
have [fs fsE] : exists fs, map (algT_eval ratr) fs = rsalg.
  have /(_ _ _)/sig_eqW-/(all_sig_cond (Base 0)) [h hE] :
      forall x : algC, x \in rsalg -> exists f, algT_eval ratr f = x.
    by move=> *; apply: mkalg; rewrite -topredE/= (eqp_root pE) root_prod_XsubC.
  by exists (map h rsalg); rewrite -map_comp map_id_in//.
pose algs := flatten (map (subeval ratr) fs).
pose mp := \prod_(x <- algs) projT1 (minCpolyP x).
have mp_monic : mp \is monic.
  by rewrite monic_prod => // i _; case: minCpolyP => /= ? [].
have mpratr : mp ^^ ratr = \prod_(x <- algs) minCpoly x.
  rewrite rmorph_prod/=; apply: eq_bigr => x _.
  by case: minCpolyP => //= ? [].
have [rsmpalg mpE] := closed_field_poly_normal (mp ^^ ratr : {poly algC}).
have mp_neq0 : mp != 0.
  rewrite prodf_seq_eq0; apply/hasPn => /= x xalgs.
  by case: minCpolyP => //= ? [_ /monic_neq0->].
have {}mpE : mp ^^ ratr = \prod_(z <- rsmpalg) ('X - z%:P).
  by rewrite mpE lead_coef_map/= (eqP mp_monic) rmorph1 scale1r.
have [L [iota [rsmp iota_rs rsf]]] := num_field_exists rsmpalg.
have charL : has_char0 L by move=> x; rewrite char_lalg char_num.
have mprs : mp ^^ in_alg L %= \prod_(z <- rsmp) ('X - z%:P).
  rewrite -(eqp_map iota) map_prod_XsubC iota_rs -map_poly_comp -mpE.
  by rewrite -char0_ratrE// (eq_map_poly (fmorph_eq_rat _)) eqpxx.
have splitL : SplittingField.axiom L.
  by exists (mp ^^ in_alg L); [apply/polyOver1P; exists mp | exists rsmp].
pose S := SplittingFieldType rat L splitL.
have algsW: {subset rsalg <= algs}.
  move=> x; rewrite -fsE => /mapP[{x}f ffs ->].
  apply/flattenP; exists (subeval ratr f); rewrite ?map_f//.
  by rewrite subevalE mem_head.
have rsmpW: {subset algs <= rsmpalg}.
  move=> x xalgs; rewrite -root_prod_XsubC -mpE mpratr.
  by rewrite (big_rem _ xalgs)/= rootM root_minCpoly.
have := rsmpW; rewrite -iota_rs => /subset_mapP[als _ /esym alsE].
have := algsW; rewrite -alsE => /subset_mapP[rs _ /esym rsE].
have prs : p ^^ in_alg S %= \prod_(x <- rs) ('X - x%:P).
  rewrite -(eqp_map iota) -map_poly_comp (eq_map_poly (fmorph_eq_rat _)).
  by rewrite map_prod_XsubC rsE.
apply/classicW; exists S, rs; split => //.
exists <<1 & als>>%AS; last first.
  rewrite adjoin_seqSr// => x /(map_f iota); rewrite rsE => /algsW.
  by rewrite -[X in _ \in X]alsE (mem_map (fmorph_inj _)).
rewrite {p p_neq0 mkalg pE prs rsmp iota_rs mprs rsf rs rsE mp
        mp_monic mpratr rsmpalg mp_neq0 mpE algsW rsmpW charL}/=.
suff: forall (L : splittingFieldType rat) (iota : {rmorphism L -> algC}) als,
        map iota als = algs -> radical.-ext 1%VS <<1 & als>>%VS.
  by move=> /(_ S iota als alsE).
move=> {}L {}iota {splitL S} {}als {}alsE; rewrite {}/algs in alsE.
elim: fs => [|f fs IHfs]//= in rsalg fsE als alsE *.
  case: als => []// in alsE *.
  by rewrite Fadjoin_nil; apply: rext_refl.
move: rsalg fsE => [|r rsalg]// [fr fsE].
pose n := size (subeval ratr f); rewrite -[als](cat_take_drop n).
have /(congr1 (take n)) := alsE; rewrite take_size_cat//.
rewrite -map_take; move: (take _ _) => als1 als1E.
have /(congr1 (drop n)) := alsE; rewrite drop_size_cat//.
rewrite -map_drop; move: (drop _ _) => als2 als2E.
have /rext_trans := IHfs _ fsE _ als2E; apply.
have -> : <<1 & als1 ++ als2>>%AS = <<<<1 & als2>>%AS & als1>>%AS.
  apply/val_inj; rewrite /= -adjoin_cat; apply/eq_adjoin => x.
  by rewrite !mem_cat orbC.
move: <<1 & als2>>%AS => /= k {als2 als2E n fs fsE IHfs rsalg als alsE}.
elim: f => //= [x|c|u f1 IHf1|b f1 IHf1 f2 IHf2] in k {r fr} als1 als1E *.
- case: als1 als1E => [|y []]//= [yx]/=.
  rewrite adjoin_seq1 (Fadjoin_idP _); first exact: rext_refl.
  suff: y \in 1%VS by apply/subvP; rewrite sub1v.
  apply/vlineP; exists x; apply: (fmorph_inj iota); rewrite yx.
  by rewrite [RHS](fmorph_eq_rat [rmorphism of iota \o in_alg _]).
- case: als1 als1E => [|y []]//= []/=; rewrite adjoin_seq1.
  case: c => [/eqP|/eqP|n yomega].
  + rewrite fmorph_eq0 => /eqP->; rewrite (Fadjoin_idP _) ?rpred0//.
    exact: rext_refl.
  + rewrite fmorph_eq1 => /eqP->; rewrite (Fadjoin_idP _) ?rpred1//.
    exact: rext_refl.
  + apply/(@rext_r _ _ _ n.+1)/radicalP; left; split.
      by apply/negP; rewrite pnatr_eq0.
    rewrite prim_expr_order ?rpred1//.
    by rewrite -(fmorph_primitive_root iota) yomega prim1rootP.
- case: als1 als1E => //= a l [IHl IHlu].
  rewrite -(eq_adjoin _ (mem_rcons _ _)) adjoin_rcons.
  apply: rext_trans (IHf1 k l IHlu) _ => /=.
  move: IHlu; rewrite subevalE; case: l => // x1 l [iotax1 _].
  rewrite -iotax1 -rmorphN -fmorphV in IHl.
  have x1kx1 : x1 \in <<k & x1 :: l>>%VS by rewrite seqv_sub_adjoin ?mem_head.
  case: u => [||n|n]/= in IHl.
  + rewrite (Fadjoin_idP _); first exact: rext_refl.
    by have /fmorph_inj-> := IHl; rewrite rpredN.
  + rewrite (Fadjoin_idP _); first exact: rext_refl.
    by have /fmorph_inj-> := IHl; rewrite rpredV.
  + rewrite (Fadjoin_idP _); first exact: rext_refl.
    by have := IHl; rewrite -rmorphX => /fmorph_inj->; rewrite rpredX.
  apply/(@rext_r _ _ _ n.+1)/radicalP; left; split.
    by apply/negP; rewrite pnatr_eq0.
  have /(congr1 ((@GRing.exp _)^~ n.+1)) := IHl.
  by rewrite rootCK// -rmorphX => /fmorph_inj->.
- case: als1 als1E => //= a l [IHl IHlu].
  rewrite -(eq_adjoin _ (mem_rcons _ _)) adjoin_rcons.
  pose n := size (subeval ratr f1); rewrite -[l](cat_take_drop n).
  have /(congr1 (take n)) := IHlu; rewrite take_size_cat//.
  rewrite -map_take; move: (take _ _) => l1 l1E.
  have /(congr1 (drop n)) := IHlu; rewrite drop_size_cat//.
  rewrite -map_drop; move: (drop _ _) => l2 l2E.
  apply: rext_trans (IHf1 _ l1 l1E) _ => /=.
  apply: rext_trans (IHf2 _ l2 l2E) _ => /=.
  rewrite -adjoin_cat (Fadjoin_idP _); first exact: rext_refl.
  rewrite subevalE in l1E; rewrite subevalE in l2E.
  case: l1 l1E => // b1 l1 [iotab1 _].
  case: l2 l2E => // b2 l2 [iotab2 _].
  rewrite -iotab1 -iotab2 -rmorphM -rmorphD in IHl.
  have b2l : b2 \in (b1 :: l1) ++ (b2 :: l2) by rewrite mem_cat mem_head orbT.
  have b1l : b1 \in (b1 :: l1) ++ (b2 :: l2) by rewrite mem_head.
  by case: b IHl => /fmorph_inj ->; rewrite ?(rpredD, rpredM)// seqv_sub_adjoin.
Qed.

End Formula.
