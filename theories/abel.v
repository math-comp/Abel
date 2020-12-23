From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field polyrcf qe_rcf_th qe_rcf.
From Abel Require Import various classic_ext map_gal.
From Abel Require Import diag char0 cyclotomic galmx.
(* bug: qe_rcf exports a redefinition of `True` and `False` *)
Notation False := Logic.False.
Notation True := Logic.True.


(*****************************************************************************)
(* We work inside a enclosing splittingFieldType L over a base field F0      *)
(*                                                                           *)
(*     radical U x n := x is a radical element of degree n over U            *)
(*    pradical U x p := x is a radical element of prime degree p over U      *)
(* r.-tower n U e pw := e is a chain of n elements of L such that            *)
(*                      forall i, r <<U & take i e>> e`_i pw`_i              *)
(*        r.-ext U V := there exists e and pw such that <<U & e>> = V        *)
(*                      and r.-tower r U e pw.                               *)
(* solvable_by r E F := there is a field K, such that F <= K and r.-ext E K  *)
(*                      if p has roots rs, solvable_by radicals E <<E, rs>>  *)
(*                                                                           *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

Section RadicalExtension.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Hypothesis (charL : [char L] =i pred0).

Section Defs.

Implicit Types (U V : {vspace L}).

Definition radical U x n  := [&& (n > 0)%N & x ^+ n \in U].
Definition pradical U x p := [&& prime p & x ^+ p \in U].

Lemma radicalP U x n : reflect  [/\ (n > 0)%N & x ^+ n \in U]
                                [&& (n > 0)%N & x ^+ n \in U].
Proof. exact/andP. Qed.

Lemma pradicalP U x p : reflect [/\ prime p & x ^+ p \in U]
                                [&& prime p & x ^+ p \in U].
Proof. exact/andP. Qed.

Implicit Types r : {vspace L} -> L -> nat -> bool.

Definition tower r n U (e : n.-tuple L) (pw : n.-tuple nat) :=
  [forall i : 'I_n, r << U & take i e >>%VS (tnth e i) (tnth pw i)].

Lemma towerP r n U (e : n.-tuple L) (pw : n.-tuple nat) :
  reflect (forall i : 'I_n, r << U & take i e >>%VS (tnth e i) (tnth pw i))
          (tower r U e pw).
Proof. exact/forallP. Qed.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.

Record ext_data := ExtData { ext_size : nat;
                             ext_ep : ext_size.-tuple L;
                             ext_pw : ext_size.-tuple nat }.
Arguments ExtData [ext_size].

Definition trivExt := ExtData [tuple] [tuple].

Definition extension_of r U V :=
  exists2 e : ext_data,
    r.-tower (ext_size e) U (ext_ep e) (ext_pw e)
    & << U & ext_ep e >>%VS = V.

Local Notation "r .-ext" := (extension_of r)
  (at level 2, format "r .-ext") : ring_scope.

Definition solvable_by r (U V : {subfield L}) :=
  exists2 E : {subfield L}, r.-ext U E & (V <= E)%VS.

End Defs.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.
Local Notation "r .-ext" := (extension_of r)
  (at level 2, format "r .-ext") : ring_scope.

Section Properties.

Implicit Types r : {vspace L} -> L -> nat -> bool.
Implicit Types (U V : {subfield L}).

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

Lemma radical_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  (0 < n)%N -> x ^+ n \in E -> radical E x n.
Proof. by move=> ? ?; apply/radicalP. Qed.

Lemma pradical_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  prime n -> x ^+ n \in E -> pradical E x n.
Proof. by move=> ? ?; apply/pradicalP. Qed.

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
  by apply: (@pradical_ext_Fadjoin n).
case/boolP: (2 <= n)%N; last first.
  case: n {lenk primeN_n} => [|[]]// in xnE n_gt0 * => _.
  suff ->:  <<E; x>>%VS = E by apply: rext_refl.
  by rewrite (Fadjoin_idP _).
move: primeN_n => /primePn[|[d /andP[d_gt1 d_ltn] dvd_dn n_gt1]].
  by case: ltngtP.
have [m n_eq_md]: {k : nat | n = (k * d)%N}.
  by exists (n %/ d)%N; rewrite [LHS](divn_eq _ d) (eqP dvd_dn) addn0.
have m_gt0 : (m > 0)%N.
  by move: n_gt0; rewrite !lt0n n_eq_md; apply: contra_neq => ->.
apply: (@rext_trans _ <<E; x ^+ d>>) => //.
  apply: (@IHk m (x ^+ d)) => //.
    by rewrite -exprM mulnC -n_eq_md//.
  by rewrite (leq_trans _ lenk)// n_eq_md ltn_Pmulr.
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

Lemma radicalext_Fadjoin_cyclotomic (E : {subfield L}) (r : L) (n : nat) :
  n.-primitive_root r -> radical.-ext E <<E; r>>%AS.
Proof.
move=> rprim; apply: (@radical_ext_Fadjoin n r E).
  exact: prim_order_gt0 rprim.
by rewrite (prim_expr_order rprim) mem1v.
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

Lemma abelian_radical_ext (F0 : fieldType) (L : splittingFieldType F0)
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
  exists (ExtData r_ [tuple of nseq n n]) => //; apply/forallP=> /= i.
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

Lemma solvableWradical_ext (E : {subfield L}) (F : {subfield L}) (r : L) :
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
move=> /prime_cyclic/cyclic_abelian/abelian_radical_ext/(_ Erm)-/(_ galEH)/=.
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
Hypothesis r_root : (n.-primitive_root r)%R.
Hypothesis solvable_G : solvable G.

Let subEF : (E <= F)%VS := galois_subW galois_EF.

Lemma galois_solvable_by_radical : solvable_by radical E F.
Proof.
pose G : {group gal_of F} := 'Gal(F / F :&: <<E; r>>%AS)%G.
have EEr := subv_adjoin E r.
rewrite /solvable_by; exists (F * <<E; r>>)%AS; last first.
  by rewrite field_subvMr; split.
apply: rext_trans (radicalext_Fadjoin_cyclotomic _ r_root) _.
have galErFEr: galois <<E; r>>%AS (F * <<E; r>>)%AS.
  by rewrite (@galois_prodvr _ _ E).
pose r' := r ^+ (n %/ #|G|).
have r'prim : #|G|.-primitive_root r'.
  by apply: dvdn_prim_root; rewrite // galois_dim ?cardSg ?galS ?subv_cap ?subEF.
have r'Er : r' \in <<E; r>>%VS by rewrite rpredX ?memv_adjoin.
apply: solvableWradical_ext r'Er _ => //=.
  rewrite (isog_sol (galois_isog galois_EF _))//.
  by apply: solvableS solvable_G; apply: galS; rewrite subv_cap subEF.
by rewrite galois_dim// (card_isog (galois_isog galois_EF _)).
Qed.

End Part1c.

(* Main lemma of part 1 *)
Lemma ext_solvable_by_radical (F0 : fieldType) (L : splittingFieldType F0)
    (r : L) (E F : {subfield L}) :
    [char L] =i pred0 -> (\dim_E (minGalois E F)).-primitive_root r ->
  solvable_ext E F -> solvable_by radical E F.
Proof.
move=> charL rprim /(galois_solvable_by_radical (minGalois_galois charL _ _)).
move=> /(_ r rprim) [M EM EFM]; exists M => //.
by rewrite (subv_trans _ EFM) ?sub_minGalois.
Qed.

End Part1.

(******************************************************************************)
(*                                                                            *)
(* Part 2 : solvable_by_radicals -> solvable                                  *)
(*                                                                            *)
(******************************************************************************)

Lemma radical_solvable_ext (F0 : fieldType) (L : splittingFieldType F0)
    (E F : {subfield L}) : [char L] =i pred0 -> (E <= F)%VS ->
  solvable_by radical E F -> solvable_ext E F.
Proof.
move: L E F => L' E' F' charL' EF'.
have charF0 : [char F0] =i pred0 by move=> i; rewrite -charL' char_lalg.
move=> [_ /pradicalext_radicalext[[/= n e' pw] /towerP epwP' <- FK']].
pose d := (\prod_(i < n) tnth pw i)%N.
have d_gt0 : (0 < d)%N.
  by rewrite prodn_gt0// => i; have /pradicalP[/prime_gt0]:= epwP' i.
have dF0N0: d%:R != 0 :> F0.
  rewrite natf_neq0; apply/pnatP => // p p_prime dvdpd; rewrite /negn/= inE/=.
  by rewrite -(char_lalg L') charL'.
(* classically grabbing a root of the unity and changing fields from L to L' *)
apply: (@classic_cycloSplitting _ L' _ dF0N0) => -[L [r [iota r_full r_root]]].
suff: solvable_ext (iota @: E') (iota @: F').
  rewrite /solvable_ext -aimg_minGalois// -img_map_gal.
  by rewrite injm_sol ?map_gal_inj ?subsetT.
set E := (iota @: E')%VS.
set F := (iota @: F')%VS.
pose e := [tuple of map iota e'].
pose K := <<E & e>>%VS.
have FK : (F <= <<E & e>>)%VS by rewrite -aimg_adjoin_seq limgS.
have EF : (E <= F)%VS by rewrite limgS.
have EK : (E <= K)%VS by apply: subv_trans FK.
have charL : [char L] =i pred0 by move=> x; rewrite char_lalg.
have epwP : forall i : 'I_n, pradical <<E & take i e>> (tnth e i) (tnth pw i).
  move=> i; have /pradicalP[pwi_prime e'i_rad] := epwP' i.
  apply/pradicalP; split; rewrite // -map_take -aimg_adjoin_seq.
  by rewrite tnth_map -rmorphX/= memv_img.
suff /(solvable_extP charL) [M /and3P[KrsubM EM solEM]] : solvable_ext E <<K; r>>%AS.
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
rewrite (solvable_ext_Fadjoin_prime charL prim _ _ _ pwk_prime)//.
  rewrite -[k]/(val ko) -tnth_nth; apply: subvP ekP.
  by apply: adjoin_seqSr => x xe; rewrite in_cons xe orbT.
by rewrite /= adjoin_cons rpredX// (subvP (subv_adjoin_seq _ _))// memv_adjoin.
Qed.

(******************************************************************************)
(*                                                                            *)
(* Abel/Galois Theorem                                                        *)
(*                                                                            *)
(******************************************************************************)

(** Ok **)
Lemma AbelGalois  (F0 : fieldType) (L : splittingFieldType F0) (r : L)
  (E F : {subfield L}) : (E <= F)%VS -> [char L] =i pred0 ->
  (\dim_E (minGalois E F)).-primitive_root r ->
  (solvable_by radical E F) <-> (solvable_ext E F).
Proof.
move=> EF charL rprim; split; first exact: radical_solvable_ext.
exact: (ext_solvable_by_radical _ rprim).
Qed.

End Abel.

Import GRing.Theory Order.Theory Num.Theory.

Open Scope ring_scope.

Module PrimeDegreeTwoNonRealRoots.
Section PrimeDegreeTwoNonRealRoots.

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

Lemma gal1 (g : gal_of K) : g \in 'Gal(K / 1%VS)%g.
Proof. by rewrite gal_kHom ?sub1v// k1HomE ahomWin. Qed.

Lemma gal_perm_eq (g : gal_of K) : perm_eq [seq g x | x <- trp] trp.
Proof.
apply: prod_XsubC_eq; rewrite -ratr_p big_map.
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

End PrimeDegreeTwoNonRealRoots.
End PrimeDegreeTwoNonRealRoots.
Module PDTNRR := PrimeDegreeTwoNonRealRoots.

Section Example1.

Definition poly_example_int : {poly int} := 'X^5 - 4%:R *: 'X + 2%:R%:P.
Definition poly_example : {poly rat} := 'X^5 - 4%:R *: 'X + 2%:R%:P.

Lemma poly_exampleEint : poly_example = map_poly intr poly_example_int.
Proof.
pose simp := (rmorphB, rmorphD, rmorphN, map_polyZ,
              map_polyXn, map_polyX, map_polyC).
by do !rewrite [map_poly _ _]simp/= ?natz.
Qed.

Lemma size_poly_exmpl_int : size poly_example_int = 6.
Proof.
rewrite /poly_example_int -addrA size_addl ?size_polyXn//.
by rewrite size_addl ?size_opp ?size_scale ?size_polyX ?size_polyC.
Qed.

Lemma size_poly_exmpl : size poly_example = 6.
Proof.
rewrite poly_exampleEint size_map_poly_id0 ?size_poly_exmpl_int//.
by rewrite intr_eq0 lead_coef_eq0 -size_poly_eq0 size_poly_exmpl_int.
Qed.

Lemma poly_exmpl_int_neq0 : poly_example_int != 0.
Proof. by rewrite -size_poly_eq0 size_poly_exmpl_int. Qed.

Lemma poly_example_neq0 : poly_example != 0.
Proof. by rewrite -size_poly_eq0 size_poly_exmpl. Qed.

Lemma poly_example_monic : poly_example \is monic.
Proof.
rewrite /poly_example monicE -addrA lead_coefDl ?lead_coefXn// size_polyXn ltnS.
rewrite (leq_trans (size_add _ _))//.
by rewrite size_polyC size_opp size_scale// size_polyX.
Qed.

Lemma irreducible_exmpl : irreducible_poly poly_example.
Proof.
pose coefE := (coefB, coefD, coefZ, coefC, coefX, coefXn).
rewrite poly_exampleEint; apply: (@eisenstein 2) => // [|||i];
  rewrite ?lead_coefE ?size_poly_exmpl_int ?coefE//.
by move: i; do 6!case=> //.
Qed.

Lemma separable_exmpl : separable_poly poly_example.
Proof.
apply/coprimepP => q /(irredp_XsubCP irreducible_exmpl) [//| eqq].
have size_deriv_exmpl : size poly_example^`() = 5.
  rewrite !derivCE addr0 alg_polyC -scaler_nat /=.
  by rewrite size_addl ?size_scale ?size_opp ?size_polyXn ?size_polyC.
by rewrite gtNdvdp -?size_poly_eq0 ?size_deriv_exmpl ?(eqp_size eqq) ?size_poly_exmpl.
Qed.

Lemma prime_exmpl : prime (size poly_example).-1.
Proof. by rewrite size_poly_exmpl. Qed.

(* Using the package real_closed, we should be able to monitor the sign of    *)
(* the derivative, and find that the polynomial has exactly three real roots. *)
(*** By Cyril ?                                                             ***)
Definition example_roots :=
  sval (closed_field_poly_normal ((map_poly ratr poly_example) : {poly algC})).

Lemma ratr_example_poly : map_poly ratr poly_example = \prod_(x <- example_roots) ('X - x%:P).
Proof.
rewrite /example_roots; case: closed_field_poly_normal => //= rs ->.
by rewrite lead_coef_map/= (eqP poly_example_monic) rmorph1 scale1r.
Qed.

Lemma deriv_poly_example : poly_example^`() = 5%:R *: 'X^4 - 4%:R%:P.
Proof. by rewrite /poly_example !derivE addr0 alg_polyC scaler_nat. Qed.

Definition alpha : algC := sqrtC (2%:R / sqrtC 5%:R).

Lemma root_deriv_poly_example (x : algC) : x \is Num.real ->
  (root (map_poly ratr poly_example^`()) x) = ((x == alpha) || (x == - alpha)).
Proof.
move=> x_real; rewrite deriv_poly_example /root.
rewrite rmorphB linearZ/= map_polyC/= map_polyXn.
rewrite hornerD hornerN hornerZ hornerXn hornerC !rmorph_nat.
rewrite -[5%:R]sqrtCK (exprM _ 2 2) -exprMn (natrX _ 2 2) subr_sqr.
rewrite mulf_eq0 orbC gt_eqF /=; last first.
  rewrite -[0](addr0) ler_lt_add// ?ltr0n//.
  by rewrite mulr_ge0// ?sqrtC_ge0 ?ler0n// real_exprn_even_ge0.
have sqrt5_neq0 : sqrtC (5%:R : algC) != 0.
  by rewrite gt_eqF// sqrtC_gt0 ?ltr0n.
rewrite subr_eq0 (can2_eq (mulKf _) (mulVKf _))// mulrC -subr_eq0.
by rewrite -[X in _ - X]sqrtCK -/alpha subr_sqr mulf_eq0 subr_eq0 addr_eq0.
Qed.

Lemma count_roots_ex : count (fun x => x \isn't Num.real) example_roots == 2.
Proof.
pose c := qe_rcf.CcountWeak [:: 2%:Q%:T; 4%:Q%:T; 0; 0; 1]%qfT
   [::] (fun t => t == 3%:Q%:T)%qfT.
(* Cannot compute c, takes too long... *)
Admitted.

(** No **)
(* An example of how it could feel to use the proposed statement              *)
Lemma example_not_solvable_by_radicals
  (L : splittingFieldType rat) (iota : {rmorphism L -> algC}) (K : {subfield L}) :
  splittingFieldFor 1%VS (map_poly ratr poly_example) K ->
  solvable_by radical 1%AS K -> False.
Proof.
have charL := char_ext L; rewrite -char0_ratrE; move=> [rs].
rewrite eqp_monic ?map_monic ?poly_example_monic ?monic_prod_XsubC//.
move=> /eqP poly_ex_eq_prod eqK.
have perm_rs : perm_eq (map iota rs) example_roots.
  apply: prod_XsubC_eq; rewrite big_map -ratr_example_poly; symmetry.
  rewrite -(eq_map_poly (fmorph_eq_rat [rmorphism of iota \o char0_ratr _])).
  rewrite map_poly_comp poly_ex_eq_prod rmorph_prod/=.
  by under eq_bigr do rewrite rmorphB/= map_polyX map_polyC/=.
have rs_uniq : uniq rs.
  by rewrite -separable_prod_XsubC -poly_ex_eq_prod separable_map separable_exmpl.
move=> /(radical_solvable_ext charL (sub1v _)) /=; rewrite -eqK.
have gal1rs : galois 1 <<1 & rs>> by apply: (@PDTNRR.galois1K _ iota poly_example).
rewrite /solvable_ext minGalois_id//.
have := PDTNRR.isog_gal_perm irreducible_exmpl rs_uniq poly_ex_eq_prod _.
move=> /(_ iota); rewrite size_poly_exmpl => /(_ isT)/(_ _)/isog_sol->//.
  by move=> /not_solvable_Sym; rewrite card_ord/=; apply.
have /eqP := count_roots_ex.
rewrite -size_filter -(perm_size (perm_filter _ perm_rs)).
by rewrite size_filter count_map => ->.
Qed.

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
  solvable_by radical 1%AS K <->
  {in root (map_poly ratr p), forall x, exists f : algformula, alg_eval f = x}.
Proof.
Admitted.

End Formula.

