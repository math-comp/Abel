From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import all_field finmap.
From Abel Require Import Sn_solvable galmx diag.
Import galmx.

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
Local Open Scope fset_scope.

Section missing_from_mathcomp.

Lemma dvdz_charf (R : ringType) (p : nat) :
  p \in [char R] -> forall n : int, (p %| n)%Z = (n%:~R == 0 :> R).
Proof.
move=> charRp [] n; rewrite [LHS](dvdn_charf charRp)//.
by rewrite NegzE abszN rmorphN// oppr_eq0.
Qed.

Lemma dvdp_ZXsubCX (R : idomainType) (p : {poly R}) (c : R) n :
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
  rewrite -['X]subr0; move=> /dvdp_ZXsubCX[k lekn]; rewrite subr0.
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

End missing_from_mathcomp.

Section RadicalExtension.

Variables (F0 : fieldType) (L : splittingFieldType F0).

Section Defs.

Implicit Types (U V : {subfield L}) (A : {fset L}).

(* Giving the parameters n and x in the definition makes it a boolean         *)
(* predicate which is useful as the tower property can be expressed as a path,*)
Definition radical N A U V := [exists x : A, exists n : 'I_N,
  [&& (n > 0)%N, val x ^+ n \in U & <<U; val x>>%AS == V]].

Lemma radicalP (N : nat) A U V :
  reflect (exists2 x : L, x \in A &
             exists n, [/\ (0 < n < N)%N, x ^+ n \in U & <<U; x>>%AS = V])
          (radical N A U V).
Proof.
apply: (iffP 'exists_'exists_and3P).
  move=> [x [n [lt0n Uxn /eqP UxeqV]]].
  by exists (val x) => //=; exists n; rewrite lt0n ltn_ord; split.
move=> [x Ax [n [/andP[lt0n ltnN] Uxn /eqP UxeqV]]].
by exists [` Ax], (Ordinal ltnN); split.
Qed.

Definition pradical N A U V := [exists x : A, exists p : 'I_N,
  [&& prime p, val x ^+ p \in U & <<U; val x>>%AS == V]].

Lemma pradicalP (N : nat) (A : {fset L}) (U V : {subfield L}) :
  reflect (exists2 x : L, x \in A &
             exists p, [/\ (p < N)%N, prime p, x ^+ p \in U & <<U; x>>%AS = V])
          (pradical N A U V).
Proof.
apply: (iffP 'exists_'exists_and3P).
  move=> [x [p [p_prime Uxp /eqP UxeqV]]].
  by exists (val x) => //=; exists p; rewrite p_prime ltn_ord; split.
move=> [x Ax [p [ltpN p_prime Uxp /eqP UxeqV]]].
by exists [` Ax], (Ordinal ltpN); split.
Qed.

Definition upstable (r : nat -> {fset L} -> rel {subfield L}) :=
  forall N N' A A', (N <= N')%N -> A `<=` A' -> subrel (r N A) (r N' A').

Definition extension (r : rel {subfield L}) := subrel r subsetv.

Lemma radical_upstable : upstable radical.
Proof.
move=> N N' A A' leNN' subAA' U V /radicalP.
move=> [x Ax [n [/andP[lt0n ltNN Uxn UxV]]]].
apply/radicalP; exists x; first exact: (fsubsetP subAA').
by exists n; split=> //; rewrite lt0n (leq_trans _ leNN').
Qed.

Lemma pradical_upstable : upstable pradical.
Proof.
move=> N N' A A' leNN' subAA' U V /pradicalP.
move=> [x Ax [p [ltpN p_prime Uxn UxV]]].
apply/pradicalP; exists x; first exact: (fsubsetP subAA').
by exists p; split=> //; rewrite (leq_trans _ leNN').
Qed.

(* n acts as an upper bound for the degree of the pure extension              *)
(* and A as the set used to extend U                                          *)
Definition tower (r : rel {subfield L}) := path r.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.

(* the quantification on n is useless as we directly have an upper bound      *)
Definition extension_pred (r : nat -> {fset L} -> rel {subfield L}) U V :=
  exists sU : seq {subfield L}, exists N, exists2 A,
    last U sU = V & (r N A).-tower U sU.

Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Definition solvable_by (r : nat -> {fset L} -> rel {subfield L}) (U V : {subfield L}) :=
  (U <= V)%VS /\ exists2 E : {subfield L}, r.-ext U E & (V <= E)%VS.

Definition solvable_by_radicals_poly (E F : {subfield L}) (p : {poly L}) :=
  splittingFieldFor E p F -> solvable_by radical E F.

End Defs.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.
Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Hint Resolve radical_upstable pradical_upstable : core.

Section Properties.

Implicit Type r : nat -> {fset L} -> rel {subfield L}.
Implicit Types (U V : {subfield L}) (A : {fset L}).

Lemma rext_refl r (E : {subfield L}) : r.-ext E E.
Proof. by exists [::], 0%N, fset0. Qed.

Lemma rext_r r N (A : {fset L}) (U V : {subfield L}) : r N A U V -> r.-ext U V.
Proof. by move=> rNAUV; exists [:: V], N, A => //=; rewrite andbT. Qed.

(* adding a field in the tower                                                *)
(* order of the variables E F K ?                                             *)
Lemma rext_r_trans r N A (E F K : {subfield L}) : upstable r ->
  r.-ext E F -> r N A F K -> r.-ext E K.
Proof.
move=> up_r [Vs [M [A' lastVsF rVs]]] rFK.
exists (rcons Vs K), (maxn N M), (A `|` A'); first by rewrite last_rcons.
rewrite /tower rcons_path (sub_path _ rVs)/=; last first.
  by apply: up_r; rewrite ?leq_maxr ?fsubsetUr.
by rewrite lastVsF; apply: up_r rFK; rewrite ?leq_maxl ?fsubsetUl.
Qed.

(* adding a tower                                                             *)
Lemma rext_trans r (E F K : {subfield L}) : upstable r ->
  r.-ext E F -> r.-ext F K -> r.-ext E K.
Proof.
move=> up_r rEF [Vs]; elim: Vs => [|V Vs IHVs] in F rEF *.
  by move=> [? [? <-]].
move=> [N [A /= VVsK /andP[rFV rVVs]]]; apply: (IHVs V).
  exact: rext_r_trans rFV.
by exists N, A.
Qed.

Lemma tower_subspace r N A E s : (forall N A, subrel (r N A) subsetv) ->
   (r N A).-tower E s -> (E <= last E s)%VS.
Proof.
move=> hsubspace; elim/last_ind: s=> [| s K ihs] //=.
rewrite last_rcons /tower rcons_path; move=> /andP[/ihs {} ihs].
by move=> /hsubspace; apply: subv_trans.
Qed.

Lemma radical_subspace N A : subrel (radical N A) subsetv.
Proof.
move=> U V /radicalP [x _ [n [_ _ <-]]].
by rewrite /= -adjoin_seq1 subv_adjoin_seq.
Qed.
Hint Resolve radical_subspace.

Lemma rext_subspace r : (forall N A, subrel (r N A) subsetv) ->
  forall E F, r.-ext E F -> (E <= F)%VS.
Proof.
by move=> rsub E F [Vs [N [A  <- /tower_subspace subEVs]]]; apply: subEVs.
Qed.

Lemma solvable_by_radicals_radicalext (E F : {subfield L}) :
  radical.-ext E F -> solvable_by radical E F.
Proof.
move=> extEF; split; last by exists F.
exact: (@rext_subspace radical).
Qed.

Lemma radical_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  (0 < n)%N -> x ^+ n \in E -> radical n.+1 [fset x]%fset E <<E; x>>%AS.
Proof.
move=> n_gt0 Exn; apply/radicalP; exists x; rewrite ?inE//.
by exists n; rewrite leqnn n_gt0; split.
Qed.

Lemma pradical_Fadjoin (p : nat) (x : L) (E : {subfield L}) :
  prime p -> x ^+ p \in E -> pradical p.+1 [fset x]%fset E <<E; x>>%AS.
Proof.
move=> prime_p Exn; apply/pradicalP; exists x; rewrite ?inE//.
by exists p; rewrite leqnn; split.
Qed.

Lemma radical_ext_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  (0 < n)%N -> x ^+ n \in E -> radical.-ext E <<E; x>>%AS.
Proof. by move=> n_gt0 Exn; apply/rext_r/(radical_Fadjoin n_gt0 Exn). Qed.

Lemma pradical_ext_Fadjoin (p : nat) (x : L) (E : {subfield L}) :
  prime p -> x ^+ p \in E -> pradical.-ext E <<E; x>>%AS.
Proof. by move=> p_prime Exn; apply/rext_r/(pradical_Fadjoin p_prime Exn). Qed.

Lemma pradical_radical N A : subrel (pradical N A) (radical N A).
Proof.
move=> U V /pradicalP[x Ax [p [ltpN p_prime Uxp UxV]]].
by apply/radicalP; exists x => //; exists p; rewrite prime_gt0//.
Qed.

Lemma pradicalext_radical N A (E F : {subfield L}) :
  radical N A E F -> pradical.-ext E F.
Proof.
move=> /radicalP[x Ax [n [/andP[n_gt0 ltnN Exn <-{F}]]]].
have [k] := ubnP n; elim: k => // k IHk in n n_gt0 ltnN x A Ax E Exn *.
rewrite ltnS => lenk.
have [n_prime|/primePn[]] := boolP (prime n).
- by apply: (@pradical_ext_Fadjoin n).
- case: n {ltnN lenk} => [|[]]// in Exn n_gt0 * => _.
  suff -> :  <<E; x>>%AS = E by apply: rext_refl.
  by apply/val_inj => /=; rewrite (Fadjoin_idP _).
move=> [d /andP[d_gt1 d_ltn /dvdnP[m n_eq_md]]].
have m_gt0 : (m > 0)%N.
  by move: n_gt0; rewrite !lt0n n_eq_md; apply: contra_neq => ->.
apply: (@rext_trans _ _ <<E; x ^+ d>>) => //.
  apply: (@IHk m _ _ _ (x ^+ d |` A)) => //.
  - by rewrite (leq_trans _ ltnN)// ltnS n_eq_md leq_pmulr ?(leq_trans _ d_gt1).
  - by rewrite !inE eqxx.
  - by rewrite -exprM mulnC -n_eq_md//.
  - by rewrite (leq_trans _ lenk)// n_eq_md ltn_Pmulr.
suff -> : <<E; x>>%AS = <<<<E; x ^+ d>>; x>>%AS.
  apply: (IHk d _ _ _ A) => //.
  - by rewrite (leq_trans _ d_gt1)//.
  - by rewrite (leq_trans _ ltnN)// ltnS n_eq_md leq_pmull.
  - by rewrite memv_adjoin.
  - by rewrite (leq_trans _ lenk).
apply/val_inj; rewrite /= adjoinC [<<_; x ^+ d>>%VS](Fadjoin_idP _)//.
by rewrite rpredX// memv_adjoin.
Qed.

Lemma radicalext_pradicalext (E F : {subfield L}) :
  radical.-ext E F <-> pradical.-ext E F.
Proof.
split=> [] [Vs [N [A EVsF pVs]]]; last first.
  by exists Vs, N, A => //; apply: sub_path pVs; apply: pradical_radical.
elim: Vs E EVsF pVs => [|V Vs IHVs/= E EVsF /andP[EVs pVs]].
  by move=> ? <- *; exact: rext_refl.
by apply: rext_trans (IHVs V _ _) => //; apply: pradicalext_radical EVs.
Qed.

Lemma solvable_by_radical_pradical (E F : {subfield L}) :
  solvable_by pradical E F <-> solvable_by radical E F.
Proof. by split=> -[EF [R /radicalext_pradicalext]]; split => //; exists R. Qed.

(** Ok **) (* but painful *)
(* Exposing the list of exponents, and elements                               *)
Lemma radicalext_explicit_parameters E F : radical.-ext E F ->
  exists n : nat, exists tn : nat ^ n, exists2 tx : L ^ n,
    (\prod_(i < n) tn i = \dim_E F)%N
    & (F == <<E & codom tx >>)%AS &&
      [forall i : 'I_n, prime i && radical (\max_i (tn i).+1) [fset tx i | i in 'I_n]
      <<E & (take i (codom tx))>> <<E & (take i.+1 (codom tx))>>].
Proof.
move=> [Vs [N [A ]]]; elim: Vs => [|V Vs IHVs] in E F N A * => [<-|].
  exists 0%N, [ffun=> 0%N], [ffun=> 0]; rewrite ?divnn ?adim_gt0 ?big_ord0//.
  apply/andP; split; [apply/eqP/val_inj => /=|apply/forallP => -[]//].
  rewrite [codom _]size0nil ?size_codom ?card_ord//.
  by rewrite adjoin_nil ?subfield_closed.
move=> /= VVsF /andP[/radicalP[x Ax [n [/andP[n_gt0 ltnN Exn ExV]]]]].
move=> /(IHVs _ F N A VVsF)[k [tn [tx prod_tn /andP[/eqP F_eq]]]].
Admitted.

(** Easy **)
Lemma solvable_by_radical_explicit_parameters E F :
  solvable_by radical E F <-> (exists n : nat, exists tn : nat ^ n,
  exists2 tx : L ^ n, (F <= <<E & (fgraph tx)>>)%VS & [forall i : 'I_n, prime i
  && radical (\max_i tn i) [fset tx i | i in 'I_n]
             <<E & (take i (fgraph tx))>>
             <<E & (take i.+1 (fgraph tx))>>]).
Proof.
Admitted.

End Properties.

End RadicalExtension.

Arguments tower {F0 L}.
Arguments extension_pred {F0 L}.
Arguments radical {F0 L}.

(* splitting field properties *)
Section Splitting.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (E F : {subfield L}) (p : {poly L}).
Hypothesis splitting_p : splittingFieldFor E p F.

(** Easy **)
Lemma subv_splittingFieldFor : (E <= F)%VS.
Proof. case: splitting_p => b pE <-; exact: subv_adjoin_seq. Qed.

(** Ok **)
Lemma root_make_separable x : [char L] =i pred0 -> root p x = root (p %/ gcdp p p^`()) x.
Proof.
move=> charL; have [->|p_neq0] := eqVneq p 0; first by rewrite div0p root0.
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

(** looks wrong! **)
(* Lemma galois_splittingFieldFor : galois E F. *)
(* Proof. *)
(* apply/splitting_galoisField. *)
(* exists p. *)
(* rewrite /galois. *)

(* from definition : *)
(* for the separable part : with minPoly_dvdp, dvdp_separable,*)
(* root_make_separable and make_separable, minPoly is separable so every root *)
(* of p is a separable_element *)
(* for the normal part : directly splitting_normalField *)
(* Admitted. *)

End Splitting.

(* (* transitivity *) *)
(* (* Looks wrong, but useless *) *)
(* Section Transitivity. *)
(* Variables (F0 : fieldType) (L : splittingFieldType F0). *)
(* Variables (E F K : {subfield L}). (* should this be E K and M ? *) *)
(* Hypothesis subvs_EFK : (E <= F <= K)%VS. *)

(* (** Completely wrong **) *)
(* Lemma normalField_trans : normalField E F -> normalField F K -> normalField E K. *)
(* Proof. *)
(* (* using, for example, splitting_normalField *) *)
(* Admitted. *)

(* (** Wrong too **) *)
(* Lemma galois_trans : galois E F -> galois F K -> galois E K. *)
(* Proof. *)
(* (* using the lemma above and the transitivity of separable *) *)
(* Admitted. *)

(* End Transitivity. *)

(* cyclotomic extensions                                                      *)
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

Section Prodv.

Variables (F0 : fieldType) (L : splittingFieldType F0).

(** N/A **)
Lemma galois_prodv (k K F : {subfield L}) :
  galois k K -> (k <= F)%VS -> galois F (K * F).
Proof.
move=> /splitting_galoisField [p [pk p_sep [rs p_eq krs]]] kF.
apply/splitting_galoisField; exists p; split => //.
  by apply: polyOverS pk => x; apply: subvP.
exists rs => //; apply/eqP; rewrite eqEsubv; apply/andP; split.
  apply/Fadjoin_seqP; rewrite field_subvMl; split => //= r rrs.
  by apply: (subvP (field_subvMr _ _)); rewrite -krs seqv_sub_adjoin.
apply/prodvP => x y xK yF; rewrite rpredM//; last first.
  by rewrite (subvP (subv_adjoin_seq _ _))//.
by rewrite -krs in xK; apply: subvP xK; apply: adjoin_seqSl.
Qed.

(** N/A **)
Lemma capv_galois (k K F : {subfield L}) :
  galois k K -> (k <= F)%VS -> galois (K :&: F) K.
Proof.
move=> /splitting_galoisField [p [pk p_sep [rs p_eq krs]]] kF.
have k_subKF: (k <= K :&: F)%VS.
  apply/subvP => x xk.
  by rewrite memv_cap (subvP kF)// -krs (subvP (subv_adjoin_seq _ _)).
apply/splitting_galoisField; exists p; split => //.
  by apply: polyOverS pk; apply/subvP.
exists rs => //; apply/eqP; rewrite -krs eqEsubv andbC adjoin_seqSl//=.
by apply/Fadjoin_seqP; split; [rewrite /= krs capvSl|apply: seqv_sub_adjoin].
Qed.

(** N/A **)
(* Do we need to know that the iso is the restriction morphism? *)
Import AEnd_FinGroup.
Lemma galois_iso (k K F : {subfield L})
  (H := 'Gal((K * F) / F)%g) (G := 'Gal(K / k)%g) (H' := 'Gal ((K :&: F) / K)%g) :
  galois k K -> (k <= F)%VS -> H \isog H'.
Proof.
move=> K_galois sub_k_F.
pose r (g : gal_of (K * F)) : gal_of (K :&: F) := gal _ (gal_repr g).
have r_H_morphic : morphic H r.
  apply/morphicP => u v uH vH.
  admit.
apply/(@misom_isog _ _ _ _ r)/misomP; exists r_H_morphic.
admit.
Admitted.

End Prodv.

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
have subv_EF : (E <= F)%VS by case/andP: galois_EF.
have n_gt0 : (n > 0)%N by rewrite /n -dim_aspaceOver ?adim_gt0.
have asimp := (mem_aspaceOver, subv_adjoin_seq).
suff [/= r_ /andP[r_basis /allP r_F] m_r {abelian_G}] :
     exists2 r_ : n.-tuple L,
       basis_of (aspaceOver E F) (r_ : seq (fieldOver E)) && all (mem F) r_ &
         forall i m, m \in G -> exists2 l, (l \in E) && (l ^+ n == 1)
                                           & m (tnth r_ i) = l * tnth r_ i.
  pose R := [fset x in val r_]; pose f i := <<E & take i r_>>%AS.
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
  pose fs := [seq f i | i <- iota 1 n]; exists fs, n.+1, R.
    rewrite -f0E last_map/= -(subnK n_gt0) iota_add cats1 last_rcons subnKC//.
    by rewrite /f take_oversize ?size_tuple//; apply/val_inj.
  have fsi j : nth F fs j = <<E & take j.+1 r_>>%VS :> {vspace _}.
    have [lt_jn|ge_jn] := ltnP j n; last first.
      by rewrite nth_default ?take_oversize ?size_tuple// leqW.
    by rewrite (nth_map n) ?size_iota// nth_iota.
  have fsEi j : nth F (E :: fs) j = <<E & take j r_>>%VS :> {vspace _}.
      by case: j => //=; rewrite -[in LHS]f0E//.
  apply/(pathP F) => i; rewrite size_map size_iota => lti.
  apply/radicalP; exists (r_`_i); first by rewrite inE mem_nth ?size_tuple.
  exists n; rewrite n_gt0 leqnn fsEi; split => //; last first.
    by apply/val_inj; rewrite /= -adjoin_rcons -take_nth ?size_tuple.
  suff: r_`_i ^+ n \in fixedField G.
    by rewrite (galois_fixedField _)//; apply/(subvP (subv_adjoin_seq _ _)).
  apply/fixedFieldP; first by rewrite rpredX ?[_ \in _]r_F ?mem_nth ?size_tuple.
  move=> g /(m_r (Ordinal lti))[l /andP[lE /eqP lX1]].
  by rewrite (tnth_nth 0) rmorphX/= => ->; rewrite exprMn lX1 mul1r.
pose LE := [fieldExtType subvs_of E of fieldOver E].
have [e e_basis] : { e : n.-1.+1.-tuple _ | basis_of (aspaceOver E F) e}.
  rewrite prednK//; have := vbasisP (aspaceOver E F); move: (vbasis _).
  by rewrite dim_aspaceOver// => e; exists e.
have e_free := basis_free e_basis.
have Gminpoly g : g \in G -> mxminpoly (mxof e g) %| 'X ^+ n - 1.
  move=> gG; rewrite mxminpoly_min// rmorphB rmorph1 rmorphX/= horner_mx_X.
  apply: (canLR (addrK _)); rewrite add0r -mxofX//.
  by rewrite [n]galois_dim// expg_cardG// mxof1.
have [p p_unit dG] : codiagonalisable [seq mxof e g | g in G].
  apply/codiagonalisableP; split.
    apply/all_commP => _ _ /mapP[g gG ->] /mapP[g' g'G ->].
    rewrite ?mem_enum in gG g'G.
    by rewrite -![_ *m _]mxofM// (centsP abelian_G).
  move=> _/mapP[g gG ->]; rewrite mem_enum in gG *.
  pose l := [seq Subvs r_in_E ^+ i | i <- index_iota 0 n].
  apply/diagonalisableP; exists l.
    rewrite map_inj_in_uniq ?iota_uniq//.
    move=> x y; rewrite !mem_index_iota !leq0n/= => x_n y_n.
    move=> /(congr1 val)/=/eqP; rewrite !rmorphX/=.
    by rewrite (eq_prim_root_expr r_is_nth_root) !modn_small// => /eqP.
  rewrite big_map (@factor_Xn_sub_1 _ _ (Subvs r_in_E)) ?Gminpoly//.
  by rewrite /= -(fmorph_primitive_root [rmorphism of vsval]).
pose r_ := [tuple vecof e (row i p) | i < n.-1.+1].
rewrite -[n]prednK//; exists r_.
  apply/andP; split; last by apply/allP => _ /mapP[/=i _ ->]; rewrite vecof_in.
  rewrite basisEdim; apply/andP; split; last first.
    by rewrite size_tuple dim_aspaceOver// prednK.
  apply/subvP => x /=; rewrite mem_aspaceOver// => xEF.
  have [l ->] : exists l, x = vecof e (l *m p).
    by exists (rowmxof e x *m invmx p); rewrite mulmxKV ?rowmxofK.
  rewrite span_def big_map big_enum_cond/= mulmx_sum_row linear_sum/=.
  by  apply: memv_sumr => i _; rewrite linearZ/= [_ \in _]memvZ// memv_line.
move=> i g gG; have /allP /(_ (mxof e g) (map_f _ _))/sim_diagPex := dG.
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
rewrite !mulmxA -!rowE row_diag_mx -scalemxAl -rowE => /(congr1 (vecof e)).
by rewrite vecofM// linearZ/= tnth_map tnth_ord_tuple.
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
move=> /rext_trans; apply; first exact: radical_upstable.
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
Hypothesis subv_EF : (E <= F)%VS.
Local Notation G := ('Gal(F / E)%g).
Local Notation n := (\dim_E F).
Variable (r : L).
Hypothesis r_is_nth_root : (n.-primitive_root r)%R.

(* Part 1c : *)
(* If : *)
(* - G is solvable *)
Hypothesis solvable_G : solvable G.

Local Notation F' := (<<E; r>> * F)%AS.

(** N/A **)
(*** the prodv part must be proven/modified before attempting this ***)
(* We want to prove that F is solvable by radicals on E                       *)
Lemma part1c : solvable_by radical E F.
Proof.
(* - Let E' = E(r) where r is an n-th root of the unity *)
(* - E'/E is then Galois (galois_Fadjoin_cyclotomic) *)
(* - Let F' = E'F *)
(* - F' is Galois over E' *)
(* - Gal(F'/E') is isomorphic to a subgroup of G *)
(* - Gal(F'/E') is thus solvable *)
(* - F' is solvable by radicals on E' (Part1b) *)
(* - F' is solvable by radicals on E (transitivity) *)
(* - F <= F' so F is solvable by radicals *)
Admitted.

End Part1c.

(** Ok **)
(* Main lemma of part 1 *)
(* there is the problem of the nth-root which must be present in the big field L
to resolve here, but here is a first suggestion *)
Lemma part1 (F0 : fieldType) (L : splittingFieldType F0)
      (E F : {subfield L}) (p : {poly L}) :
  let n := (\dim_E F) in
  (exists r : L, (n.-primitive_root r)%R) -> splittingFieldFor E p F ->
  solvable 'Gal(F / E) -> solvable_by radical E F.
Proof.
Admitted.

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
Hypothesis prime_p : prime p.
Hypothesis r_is_pth_root : (p.-primitive_root r)%R.
Hypothesis x_notin_E : x \notin E.
Hypothesis xp_in_E : (x ^+ p)%R \in E.
Local Notation G := ('Gal(<<E; x>> / E))%g.

Section Part2a.
(* We want to prove that E(x) is Galois and abelian                           *)

(** Easy **)
(* - the roots of X^p - x^p are the x * a p-th root of the unity              *)
Lemma root_Xp_sub_xp (i : 'I_p) : root ('X^p - x%:P) ((x * r) ^+ i)%R.
Proof.
Admitted.

(** Hard **)
Lemma size_Fadjoin_prime : size (minPoly E x) = p.+1.
Proof.
(* using a decomposition of minPoly in linear terms : its constant *)
(* coefficient is a power of x, and in E : it can only be at power p, hence *)
(* its size *)
Admitted.

(** Ok **)
(* - E(x) is the splitting field of X^p - x^p                                 *)
Lemma minPoly_Fadjoin_prime : minPoly E x = ('X^p - (x ^+ p)%:P)%R.
Proof.
Admitted.

(** Ok **)
(* - E(x) is thus Galois                                                      *)
Lemma galois_Fadjoin_prime : galois E <<E; x>>.
(* using separable (separable_Fadjoin_seq & charf0_separable) *)
(* and probably normalFieldP *)
Proof.
Admitted.

(** Easy **)
(* - Gal(E(x) / E) has order p                                                *)
Lemma order_galois_Fadjoin_prime : #|G| = p.
Proof.
(* using galois_dim and minPoly_Fadjoin_prime *)
Admitted.

(** Easy **)
(* - Gal(E(x) / E) is cyclic                                                  *)
(* - Gal(E(x) / E) is abelian                                                 *)
(* (end of part2a)                                                            *)
Lemma abelian_Fadjoin_prime : abelian G.
Proof.
(* using prime_cyclic & cyclic_abelian *)
Admitted.

End Part2a.

(** Ok **)
(* in the same context, we can prove a lemma for the next step (part 2b)      *)
(* in the recurrence :                                                        *)
(* - Let Fi = K(x0,..,xi) and Gi = Gal(Fi / K)                                *)
(*   - i >= 0 :                                                               *)
(*     - we suppose that Fi is Galois and solvable                            *)
(*     - Fi+1 / Fi is Galois and its Galois group H is abelian (part2a)       *)
(*     - Fi+1 / K is Galois                                                   *)
(*     - Gi+1 = Gi x| H                                                       *)
(*     - Gi+1 is solvable                                                     *)
Lemma solvable_gal_Fadjoin_prime (F : {subfield L}) :
  r \in F -> galois F E -> solvable 'Gal(E / F) ->
  galois F <<E; x>> /\ solvable 'Gal(<<E; x>> / F).
Proof.
(* E(x) is galois over E (galois_Fadjoin_prime) *)
(* its galois group is abelian (abelian_Fadjoin_prime) *)
(* by transitivity, E(x) is galois over F (its galois group is solvable *)
(* Gal(E/F) is isomorphic to Gal(E(x)/F) / Gal(E(x)/E) *)
(* Gal(E(x)/E) <| Gal(E(x)/F) *)
(* Gal(E(x)/E) is abelian thus solvable *)
(* Gal(E(x)/F) is solvable (series_sol) *)
Admitted.

End IntermediateLemmas.

Section Part2b.

(* Let F be a finite extension of E                                           *)
Variables (E F : {subfield L}) (P : {poly L}) (n : nat).
Variables (tn : nat ^ n) (tx : L ^ n) (r : L).
Hypothesis galois_EF : galois E F.
Hypothesis subv_EF : (E <= F)%VS.
Hypothesis prime_tn : forall i, prime (tn i).
Hypothesis subv_FEtx : (F <= <<E & (fgraph tx)>>)%VS.
Hypothesis radical_Ei : forall i, radical (\max_i tn i) [fset tx i | i in 'I_n]
  <<E & (take i (fgraph tx))>> <<E & (take i.+1 (fgraph tx))>>.

(* - we can also add an m0 = (m1*..*mn)-th root of the unity at the beginning *)
Local Notation m := (\prod_(i < n) tn i)%N.
Hypothesis r_is_mth_root : (m.-primitive_root r)%R.

Local Notation Ei i := <<<<E; r>> & (take i (fgraph tx))>>%VS.
Local Notation Gi i := ('Gal(Ei i / E))%g.

(** Ok **)
(* - we proceed by recurrence on n, by proving that each extension E(x0..xn)  *)
(*   of E is Galois and its Galois group is solvable.                         *)
Lemma galois_solvable_Fadjoin_seq : galois E (Ei n) && solvable (Gi n).
Proof.
(* - by Galois, E(x0,..,xn) is Galois over E (recurrence step on n) *)
(* using the cyclotomic extension for the initial step *)
(* using solvable_gal_Fadjoin_prime_galois for the step *)
Admitted.

(** Ok **)
Lemma solvable_gal_Fadjoin_seq : solvable 'Gal(F / E).
Proof.
(* - Gal(F/E) is isomorphic to Gal(E(x0,..,xn)/E) / Gal(E(x0,..,xn)/F) *)
(* - then, Gal(F/E) is also solvable (quotient_sol) *)
Admitted.

End Part2b.

(** No **)
(* Main lemma of part 2 *)
(* there is still the problem of the nth-root... but I don't know how to resolve it
here, as I don't see how we can explicitly get an upper_bound (which would be
enough) for the value of n *)
(* a solution would be to explicitly give an upper bound in solvable_by_radicals *)
Lemma part2 (E F : {subfield L}) (p : {poly L}) :
  splittingFieldFor E p F -> solvable_by radical E F -> solvable 'Gal(F / E).
Proof.
Admitted.

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
  exists (r : L), (#|'Gal(F / E)|%g).-primitive_root r ->
  radical.-ext E F <-> solvable 'Gal (F / E).
Proof.
Admitted.

End Abel.



















Section Examples.


Import GRing.Theory Num.Theory.

Open Scope ring_scope.


Variable (L : splittingFieldType rat).
Variable (K : {subfield L}).

Section Example1.

Variable p : {poly rat}.
Variable C : numClosedFieldType.

Hypothesis K_split_p : splittingFieldFor 1%AS (map_poly ratr p) K.
Hypothesis p_sep : separable_poly p.
Hypothesis p_irr : irreducible_poly p.

Let d := (size p).-1.
Hypothesis d_prime : prime d.

Let rp := sval (closed_field_poly_normal ((map_poly ratr p) : {poly C})).
Hypothesis count_roots_p : count (fun x => x \isn't Num.real) rp == 2.

(** Easy **)
Lemma rp_roots : all (root (map_poly ratr p)) rp.
Proof.
Admitted.

(** N/A **)
(* This lemma should be divided into smaller parts                            *)
Definition pre_gal_perm (g : gal_of K) (i : 'I_d) : 'I_d.
Admitted.

(** N/A **)
Lemma gal_perm_is_perm (g : gal_of K) : injectiveb (finfun (pre_gal_perm g)).
Proof.
Admitted.

Definition gal_perm (g : gal_of K) := Perm (gal_perm_is_perm g).


(** N/A **)
Lemma injective_gal_perm : injective gal_perm.
Proof.
Admitted.

(** N/A **)
Lemma gal_perm_is_morphism :
  {in ('Gal(K / 1%AS))%G &, {morph gal_perm : x y / (x * y)%g >-> (x * y)%g}}.
Proof.
Admitted.

Canonical gal_perm_morphism :=  Morphism gal_perm_is_morphism.


(** N/A **)
Lemma injm_gal_perm : ('injm gal_perm)%g.
Proof.
Admitted.


(** N/A **)
(* Here it should also be divided                                             *)
Definition gal_orderd : gal_of K.
Admitted.

(** N/A **)
Lemma gal_orderp_orderd : #[gal_orderd]%g = d.
Proof.
Admitted.

(** N/A **)
Lemma permp_orderd : #[(gal_perm gal_orderd)]%g = d.
Proof.
(* morph_order & d_prime *)
Admitted.



(** N/A **)
(* Using the 2 complex roots                                                  *)
Definition gal_order2 : gal_of K.
Admitted.

(** N/A **)
Lemma gal_order2_order2 : #[gal_order2]%g = 2.
Proof.
Admitted.

(** N/A **)
Lemma perm2_order2 : #[(gal_perm gal_order2)]%g = 2.
Proof.
Admitted.



(* Missing lemma :                                                            *)
(* Sp is generated by a p-cycle and a transposition : how to state it ?       *)



(** N/A **)
Lemma surj_gal_perm : (gal_perm @* 'Gal (K / 1%AS) = 'Sym_('I_d))%g.
Proof.
Admitted.



(** N/A **)
Lemma isog_gal_perm : 'Gal (K / 1%AS) \isog ('Sym_('I_d)).
Proof.
(* isogP, surj_gal_perm & injm_gal_perm *)
Admitted.


End Example1.

(** N/A **)
(* I think this lemma is quite close to the mathematical statement :          *)
(* Let P be an irreducible polynomial with rational coefficients, separable   *)
(* and of degree p prime. If P has precisely two nonreal roots in the complex *)
(* numbers, then the Galois group of P is Sp                                  *)
Lemma example1 (p : {poly rat}) (C : numClosedFieldType) :
  splittingFieldFor 1%AS (map_poly ratr p) K ->
  separable_poly p ->
  irreducible_poly p ->
  let d := (size p).-1 in prime d ->
  let rp := sval (closed_field_poly_normal ((map_poly ratr p) : {poly C})) in
  count (fun x => x \isn't Num.real) rp == 2 ->
  'Gal (K / 1%AS) \isog ('Sym_('I_d)).
Proof.
(* We could split this lemma in smaller steps (which may be generalized) :    *)
(*   - constructing a function from the Galois group to the permutations      *)
(*   - showing it is injective                                                *)
(*   - showing it is a group morphism                                         *)
(*   - there is an element of order d in its image                            *)
(*   - there is a transposition in its image (with the nonreal roots)         *)
(*   - Sd is generated by any d-cycle and a transposition (this may already   *)
(*       exists, but I don't know where)                                      *)
(* See Section Example1 just above for a first draft of the steps             *)
Admitted.

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

(** N/A : Cyril ? **)
(* Usually, this is done with Eisenstein's criterion, but I don't think it is *)
(* already formalized in mathcomp                                             *)
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
Lemma example_not_solvable_by_radicals :
  splittingFieldFor 1%AS (map_poly ratr poly_example) K ->
  ~ solvable_by radical 1%AS K.
Proof.
(* The statement of the theorem has changed : problem with the nth-root *)
(*move=> K_splitP; rewrite (AbelGalois K_splitP).
have := (example1 K_splitP separable_ex irreducible_ex prime_ex count_roots_ex).
by move/isog_sol => ->; apply: not_solvable_Sym; rewrite card_ord size_poly_ex.
Qed.*)
Admitted.


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

End Examples.
