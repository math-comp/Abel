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

(* missing from coq or mathcomp *)
Inductive iffT T1 T2 : Type := Record {iffT12 : T1 -> T2 ; iffT21 : T2 -> T1}.
Notation "T1 <=> T2" := (iffT T1 T2) (at level 95) : type_scope.

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

Lemma lead_coef_XnsubC {R : ringType} n (c : R) : (0 < n)%N ->
  lead_coef ('X^n - c%:P) = 1.
Proof.
move=> gt0_n; rewrite lead_coefDl ?lead_coefXn //.
by rewrite size_opp size_polyC size_polyXn ltnS (leq_trans (leq_b1 _)).
Qed.

Lemma lead_coef_XsubC {R : ringType} (c : R) :
  lead_coef ('X - c%:P) = 1.
Proof. by apply: (@lead_coef_XnsubC _ 1%N). Qed.


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

(* rename primeNsig? *)
Lemma primePn (n : nat) : ~~ prime n -> (2 <= n)%N ->
  { d : nat | (1 < d < n)%N & (d %| n)%N }.
Proof.
move=> primeN_n le2n; case/pdivP: {+}le2n => d /primeP[lt1d prime_d] dvd_dn.
exists d => //; rewrite lt1d /= ltn_neqAle dvdn_leq 1?andbT //; last first.
  by apply: (leq_trans _ le2n).
by apply: contra primeN_n => /eqP <-; apply/primeP.
Qed.

Lemma adjoin_cat
    (K : fieldType) (aT : FalgType K) (V : {vspace aT}) (rs1 rs2 : seq aT)
  : <<V & rs1 ++ rs2>>%VS = <<<<V & rs1>> & rs2>>%VS.
Proof.
elim: rs1 => /= [|r rs1 ih] in V *.
- by rewrite adjoin_nil agenv_add_id.
- by rewrite !adjoin_cons ih.
Qed.

Lemma eq_adjoin (K : fieldType) (aT : FalgType K) (U : {vspace aT})
    (rs1 rs2 : seq aT) :
  rs1 =i rs2 -> (<<U & rs1>> = <<U & rs2>>)%VS.
Proof.
by move=> rs12; apply/eqP; rewrite eqEsubv !adjoin_seqSr// => x; rewrite rs12.
Qed.

(* turn into a reflect before adding to mathcomp? *)
Lemma Fadjoin_seq_idP
    (F0 : fieldType) (L : fieldExtType F0) (K : {subfield L}) (xs : seq L)
  : all (mem K) xs -> <<K & xs>>%VS = K.
Proof.
elim: xs => /= [|x xs ih]; first by  rewrite Fadjoin_nil.
by case/andP=> xK {}/ih ih; rewrite adjoin_cons (Fadjoin_idP _).
Qed.

Lemma tnth_lshift {T : Type} {n1 n2} (t1 : n1.-tuple T) (t2 : n2.-tuple T) (i : 'I_n1) :
  tnth [tuple of t1 ++ t2] (lshift n2 i) = tnth t1 i.
Proof.
have x0 := tnth_default t1 i; rewrite !(tnth_nth x0).
by rewrite nth_cat size_tuple /= ltn_ord.
Qed.

Lemma tnth_rshift {T : Type} {n1 n2} (t1 : n1.-tuple T) (t2 : n2.-tuple T) (i : 'I_n2) :
  tnth [tuple of t1 ++ t2] (rshift n1 i) = tnth t2 i.
Proof.
have x0 := tnth_default t2 i; rewrite !(tnth_nth x0).
by rewrite nth_cat size_tuple ltnNge leq_addr /= addKn.
Qed.

End missing_from_mathcomp.

Section RadicalExtension.

Variables (F0 : fieldType) (L : splittingFieldType F0).

Section Defs.

Implicit Types (U V : {vspace L}).

Definition radical U x n := [&& (n > 0)%N & x ^+ n \in U].

Lemma radicalP U x n :
  reflect
    [/\ (n > 0)%N & x ^+ n \in U]
    [&& (n > 0)%N & x ^+ n \in U].
Proof. exact: andP. Qed.

Definition pradical U x p := [&& prime p & x ^+ p \in U].

Lemma pradicalP U x p :
  reflect
    [/\ prime p & x ^+ p \in U]
    [&& prime p & x ^+ p \in U].
Proof. exact: andP. Qed.

Implicit Types r : {vspace L} -> L -> nat -> bool.

Definition tower r n U (e : n.-tuple L) (pw : n.-tuple nat) :=
  [forall i : 'I_n, r << U & take i e >>%VS (tnth e i) (tnth pw i)].

Lemma towerP r n U (e : n.-tuple L) (pw : n.-tuple nat) :
  reflect
    (forall i : 'I_n, r << U & take i e >>%VS (tnth e i) (tnth pw i))
    (tower r U e pw).
Proof. exact: forallP. Qed.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.

Inductive extension_pred r U V : Type :=
| Extension n (e : n.-tuple L) (pw : n.-tuple nat) of
    << U & e >>%VS = V & r.-tower n U e pw.

Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Definition ep_size r U V (h : r.-ext U V) : nat :=
  let: Extension n _ _ _ _ := h in n.

Definition ep_e r U V (h : r.-ext U V) : (ep_size h).-tuple L :=
  let: Extension _ e _ _ _ := h in e.

Definition ep_pw r U V (h : r.-ext U V) : (ep_size h).-tuple nat :=
  let: Extension _ _ pw _ _ := h in pw.

Definition solvable_by r (U V : {subfield L}) : Type :=
  { E : {subfield L} & ((r.-ext U E) * (V <= E)%VS)%type }.

Definition solvable_by_radicals_poly (E F : {subfield L}) (p : {poly L}) :=
  splittingFieldFor E p F -> solvable_by radical E F.

End Defs.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.
Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Section Properties.

Implicit Types r : {vspace L} -> L -> nat -> bool.
Implicit Types (U V : {subfield L}) (A : {fset L}).

Lemma rext_refl r (E : {subfield L}) : r.-ext E E.
Proof.
exists _ [tuple] [tuple] => /=.
- by rewrite Fadjoin_nil.
- by apply/forallP; case.
Qed.

Lemma rext_r r n (U : {subfield L}) x : r U x n -> r.-ext U << U; x >>%VS.
Proof.
move=> rUxn; exists _ [tuple x] [tuple n] => /=; first by rewrite adjoin_seq1.
by apply/forallP=> /= i; rewrite ord1 /= !tnth0 Fadjoin_nil.
Qed.

Lemma rext_trans r (F E K : {subfield L}) :
  r.-ext E F -> r.-ext F K -> r.-ext E K.
Proof.
move=> [n1 e1 pw1] FE Ee [n2 e2 pw2] KE Fe.
exists _ [tuple of e1 ++ e2] [tuple of pw1 ++ pw2] => /=.
  by rewrite adjoin_cat FE.
apply/forallP=> /= i; case: (unsplitP i) => [j eq_ij|k eq_i_n1Dk].
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
Proof. by case=> [n e pw] <- _; apply: subv_adjoin_seq. Qed.

Lemma solvable_by_radicals_radicalext (E F : {subfield L}) :
  radical.-ext E F -> solvable_by radical E F.
Proof. by move=> extEF; exists F. Qed.

Lemma radical_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  (0 < n)%N -> x ^+ n \in E -> radical E x n.
Proof. by move=> ??; apply/radicalP. Qed.

Lemma pradical_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  prime n -> x ^+ n \in E -> pradical E x n.
Proof. by move=> ??; apply/pradicalP. Qed.

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
- by apply: (@pradical_ext_Fadjoin n).
case/boolP: (2 <= n)%N; last first.
- case: n {lenk primeN_n} => [|[]]// in xnE n_gt0 * => _.
  suff ->:  <<E; x>>%VS = E by apply: rext_refl.
  by rewrite (Fadjoin_idP _).
move/primePn=> -/(_ primeN_n)[d /andP[d_gt1 d_ltn] dvd_dn].
have [m n_eq_md]: {k : nat | n = (k * d)%N}.
+ by exists (n %/ d)%N; rewrite [LHS](divn_eq _ d) (eqP dvd_dn) addn0.
have m_gt0 : (m > 0)%N.
  by move: n_gt0; rewrite !lt0n n_eq_md; apply: contra_neq => ->.
apply: (@rext_trans _ <<E; x ^+ d>>) => //.
  apply: (@IHk m (x ^+ d)) => //.
  - by rewrite -exprM mulnC -n_eq_md//.
  - by rewrite (leq_trans _ lenk)// n_eq_md ltn_Pmulr.
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
case=> [n e pw] FE Ee; exists _ e pw => //.
by apply: (tower_sub radical_pradical).
Qed.

Lemma pradicalext_radicalext (E F : {subfield L}) :
  radical.-ext E F -> pradical.-ext E F.
Proof.
case=> [n e pw]; elim: n e pw E => [|n ih] e pw E FE Ee.
  by rewrite -FE tuple0 /= Fadjoin_nil; apply: rext_refl.
apply: (@rext_trans _ << E; tnth e 0 >>).
  apply: (@pradicalext_radical (tnth pw 0)).
  by move/forallP/(_ ord0): Ee; rewrite take0 Fadjoin_nil.
apply: (ih [tuple of behead e] [tuple of behead pw]) => /=.
  by rewrite -adjoin_cons -drop1 (tnth_nth 0) -drop_nth 1?(drop0, size_tuple).
apply/forallP=> /= i; move/forallP/(_ (rshift 1 i)): Ee => /=.
rewrite !(tnth_nth 0, tnth_nth 0%N) !nth_behead [_ (rshift 1 i)]/=.
by rewrite -adjoin_cons take_addn drop1 (take_nth 0) 1?size_tuple // take0.
Qed.

Lemma solvable_by_radical_pradical (E F : {subfield L}) :
  solvable_by pradical E F -> solvable_by radical E F.
Proof. by case=> [R [/radicalext_pradicalext ERe FR]]; exists R. Qed.

Lemma solvable_by_pradical_radical (E F : {subfield L}) :
  solvable_by radical E F -> solvable_by pradical E F.
Proof. by case=> [R [/pradicalext_radicalext ERe FR]]; exists R. Qed.

End Properties.

End RadicalExtension.

Arguments tower {F0 L}.
Arguments extension_pred {F0 L}.
Arguments radical {F0 L}.

(* Field extensions in characteristic 0 are always separable *)
Section FieldExtChar0.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (charL : [char L] =i pred0).
Implicit Types (E F : {subfield L}) (p : {poly L}) (x : L).

(* (** Easy **) *)
(* Lemma subv_splittingFieldFor : (E <= F)%VS. *)
(* Proof. case: splitting_p => b pE <-; exact: subv_adjoin_seq. Qed. *)

(** Ok **)
Lemma root_make_separable p x : root p x = root (p %/ gcdp p p^`()) x.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite div0p root0.
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

Lemma char0_minPoly_separable x E : separable_poly (minPoly E x).
Proof.
have pE := minPolyOver E x; set p := minPoly E x.
suff /eqp_separable-> : p %= p %/ gcdp p p^`().
  by rewrite make_separable ?monic_neq0 ?monic_minPoly.
rewrite /eqp divp_dvd ?dvdp_gcdl// andbT.
rewrite minPoly_dvdp ?divp_polyOver ?gcdp_polyOver ?polyOver_deriv//.
by rewrite -root_make_separable// root_minPoly.
Qed.

Lemma char0_separable_element x E : separable_element E x.
Proof. exact: char0_minPoly_separable. Qed.

Lemma char0_separable E F : separable E F.
Proof. by apply/separableP => y _; apply: char0_separable_element. Qed.

Lemma char0_galois E F : (E <= F)%VS -> normalField E F -> galois E F.
Proof. by move=> sEF nEF; apply/and3P; split=> //; apply: char0_separable. Qed.

End FieldExtChar0.

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

Lemma kAutEnormal (K E : {subfield L}) (f : 'End(L)) :
  (K <= E)%VS -> normalField K E -> kAut K E f = kHom K E f.
Proof.
move=> KE normalKE; rewrite kAutE; have [f_hom|]//= := boolP (kHom _ _ _).
apply/subvP => _/memv_imgP[x Ex ->].
have := kHom_to_gal _ normalKE f_hom; rewrite subvv KE => -[//|g gK ->//].
by rewrite memv_gal.
Qed.

Import AEnd_FinGroup.
Lemma normalField_refl (K : {subfield L}) : normalField K K.
Proof.
apply/forallP => /= u; apply/implyP; rewrite in_set.
by move=> /andP[/andP[_ /fixedSpace_limg->]].
Qed.
Hint Resolve normalField_refl.

Lemma memv_mulP (K : fieldType) (aT : FalgType K) (U V : {vspace aT}) w :
  reflect (exists n (us vs : n.-tuple aT),
            [/\ all (mem U) us, all (mem V) vs & w = \sum_(i < n) tnth us i * tnth vs i])
          (w \in (U * V)%VS).
Proof.
apply: (iffP idP) => [|[b [us [vs [usU vsV ->]]]]]; last first.
  by rewrite rpred_sum// => i _; rewrite memv_mul//; apply/all_tnthP.
rewrite unlock span_def big_tuple => /memv_sumP[/= w_ w_mem ->].
have wP_ i : exists2 uv, (uv.1 \in U) && (uv.2 \in V) & w_ i = uv.1 * uv.2.
  have /vlineP[k ->] := w_mem i isT; set UV := (X in tnth X _).
  have /allpairsP[[u v] [uP vP ->]] := mem_tnth i UV.
  by exists (k *: u, v); rewrite /= ?rpredZ ?vbasis_mem// scalerAl.
pose uv i := (projT1 (sig2_eqW (wP_ i))).
exists _, [tuple (uv i).1 | i < _], [tuple (uv i).2 | i < _]; rewrite /uv.
split; do ?by apply/allP => _/mapP[i _ ->]; case: sig2_eqW => /= ? /andP[].
by apply: eq_bigr => i; rewrite !tnth_map/= tnth_ord_tuple; case: sig2_eqW.
Qed.

Lemma fixedField_sub  (K E : {subfield L}) (A : {set gal_of E}) :
  galois K E -> (('Gal(E / K))%g \subset A) -> (fixedField A <= K)%VS.
Proof. by move=> /galois_fixedField{2}<- subA; apply: fixedFieldS. Qed.

Lemma galois_sub  (K E : {subfield L}) (A : {group gal_of E}) :
  galois K E -> (('Gal(E / K))%g \subset A) = (fixedField A <= K)%VS.
Proof.
move=> galKE; apply/idP/idP; first exact: fixedField_sub.
move=> /galS-/(_ E)/=/subset_trans->//.
by apply/subsetP => u; rewrite gal_fixedField.
Qed.

Lemma galois_eq  (K E : {subfield L}) (A : {group gal_of E}) :
  galois K E -> ('Gal(E / K)%g == A) = (fixedField A == K)%VS.
Proof.
move=> galKE; have KE : (K <= E)%VS by case/andP: galKE.
by rewrite eqEsubset eqEsubv galois_sub// galois_connection.
Qed.

Lemma galois_misom (k K F : {subfield L})
  (H := 'Gal((K * F) / F)%g) (H' := 'Gal (K / (K :&: F))%g) :
  galois k K -> (k <= F)%VS -> misom H H' (normalField_cast K).
Proof.
move=> gal_kK kF; have kK : (k <= K)%VS by case/andP: gal_kK.
have normal_kK : normalField k K by case/and3P: gal_kK.
have KF u : u \in H -> (u @: K <= K)%VS.
  move=> Hu; suff : kHom k K u by rewrite -kAutEnormal// kAutE => /andP[].
  by apply/kAHomP => x kx; rewrite (fixed_gal _ Hu) ?field_subvMl ?(subvP kF).
have r_H_morphic : morphic H (normalField_cast K).
  apply/morphicP => u v uH vH; apply/eqP/gal_eqP => x Kx.
  rewrite galM// [LHS]galK ?KF ?groupM//.
  rewrite 2?galK ?KF//; last by apply/(subvP (KF u uH)); rewrite memv_img.
  by rewrite galM//; apply: subvP Kx; apply: field_subvMr.
apply/misomP; exists r_H_morphic; apply/isomP; split.
  apply/subsetP => /= u ker_u; have Hu := dom_ker ker_u.
  apply/set1gP/eqP/gal_eqP => _ /memv_mulP[n [xs [ys [xsP ysP ->]]]].
  rewrite rmorph_sum/= gal_id; apply: eq_bigr => i _; rewrite rmorphM/=.
  have [xiK yiK] := (allP xsP _ (mem_tnth i _), allP ysP _ (mem_tnth i _)).
  have /eqP/gal_eqP/(_ _ xiK) := mker ker_u.
  rewrite /normalField_cast galK ?KF// => ->; rewrite gal_id.
  by rewrite (fixed_gal _ Hu)// field_subvMl.
apply/eqP; rewrite eq_sym galois_eq ?(capv_galois gal_kK kF)//.
rewrite eqEsubv; apply/andP; split; apply/subvP => x; last first.
  rewrite memv_cap => /andP[Kx Fx].
  apply/fixedFieldP => // _ /morphimP[/= v Hv _ ->].
  rewrite morphmE /normalField_cast galK// ?KF//.
  by rewrite (fixed_gal _ Hv)// field_subvMl.
move=> /mem_fixedFieldP[Kx xP]; rewrite memv_cap Kx/=.
rewrite -(galois_fixedField (galois_prodv gal_kK kF)).
apply/fixedFieldP; first by rewrite -[x]mulr1 memv_mul// rpred1.
move=> u Hu; have := xP (normalField_cast _ u).
by rewrite /normalField_cast galK ?KF//; apply; apply/morphimP; exists u.
Qed.

Lemma galois_isog (k K F : {subfield L})
  (H := 'Gal((K * F) / F)%g) (H' := 'Gal (K / (K :&: F))%g) :
  galois k K -> (k <= F)%VS -> H \isog H'.
Proof. by move=> galkK /(galois_misom galkK) /misom_isog. Qed.

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
  exists _ r_ [tuple of nseq n n] => //; apply/forallP=> /= i.
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
have Gminpoly g : g \in G -> mxminpoly (mxof e g) %| 'X ^+ n - 1.
  move=> gG; rewrite mxminpoly_min// rmorphB rmorph1 rmorphX/= horner_mx_X.
  apply: (canLR (addrK _)); rewrite add0r -mxofX//.
  by rewrite [n]galois_dim// expg_cardG// mxof1.
have /sig2W [p p_unit dG] : codiagonalisable [seq mxof e g | g in G].
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
Hypothesis r_is_nth_root : (n.-primitive_root r)%R.

(* Part 1c : *)
(* If : *)
(* - G is solvable *)
Hypothesis solvable_G : solvable G.

Let subEF : (E <= F)%VS. Proof. by case/and3P: galois_EF. Qed.


(*** the prodv part must be proven/modified before attempting this ***)
(* We want to prove that F is solvable by radicals on E                       *)
Lemma part1c : solvable_by radical E F.
Proof.
pose G : {group gal_of F} := 'Gal(F / F :&: <<E; r>>%AS)%G.
have EEr := subv_adjoin E r.
rewrite /solvable_by; exists (F * <<E; r>>)%AS.
rewrite field_subvMr; split=> //.
apply: rext_trans (radicalext_Fadjoin_cyclotomic _ r_is_nth_root) _.
have galErFEr: galois <<E; r>>%AS (F * <<E; r>>)%AS.
  by rewrite (@galois_prodv _ _ E).
pose r' := r ^+ (n %/ #|G|).
have r'prim : #|G|.-primitive_root r'.
  by apply: dvdn_prim_root; rewrite // galois_dim ?cardSg ?galS ?subv_cap ?subEF.
have r'Er : r' \in <<E; r>>%VS by rewrite rpredX ?memv_adjoin.
apply: part1b r'Er _ => //=.
  rewrite (isog_sol (galois_isog galois_EF _))//.
  by apply: solvableS solvable_G; apply: galS; rewrite subv_cap subEF.
by rewrite galois_dim// (card_isog (galois_isog galois_EF _)).
Qed.

End Part1c.

(** Ok **)
(* Main lemma of part 1 *)
(* there is the problem of the nth-root which must be present in the big field L
to resolve here, but here is a first suggestion *)
Lemma part1 (F0 : fieldType) (L : splittingFieldType F0)
      (E F : {subfield L}) (p : {poly L}) :
  let n := (\dim_E F) in
  (exists r : L, (n.-primitive_root r)%R) -> galois E F ->
  solvable 'Gal(F / E) -> solvable_by radical E F.
Proof. by move=> /= /sigW [r r_prim] EF /(part1c EF r_prim); apply. Qed.

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
Hypothesis char_L : [char L] =i pred0.
Hypothesis prime_p : prime p.
Hypothesis r_is_pth_root : (p.-primitive_root r)%R.
Hypothesis x_notin_E : x \notin E.
Hypothesis xp_in_E : (x ^+ p)%R \in E.
Local Notation G := ('Gal(<<E; x>> / E))%g.

Section Part2a.
Hypothesis r_in_E : r \in E.

(* We want to prove that E(x) is Galois and abelian                           *)

(* - the roots of X^p - x^p are the x * a p-th root of the unity              *)
Lemma root_Xp_sub_xp (i : 'I_p) : root ('X^p - (x ^+ p)%:P) (x * r ^+ i)%R.
Proof.
apply/rootP; rewrite !(hornerE, hornerXn) exprMn exprAC.
by rewrite [r ^+ p]prim_expr_order // expr1n mulr1 subrr.
Qed.

Lemma uniq_roots_Xp_sub_xp : uniq [seq x * r ^+ (val i) | i : 'I_p].
Proof.
apply/(uniqP 0) => i j; rewrite !inE size_map size_enum_ord => ltip ltjp.
rewrite (nth_map (Ordinal ltip)) ?size_enum_ord //= nth_enum_ord //.
rewrite (nth_map (Ordinal ltjp)) ?size_enum_ord //= nth_enum_ord //.
have: x != 0 by apply/contra: x_notin_E => /eqP->; rewrite rpred0.
move/mulfI=> h{}/h /eqP; rewrite (eq_prim_root_expr r_is_pth_root).
by rewrite !modn_small -1?size_rs // => /eqP.
Qed.

Lemma size_Xp_sub_xp : size ('X^p - (x ^+ p)%:P) = p.+1.
Proof.
rewrite size_addl 1?size_polyXn // size_opp size_polyC.
by rewrite (@ltn_trans 2) // ltnS ?leq_b1 // prime_gt1.
Qed.

Lemma monic_Xp_sub_xp : 'X^p - (x ^+ p)%:P \is monic.
Proof.
rewrite monicE lead_coefE size_Xp_sub_xp // coefB.
rewrite coefXn coefC eqxx /= gtn_eqF ?subr0 //.
by rewrite (leq_trans _ (prime_gt1 _)).
Qed.

Lemma Xp_sub_xp_prod :
  'X^p - (x ^+ p)%:P = \prod_(i < p) ('X - (x * r ^+ i)%:P).
Proof.
pose rs := [seq x * r ^+ (val i) | i : 'I_p].
have [] := (@uniq_roots_prod_XsubC _ ('X^p - (x ^+ p)%:P) rs).
- by apply/allP=> z /mapP[/= i _ ->]; apply: root_Xp_sub_xp.
- by rewrite uniq_rootsE uniq_roots_Xp_sub_xp.
move=> /= q eq; suff eq1_q: q = 1.
  by rewrite eq eq1_q mul1r /rs big_map enumT.
case/boolP: (q == 0) eq => [|nz_q eq].
  by move/eqP=> -> /eqP; rewrite mul0r -size_poly_eq0 size_Xp_sub_xp.
move/(congr1 (size \o polyseq)): (eq) => /=; rewrite size_Mmonic //; last first.
  by apply: monic_prod => i _; apply: monicXsubC.
rewrite size_prod_XsubC addnS /= size_map size_enum_ord size_Xp_sub_xp -add1n.
move/addIn => /esym /eqP /size_poly1P [c nz_c qE] {nz_q}.
move/(congr1 lead_coef): (eq); rewrite lead_coef_XnsubC 1?prime_gt0 //.
by rewrite lead_coefM lead_coef_prod_XsubC mulr1 qE lead_coefC => <-.
Qed.

Lemma dvdp_Fadjoin_prime_Xp_sub_xp : minPoly E x %| ('X^p - (x ^+ p)%:P).
Proof.
apply: minPoly_dvdp.
- by rewrite rpredB 1?polyOverC //; apply/rpredX/polyOverX.
- by apply/rootP; rewrite !(hornerE, hornerXn) subrr.
Qed.

Lemma size_Fadjoin_prime : size (minPoly E x) = p.+1.
Proof.
have le_Ex_Sp: (size (minPoly E x) <= p.+1)%N.
  rewrite -size_Xp_sub_xp dvdp_leq //.
  - by rewrite -size_poly_gt0 size_Xp_sub_xp.
  - exact: dvdp_Fadjoin_prime_Xp_sub_xp.

Admitted.

(* - E(x) is the splitting field of X^p - x^p                                 *)
Lemma minPoly_Fadjoin_prime : minPoly E x = ('X^p - (x ^+ p)%:P)%R.
Proof.
apply/eqP; rewrite -eqp_monic.
- rewrite -dvdp_size_eqp; last exact dvdp_Fadjoin_prime_Xp_sub_xp.
  by rewrite size_Fadjoin_prime size_Xp_sub_xp.
- exact: monic_minPoly.
- exact: monic_Xp_sub_xp.
Qed.

(* - E(x) is thus Galois                                                      *)
Lemma galois_Fadjoin_prime : galois E <<E; x>>.
Proof.
apply/and3P; split.
- exact: subv_adjoin.
- rewrite -adjoin_seq1; apply: separable_Fadjoin_seq.
  by rewrite all_seq1; apply/charf0_separable/char_L.
apply/splitting_normalField => /=; first exact: subv_adjoin.
exists ('X^p - (x ^+ p)%:P).
  by rewrite rpredB // 1?polyOverC //; apply/rpredX/polyOverX.
pose rs := [seq x * r ^+ i | i : 'I_p].
exists rs.
  apply/eqpP; exists (1, 1); rewrite !(oner_neq0, scale1r) //.
  by rewrite Xp_sub_xp_prod /rs big_map enumT.
rewrite /rs /image_mem (map_comp (fun i => x * r ^+ i) _) val_enum_ord.
rewrite -[X in iota 0 X]prednK ?prime_gt0 // -add1n iota_add.
rewrite map_cat /= expr0 mulr1 adjoin_cons.
rewrite Fadjoin_seq_idP //; apply/allP => z /mapP[/= i].
rewrite mem_iota /= add0n add1n prednK 1?[(0 < p)%N]prime_gt0 //.
case/andP=> _ ltip ->; apply: rpredM.
- exact: memv_adjoin.
- by apply/subvP_adjoin/rpredX.
Qed.

(* - Gal(E(x) / E) has order p                                                *)
Lemma order_galois_Fadjoin_prime : #|G| = p.
Proof.
rewrite -galois_dim 1?galois_Fadjoin_prime // -adjoin_degreeE.
by have [] := size_minPoly E x; rewrite size_Fadjoin_prime => -[].
Qed.

(* - Gal(E(x) / E) is cyclic                                                  *)
(* - Gal(E(x) / E) is abelian                                                 *)
(* (end of part2a)                                                            *)
Lemma abelian_Fadjoin_prime : abelian G.
Proof.
by apply/cyclic_abelian/prime_cyclic; rewrite order_galois_Fadjoin_prime.
Qed.

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
  r \in E -> galois F E -> solvable 'Gal(E / F) ->
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

Lemma part2 (E F : {subfield L}) (p : {poly L}) : [char L] =i pred0 ->
  galois E F -> solvable_by radical E F ->
  {n : nat | forall r : L, n.-primitive_root r -> solvable 'Gal(F / E)}.
Proof.
move=> charL galEF [K [/pradicalext_radicalext [n e pw {K}<- /towerP epwP FK]]].
pose K := <<E & e>>%VS; pose d := (\prod_(i < n) tnth pw i)%N.
exists d => r r_root.
have EF: (E <= F)%VS by case/andP: galEF.
have EK: (E <= K)%VS by apply: subv_trans FK.
suff [galEKr solEKr] : galois E <<K; r>>%VS /\ solvable ('Gal(<<K; r>> / E))%G.
  rewrite -(isog_sol (normalField_isog galEKr _ _)); last 2 first.
  - by rewrite EF (subv_trans FK)// subv_adjoin.
  - by case/and3P: galEF.
  - exact: quotient_sol.
pose k := n; have eq_Kr : <<K ; r>>%AS = <<E & r :: take k e>>%AS.
  rewrite take_oversize ?size_tuple//.
  apply/val_inj; rewrite /= -adjoin_rcons.
  by rewrite (@eq_adjoin _ _ _ (rcons _ _) (r :: e))// => x; rewrite mem_rcons.
rewrite eq_Kr [<<K; r>>%VS](congr1 val eq_Kr) {eq_Kr}.
elim: k => /= [|k [IHgal IHsol]]; rewrite ?take0 ?adjoin_seq1.
  split; first exact: galois_Fadjoin_cyclotomic r_root.
  exact: solvable_Fadjoin_cyclotomic r_root.
have [ltnk|lenk] := ltnP k n; last first.
  by rewrite !take_oversize ?size_tuple// leqW in IHgal IHsol *.
rewrite (take_nth r) ?size_tuple// -rcons_cons adjoin_rcons.
pose ko := Ordinal ltnk; have /pradicalP[pwk_prime ekP] := epwP ko.
have [ekE|ekNE] := boolP (nth r e k \in <<E & r :: take k e>>%VS).
  by rewrite (Fadjoin_idP _).
have prim : (tnth pw ko).-primitive_root (r ^+ (d %/ tnth pw ko)).
  by rewrite dvdn_prim_root// /d (bigD1 ko)//= dvdn_mulr.
apply: (solvable_gal_Fadjoin_prime charL pwk_prime prim) => //=.
  rewrite -[k]/(val ko) -tnth_nth; apply: subvP ekP.
  by apply: adjoin_seqSr => x xe; rewrite in_cons xe orbT.
by rewrite adjoin_cons rpredX// (subvP (subv_adjoin_seq _ _))// memv_adjoin.
Qed.

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
  { r : L & (#|'Gal(F / E)|%g).-primitive_root r ->
        (radical.-ext E F <=> solvable 'Gal (F / E))
  }.
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
  solvable_by radical 1%AS K -> False.
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
  solvable_by radical 1%AS K <=>
  {in root (map_poly ratr p), forall x, exists f : algformula, alg_eval f = x}.
Proof.
Admitted.

End Examples.
