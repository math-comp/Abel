From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(********************)
(* package fingroup *)
(********************)

(*************)
(* gproduct *)
(*************)

Definition setX0 := groupX0.
#[deprecated(since="mathcomp 2.3",note="Use groupX0 instead.")]

(*******************)
(* package algebra *)
(*******************)

(********)
(* poly *)
(********)

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

#[deprecated(since="mathcomp 2.2.0",note="Use polyOverXsubC instead.")]
Lemma poly_XsubC_over {R : ringType} c (S : subringClosed R) :
  c \in S -> 'X - c%:P \is a polyOver S.
Proof. by move=> cS; rewrite rpredB ?polyOverC ?polyOverX. Qed.

#[deprecated(since="mathcomp 2.2.0",note="Use polyOverXnsubC instead.")]
Lemma poly_XnsubC_over {R : ringType} n c (S : subringClosed R) :
  c \in S -> 'X^n - c%:P \is a polyOver S.
Proof. by move=> cS; rewrite rpredB ?rpredX ?polyOverX ?polyOverC. Qed.

#[deprecated(since="mathcomp 2.2.0",note="Use prim_root_natf_eq0 instead.")]
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

#[deprecated(since="mathcomp 2.2.0",note="Use prim_root_eq0 instead.")]
Lemma primitive_root_eq0 (F : fieldType) n (w : F) :
  n.-primitive_root w -> (w == 0) = (n == 0%N).
Proof.
move=> wp; apply/eqP/idP => [w0|/eqP p0]; move: wp; rewrite ?w0 ?p0; last first.
  by move=> /prim_order_gt0//.
move=> /prim_expr_order/esym/eqP.
by rewrite expr0n; case: (n =P 0%N); rewrite ?oner_eq0.
Qed.

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

