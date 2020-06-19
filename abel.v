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

Local Open Scope ring_scope.
Local Open Scope fset_scope.

Section RadicalExtension.

Variables (F0 : fieldType) (L : splittingFieldType F0).

Section Defs.

(* Giving the parameters n and x in the definition makes it a boolean         *)
(* predicate which is useful as the tower property can be expressed as a path,*)
Definition radical (n : nat) (x : L) (U V : {subfield L}) :=
  [&& (n > 0)%N, x ^+ n \in U & (<<U; x>>%AS == V)].

(* n acts as an upper bound for the degree of the pure extension              *)
(* and A as the set used to extend U                                          *)
Definition tower (r : nat -> L -> rel {subfield L}) (n : nat) (A : {fset L}) :=
  path (fun U V => [exists x : A, [exists m : 'I_n, r m (val x) U V]]).

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.

(* the quantification on n is useless as we directly have an upper bound      *)
Definition extension_pred (r : nat -> L -> rel {subfield L}) (U V : {subfield L}) :=
  exists2 sU : seq {subfield L}, exists A : {fset L},
    r.-tower (\dim_U V).+1 A U sU & last U sU = V.

Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

Definition solvable_by (r : nat -> L -> rel {subfield L}) (U V : {subfield L}) :=
  (U <= V)%VS /\ exists2 E : {subfield L}, r.-ext U E & (V <= E)%VS.

Definition solvable_by_radicals_poly (E F : {subfield L}) (p : {poly L}) :=
  splittingFieldFor E p F -> solvable_by radical E F.

End Defs.

Local Notation "r .-tower" := (tower r)
  (at level 2, format "r .-tower") : ring_scope.
Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.



Section Properties.

Implicit Type r : nat -> L -> rel {subfield L}.

Lemma rext_refl r (E : {subfield L}) : r.-ext E E.
Proof. by exists [::] => //; exists fset0. Qed.

(** We could generalize to an m >= dim_U V **)
Lemma rext_r r (x : L) (U V : {subfield L}) :
  r (\dim_U V) x U V -> r.-ext U V.
Proof.
move=> rxUV; exists [:: V] => //; exists [fset x]%fset; rewrite /= andbT.
by apply/existsP; exists [` fset11 _]%fset; apply/existsP; exists ord_max.
Qed.

(** Easy **)
(* adding a field in the tower                                                *)
(* order of the variables E F K ?                                             *)
Lemma rext_r_trans r (x : L) (n : nat) (E F K : {subfield L}) :
  r.-ext E F -> r n x F K -> r.-ext E K.
Proof.
Admitted.

(** Easy **)
(* adding a tower                                                             *)
Lemma rext_trans r (E F K : {subfield L}) :
  r.-ext E F -> r.-ext F K -> r.-ext E K.
Proof.
Admitted.

Lemma tower_subspace r n A E s : (forall n x U V, r n x U V -> (U <= V)%VS) ->
   r.-tower n A E s -> (E <= last E s)%VS.
Proof.
move=> hsubspace; elim/last_ind: s=> [| s K ihs] //=.
rewrite last_rcons /tower rcons_path; case/andP=> /ihs=> {ihs} ihs.
case/existsP => x /existsP[m /hsubspace]; exact: subv_trans.
Qed.

Lemma radical_subspace n x U V : radical n x U V -> (U <= V)%VS.
Proof.
by case/and3P=> _ _ /eqP<-; rewrite /= -adjoin_seq1; apply: subv_adjoin_seq.
Qed.

Lemma rext_subspace (E F : {subfield L}) : radical.-ext E F -> (E <= F)%VS.
Proof.
case=> s [A rtow <-]; apply: tower_subspace rtow; exact: radical_subspace.
Qed.

Lemma solvable_by_radicals_radicalext (E F : {subfield L}) :
  radical.-ext E F -> solvable_by radical E F.
Proof.
move=> extEF; split;last by exists F.
exact: rext_subspace.
Qed.

Lemma radical_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  (0 < n)%N -> x ^+ n \in E -> radical n x E <<E; x>>%AS.
Proof. by rewrite /radical => -> -> /=. Qed.

(** Easy **)
Lemma rext_Fadjoin (n : nat) (x : L) (E : {subfield L}) :
  (0 < n)%N -> x ^+ n \in E -> radical.-ext E <<E; x>>%AS.
Proof.
(* direct *)
Admitted.

(* radical extension with only pure extensions of prime degree                *)
Definition pradical (n : nat) (x : L) (U V : {subfield L}) :=
  radical n x U V && prime n.



(** Easy **)
Lemma pradicalext_radical (n : nat) (x : L) (E F : {subfield L}) :
  radical n x E F -> pradical.-ext E F.
Proof.
(* factorization of the degree of the extension : if n = uv *)
(* instead of adding x ^ (uv) in E, we can first add x^u and then x *)
Admitted.

(** Easy **)
Lemma radicalext_pradicalext (E F : {subfield L}) :
  radical.-ext E F <-> pradical.-ext E F.
Proof.
(* first implication : using pradicalext_radical *)
(* second implication : direct *)
Admitted.

(** Easy **)
Lemma solvable_by_radical_pradical (E F : {subfield L}) :
  solvable_by pradical E F <-> solvable_by radical E F.
Proof.
Admitted.

(** Ok **) (* but painful *)
(* Exposing the list of exponents, and elements                               *)
Lemma radicalext_explicit_parameters E F :
  radical.-ext E F -> (exists n : nat, exists tn : nat ^ n, exists2 tx : L ^ n,
  (\prod_(i < n) tn i = \dim_E F)%N & (F == <<E & (fgraph tx)>>)%AS &&
  [forall i : 'I_n, prime i && radical (tn i) (tx i)
  <<E & (take i (fgraph tx))>> <<E & (take i.+1 (fgraph tx))>>]).
Proof.
Admitted.

(** Easy **)
Lemma solvable_by_radical_explicit_parameters E F :
  solvable_by radical E F <-> (exists n : nat, exists tn : nat ^ n,
  exists2 tx : L ^ n, (F <= <<E & (fgraph tx)>>)%VS & [forall i : 'I_n, prime i
  && radical (tn i) (tx i) <<E & (take i (fgraph tx))>>
  <<E & (take i.+1 (fgraph tx))>>]).
Proof.
(* using solvable_by pradical <-> solvable_by radical and the lemma above *)
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
Lemma root_make_separable x : root p x = root (p %/ gcdp p p^`()) x.
Proof.
Admitted.

(** Ok **)
Lemma galois_splittingFieldFor : galois E F.
Proof.
(* from definition : *)
(* for the separable part : with minPoly_dvdp, dvdp_separable,*)
(* root_make_separable and make_separable, minPoly is separable so every root *)
(* of p is a separable_element *)
(* for the normal part : directly splitting_normalField *)
Admitted.

End Splitting.

(* transitivity *)
Section Transitivity.
Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (E F K : {subfield L}). (* should this be E K and M ? *)
Hypothesis subvs_EFK : (E <= F <= K)%VS.

(** Easy **)
Lemma normalField_trans : normalField E F -> normalField F K -> normalField E K.
Proof.
(* using, for example, splitting_normalField *)
Admitted.

(** Easy **)
Lemma galois_trans : galois E F -> galois F K -> galois E K.
Proof.
(* using the lemma above and the transitivity of separable *)
Admitted.

End Transitivity.

(* cyclotomic extensions                                                      *)
Section Cyclotomic.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (E : {subfield L}) (r : L) (n : nat).
Hypothesis r_is_nth_root : n.-primitive_root r.

(** Hard **)
(*     - E(x) is cyclotomic                                                   *)
Lemma minPoly_cyclotomic : r \notin E -> minPoly E r = cyclotomic r n.
Proof.
(* minPoly %| cyclotomic *)
(* then using a decomposition of minPoly in linear terms : its constant *)
(* coefficient is a power of x, and in E : it can only be at power p, hence *)
(* its size, and value *)
Admitted.

(** Ok **)
Lemma splitting_Fadjoin_cyclotomic :
  r \notin E -> splittingFieldFor E (cyclotomic r n) <<E; r>>.
Proof.
Admitted.

(** Easy **)
(*     - E(x) is Galois                                                       *)
Lemma galois_Fadjoin_cyclotomic : galois E <<E; r>>.
Proof.
(* if yes, ok, if no, we use splitting_cyclotomic *)
Admitted.

Local Notation "r .-ext" := (extension_pred r)
  (at level 2, format "r .-ext") : ring_scope.

(** Easy **)
Lemma radicalext_Fadjoin_cyclotomic : radical.-ext E <<E; r>>%AS.
Proof.
(* is r in E ? *)
(* is yes, ok, if no, we use its minPoly *)
Admitted.

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
  rewrite root_minPoly_gal // ?subF ?subvv ?memv_adjoin //.
have := svalP (prim_rootP r_is_nth_root (hg_gal _ g_in)).
have h1_in : (h^-1)%g \in 'Gal(<<E; r>> / E)%g by rewrite ?groupV.
have := svalP (prim_rootP r_is_nth_root (hg_gal _ h1_in)).
set ih1 := sval _ => hh1; set ig := sval _ => hg.
rewrite hh1 GRing.rmorphX /= hg GRing.exprAC -hh1 GRing.rmorphX /=.
by rewrite -galM ?memv_adjoin // mulVg gal_id.
Qed.

(** Easy **)
(*     - Gal(E(x) / E) is then solvable                                       *)
Lemma solvable_Fadjoin_cyclotomic : solvable 'Gal(<<E; r>> / E).
Proof.
(* direct *)
Admitted.

End Cyclotomic.

Section Prodv.

Variables (F0 : fieldType) (L : splittingFieldType F0).

(** N/A **)
Lemma prodv_galois (E F K : {subfield L}) :
  galois E K -> galois F (E * F).
Proof.
Admitted.

(** N/A **)
Lemma prodv_galoisI (E F K : {subfield L}) :
  galois E K -> galois (E :&: F) F.
Proof.
Admitted.

(** N/A **)
Lemma prodv_gal (E F K : {subfield L}) :
  galois E K -> ('Gal((E * F) / F) \isog 'Gal(F / (E :&: F)))%g.
Proof.
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

(* Let F be a finite extension of E with degre n. *)
(* Let G = Gal(F/E). *)
(* - then the order of G is n *)

Section Part1a.
Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (E F : {subfield L}).
Hypothesis galois_EF : galois E F.
Hypothesis subv_EF : (E <= F)%VS.
Local Notation G := ('Gal(F / E)%g).
Local Notation n := (\dim_E F).

(* Part 1a : *)
(* If : *)
(* - G is abelian *)
(* - E contains the n-th roots of the unity *)
Hypothesis abelian_G : abelian G.

(** Easy **)
(* - with Lagrange, each element of G is canceled by X^n - 1                  *)
Lemma order_galois g : g \in G -> (g ^+ n = 1)%g.
Proof.
Admitted.

(** Easy/Useless == (centsP abelian_G) **)
(* - the elements of G commutes because G is abelian *)
(* Lemma commute_galois : {in G &, forall g h, commute g h}. *)
(* Proof. by move=> *; apply/(centsP abelian_G). Qed. *)

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

(** Hard : Cyril **)
(* - F is solvable by radicals on E *)

End Part1a.

Import GRing.Theory.


Lemma part1a (F0 : fieldType) (L : splittingFieldType F0)
    (E F : {subfield L}) (G := 'Gal(F / E)%g) (n := \dim_E F) (r : L) :
      (E <= F)%VS -> galois E F -> abelian G ->
      r \in E -> (n.-primitive_root r)%R ->
  radical.-ext E F.
Proof.
move=> subv_EF galois_EF abelian_G r_in_E r_is_nth_root.
have n_gt0 : (n > 0)%N by rewrite /n -dim_aspaceOver ?adim_gt0.
have asimp := (mem_aspaceOver, subv_adjoin_seq).
suff [/= r_ /andP[r_basis /allP r_F] m_r {abelian_G}] :
     exists2 r_ : n.-tuple L,
       basis_of (aspaceOver E F) (r_ : seq (fieldOver E)) && all (mem F) r_ &
         forall i m, m \in G -> exists2 l, (l \in E) && (l ^+ n == 1)
                                           & m (tnth r_ i) = l * tnth r_ i.
  exists [seq <<E & (take i r_)>>%AS | i <- iota 1 n]; last first.
    pose f i := <<E & take i r_>>%AS.
    have {1}<- : f 0%N = E by apply/val_inj; rewrite /f/= take0 Fadjoin_nil.
    rewrite last_map/= -(subnK n_gt0) iota_add/= cats1 last_rcons subnKC// /f.
    rewrite take_oversize// ?size_tuple//.
    apply/val_inj/eqP; rewrite eqEdim; apply/andP; split.
      by apply/Fadjoin_seqP; split.
    rewrite [X in (X <= _)%N](dim_sup_field subv_EF).
    rewrite [X in (_ <= X)%N](dim_sup_field (subv_adjoin_seq _ _)).
    rewrite leq_mul2r gtn_eqF ?adim_gt0//=.
    rewrite -[X in (_ <= X)%N]dim_aspaceOver ?subv_adjoin_seq//=.
    suff -> : vspaceOver E << E & r_ >>%AS = <<1 & r_ : seq (fieldOver E)>>%AS.
      rewrite (span_basis r_basis) (addv_idPr _) ?sub1v//=.
      by rewrite subfield_closed dim_aspaceOver.
    (* extract commutation between vspaceOver and << _ & _ >> *)
    apply/eqP; rewrite eqEsubv; apply/andP; split; last first.
      apply/Fadjoin_seqP; split; rewrite ?sub1v// => x x_r_.
      by rewrite ?asimp//= seqv_sub_adjoin.
    have [K [r_K EK memK]] := aspaceOverP <<1 & r_ : seq (fieldOver E) >>%AS.
    suff subErK: (<<E & r_>>%AS <= K)%VS.
      by apply/subvP => x; rewrite ?asimp//= memK; apply/subvP.
    by apply/Fadjoin_seqP; split => // x x_r_; rewrite -memK seqv_sub_adjoin.
  pose R := [fset x in val r_].
  exists R; apply/(pathP F) => val_i; rewrite size_map size_iota => lt_in.
  pose i := Ordinal lt_in; have riR: tnth r_ i \in R by rewrite inE mem_tnth.
  apply/existsP => /=; exists [` riR]; apply/existsP => /=; exists ord_max.
  rewrite /radical n_gt0//=; apply/andP; split; last first.
     admit. (* should be easy *)
  suff: tnth r_ i ^+ n \in fixedField G.
    rewrite (galois_fixedField _)//; apply/subvP.
    admit. (* should be very easy *)
  apply/fixedFieldP; first by rewrite rpredX// [_ \in _]r_F// mem_tnth.
  move=> g /(m_r i)[l /andP[lE /eqP lX1] gri].
  by rewrite rmorphX/= gri exprMn lX1 mul1r.
pose LE := [fieldExtType subvs_of E of fieldOver E].
have [e e_basis] : { e : n.-1.+1.-tuple _ | basis_of (aspaceOver E F) e}.
  rewrite prednK//; have := vbasisP (aspaceOver E F); move: (vbasis _).
  by rewrite dim_aspaceOver// => e; exists e.
have e_free := basis_free e_basis.
have Gminpoly g : g \in G -> mxminpoly (mxof e g) %| 'X ^+ n - 1.
  move=> gG; rewrite mxminpoly_min// rmorphB rmorph1 rmorphX/= horner_mx_X.
  by apply: (canLR (addrK _)); rewrite add0r -mxofX// order_galois// mxof1//.
have /codiagonalisableP[p p_unit dG] : codiagonalisable [seq mxof e g | g in G].
  split.
    apply/all_commP => _ _ /mapP[g gG ->] /mapP[g' g'G ->].
    rewrite /GRing.comm -!mxofM//; congr mxof.
    by rewrite !mem_enum in g'G gG; rewrite (centsP abelian_G).
  move=> _/mapP[g gG ->]; rewrite mem_enum in gG *.
  pose l := [seq Subvs r_in_E ^+ i | i <- index_iota 0 n].
  exists l.
    rewrite map_inj_in_uniq ?iota_uniq//.
    move=> x y; rewrite !mem_index_iota !leq0n/= => x_n y_n.
    move=> /(congr1 val)/=/eqP; rewrite !rmorphX/=.
    by rewrite (eq_prim_root_expr r_is_nth_root) !modn_small// => /eqP.
  rewrite big_map (@factor_Xn_sub_1 _ _ (Subvs r_in_E)) ?Gminpoly//.
  by rewrite /= -(fmorph_primitive_root [rmorphism of vsval]).
pose r_ := [tuple vecof e (row i p) | i < n.-1.+1].
rewrite -[n]prednK//; exists r_.
  apply/andP; split; last first.
    by apply/allP => _ /mapP[/=i _ ->]; rewrite vecof_in.
  admit. (* follows from p_unit, via missing lemma in galmx *)
move=> i g gG; have /allP /(_ (mxof e g) (map_f _ _))/sim_diagP := dG.
case=> // [|M pg]; first by rewrite mem_enum.
exists (val (M 0 i)); [apply/andP; split|]; first by rewrite /= subvsP.
  rewrite [X in _ ^+ X]prednK// -subr_eq0.
  have := Gminpoly _ gG; rewrite (simP _ pg)//.
  move => /dvdpP [q] /(congr1 (val \o horner^~ (M 0 i)))/=.
  rewrite hornerM hornerD hornerN hornerXn hornerC/= rmorphX algid1 => ->.
  suff -> : (mxminpoly (p^-1 * diag_mx M * p)).[M 0 i] = 0 by rewrite mulr0.
  admit. (* commutation between conjucation and mxminpoly *)
have /eqP/(congr1 (mulmx (@delta_mx _ 1 _ 0 i))) := pg; rewrite !mulmxA -!rowE.
have -> : row i (diag_mx M) = M 0 i *: delta_mx 0 i.
  by apply/rowP => j; rewrite !mxE eqxx eq_sym/= mulr_natr.
rewrite -scalemxAl -rowE => pg_eq.
admit. (* transfer pg_eq via vecof, via missing lemma in galmx *)
Admitted.


Section Part1b.
Variables (F0 : fieldType) (L : splittingFieldType F0).
Variable (E : {subfield L}).

(** Hard **) (* but only because it is long *)
Lemma part1b (F : {subfield L}) (r : L) :
  let n := \dim_F E in
  galois E F -> solvable 'Gal(F / E)%g -> r \in E -> n.-primitive_root r ->
  radical.-ext E F.
Proof.
(* we have n > 0 (order of the group, or dim) *)
(* either by generalized recurrence on n, (or on the chain of solvability) : *)
(*   (E or F or both need to be generalize for the induction hypothesis) *)
(* if n = 1 : we have \dim_E F = 1 so E = F*)
(* if n > 1 : *)
(*   we use sol_prime_factor_exists to get a distinguished subgroup H of *)
(*     Gal(F/E) *)
(*   we also get that the order of G/H is prime *)
(*   we directly have that F/F^H is galois and its galois group is H *)
(*   by normal_fixedField_galois, F^H/E is galois *)
(*   by normalField_isog, its galois group is isomorphic to G/H *)
(*   G/H is abelian, as its order is prime (p.-abelem) *)
(*   by part1a, F^H is radical over E *)
(*   to use the induction hypothesis we need to show that : *)
(*     - H is solvable as a subgroup of G *)
(*     - F^H contains a #|H| primitive root of the unity (#|H| divides n) *)
(*     - F/F^H is galois (already said before) *)
(*   so F is radical over F^H *)
(*   finally, by transitivity, F is radical over E *)
Admitted.

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
Hypothesis radical_Ei : forall i, radical (tn i) (tx i)
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

Definition poly_example : {poly rat} := 'X^5 - 4%:R *: 'X + 2%:R%:P.

Lemma size_poly_ex : size poly_example = 6.
Proof.
rewrite /poly_example -addrA size_addl ?size_polyXn//.
by rewrite size_addl ?size_opp ?size_scale ?size_polyX ?size_polyC.
Qed.

Lemma poly_example_neq0 : poly_example != 0.
Proof. by rewrite -size_poly_eq0 size_poly_ex. Qed.

(** N/A : Cyril ? **)
(* Usually, this is done with Eisenstein's criterion, but I don't think it is *)
(* already formalized in mathcomp                                             *)
Lemma irreducible_ex : irreducible_poly poly_example.
Proof.
Admitted.


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
