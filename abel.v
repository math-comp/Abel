From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.
From mathcomp Require Import all_field finmap.
From Abel Require Import Sn_solvable.

(******************************************************************************)
(*                                                                            *)
(*  Definitions for the statement ?                                           *)
(*    pure extension                                                          *)
(*    radical tower                                                           *)
(*    radical extension                                                       *)
(*    solvable by radicals                                                    *)
(*    Galois group of a polynomial ?                                          *)
(*                                                                            *)
(*  Additional lemmas ?                                                       *)
(*    Eisenstein criterion                                                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Defs.


Variables (F : fieldType) (L : splittingFieldType F).

(* Giving the parameters n and x in the definition makes it a boolean         *)
(* predicate which is useful as the tower property can be expressed as a path,*)
(* but it feels quite ugly for a tower                                        *)
Definition pure_extension (K E : {subfield L}) (x : L) (n : nat) :=
  [&& n > 0, (x ^+ n)%R \in K & (<<K; x>>%VS == E)].

(* n acts as an upper bound for the degree of the pure extension              *)
(* and sx as the set used to extend K                                         *)
Definition radical_tower (K : {subfield L}) (sE : seq {subfield L}) (n : nat)
  (A : {fset L}) :=
  path (fun (U V : {subfield L}) =>
    [exists x : A, [exists m : 'I_n, pure_extension U V (val x) m]]) K sE.

Definition radical_extension (K E : {subfield L}) :=
  exists2 n : nat, n > 0 & exists2 sE : seq {subfield L},
  last K sE == E & exists A : {fset L}, radical_tower K sE n A.


Definition solvable_by_radicals (k K : {subfield L}) (p : {poly L}) :=
  splittingFieldFor k p K ->
  exists2 E : {subfield L}, radical_extension k E & (K <= E)%VS.



End Defs.

Section Abel.

Variables (F : fieldType) (L : splittingFieldType F).

(* Following the french wikipedia proof :
https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_d%27Abel_(alg%C3%A8bre)#D%C3%A9monstration_du_th%C3%A9or%C3%A8me_de_Galois
*)

Section Part1.

(* Let K be a finite extension of k with degre n. *)
(* Let G = Gal(K/k). *)
(* - then the order of G is n *)

Section Part1a.

(* common context *)
Variables (k K : {subfield L}) (P : {poly L}).
Hypothesis P_split : splittingFieldFor k P K.
Hypothesis k_sub_K : (k <= K)%VS.
Local Notation G := ('Gal(K / k)%g).
Local Notation n := (\dim_k K).


(* Part 1a : *)
(* If : *)
(* - G is abelian *)
(* - k contains the n-th roots of the unity *)
Variable (r : L).
Hypothesis abelian_G : abelian G.
Hypothesis r_nth_root : (n.-primitive_root r)%R.
Hypothesis r_in_k : r \in k.


(* We want to prove that there exists a basis of K (as a k-vectoriel space) *)
(* which only has radical elements on k *)
(* Proof : *)
(* X^n - 1 splits on k in linear terms and it is separable *)
(* - with Lagrange, each element of G is canceled by X^n - 1 *)
(* - each element of G is diagonalizable *)
(* - the elements of G commutes because G is abelian *)
(* - the elements of G are simultaneously diagonalizable *)
(* - their eigenvalues are n-th root of the unity because their minimal *) 
(*   polynomial divides X^n - 1 *)
(* - let (r1, ..., rn) be their common basis *)
(* - we use the fact :  ri^n is unchanged by any m of G => ri^n is in k *)
(*   - let lambda be the eigenvalue which corresponds to m and ri *)
(*   - then m(ri^n) = (m(ri))^n (m automorphism) *)
(*   - m(ri) = lambda ri (lambda eigenvalue) *)
(*   - lambda^n ri^n = ri^n (lambda is an n-th root of the unity) *)
(*   - ri^n is unchanged by m *)
(*   - then ri^n is in k *)
(* - ri is a radical element on k *)
(* We can also add that K is solvable by radicals on k *)

Lemma part1a : radical_extension k K.
Proof.
Admitted.

End Part1a.

Section Part1b.

(* common context *)
Variables (k K : {subfield L}) (P : {poly L}).
Hypothesis P_split : splittingFieldFor k P K.
Hypothesis k_sub_K : (k <= K)%VS.
Local Notation G := ('Gal(K / k)%g).
Local Notation n := (\dim_k K).

(* Part 1b : *)
(* If : *)
(* - G is solvable *)
(* - k contains the n-th roots of the unity *)
Hypothesis solvable_G : solvable G.
Variable (r : L).
Hypothesis r_nth_root : (n.-primitive_root r)%R.
Hypothesis r_in_k : r \in k.


(* We want to prove that K is solvable by radicals *)
(* We proceed by recurrence on the length of the solvability chain of G *)
(* ({e} = G0 <| G1 <| ...<| Gi = G *)
(* - if i = 0, G is trivial, and K = k *)
(* - if i >= 0, let ki = K^Gi *)
(* - by Galois, K/ki and ki/k are Galois extension *)
(* - by recurrence, K is solvable by radicals on ki (the chain has length i-1)*)
(* - G = Gi x| G/Gi *)
(* - G/Gi is abelian thus ki is solvable by radicals on k (using Part1a) *)
(* - by transitivity, K is solvable by radicals on k *)

Lemma part1b : radical_extension k K.
Proof.
Admitted.

End Part1b.

Section Part1c.

(* common context *)
Variables (k K : {subfield L}) (P : {poly L}).
Hypothesis P_split : splittingFieldFor k P K.
Hypothesis k_sub_K : (k <= K)%VS.
Local Notation G := ('Gal(K / k)%g).
Local Notation n := (\dim_k K).

(* Part 1c : *)
(* If : *)
(* - G is solvable *)
Hypothesis solvable_G : solvable G.
Variable (r : L).
Hypothesis r_nth_root : (n.-primitive_root r)%R.

(* We want to prove that K is solvable by radicals on k *)
(* - Let k' = k(dzeta) where dzeta is an n-th root of the unity *)
(* - k' is solvable by radicals on k *)
(* - k' is a splitting field for X^n - 1 ***)
(* - k/k' is then Galois *)
(* - Let K' = k'K *)
(* - K' is Galois over k' *)
(* - Gal(K'/k') is isomorphic to a subgroup of G *)
(* - Gal(K'/k') is thus solvable *)
(* - K' is solvable by radicals on k' (Part1b) *)
(* - K' is solvable by radicals on k (transitivity) *)
(* - K <= K' so K is solvable by radicals *)

Lemma part1c : solvable_by_radicals k K P.
Proof.	
Admitted.

End Part1c.

(* Main lemma of part 1 *)
(* there is the problem of the nth-root which must be present in the big field L
to resolve here, but here is a first suggestion *)
Lemma part1 (k K : {subfield L}) (p : {poly L}) :
  let n := (\dim_k K) in
  exists r : L, (n.-primitive_root r)%R ->
  splittingFieldFor k p K -> solvable 'Gal(K / k) -> solvable_by_radicals k K p.
Proof.
Admitted.

End Part1.



















Section Part2.

Section IntermediateLemmas.

(* Part 2a : *)
(* If : *)
(* - K contains the p-th root of the unity, where p is prime *)
(* - let x be a p-th root of an element of K *)
Variables (K : {subfield L}) (p : nat) (x : L) (r : L).
Hypothesis prime_p : prime p.
Hypothesis r_pth_root : (p.-primitive_root r)%R.
Hypothesis x_notin_K : x \notin K.
Hypothesis xp_in_K : (x ^+ p)%R \in K.
Local Notation Kx := (<<K; x>>%VS).
Local Notation G := (('Gal(Kx / K))%g).


(* We want to prove that K(x) is Galois and abelian *)
(* - K(x) is the splitting field of X^p - x^p *)
(* - K(x) is thus Galois *)
(* - the roots of X^p - x^p are the x * a p-th root of the unity *)
(* - Every automorphism of K(x) which fixes K send x on one of the p roots of *)
(*   X^p - x^p *)
(* - Gal(K(x) / K) has order p *)
(* - Gal(K(x) / K) is cyclic *)
(* - Gal(K(x) / K) is abelian *)

Lemma radical_extension_roots (i : 'I_p) : root ('X^p - x%:P) ((x * r) ^+ i)%R.
Proof.
Admitted.

(* using a decomposition of minPoly in linear terms : its constant coefficient*)
(* is a power of x, and in K : it can only be at power p, hence its size *)
Lemma radical_extension_size_minPoly : size (minPoly K x) = p.+1.
Proof.
Admitted.

Lemma radical_extension_minPoly : minPoly K x = ('X^p + (x ^+ p)%:P)%R.
Proof.
Admitted.

(* using separable (separable_Fadjoin_seq & charf0_separable) *)
(* and probably normalFieldP *)
Lemma radical_extension_galois : galois K Kx.
Proof.
Admitted.

(* using galois_dim and radical_extension_minPoly *)
Lemma radical_extension_order_group : #|G| = p.
Proof.
Admitted.

(* using prime_cyclic & cyclic_abelian *) 
Lemma radical_extension_abelian : abelian G.
Proof.
Admitted.

(* in the recurrence : *)
(* - Let Fi = K(x0,..,xi) and Gi = Gal(Fi / K) *)
(*   - i >= 0 : *)
(*     - we suppose that Fi is Galois and solvable *)
(*     - Fi+1 / Fi is Galois and its Galois group H is abelian (part2a) *)
(*     - Fi+1 / K is Galois *)
(*     - Gi+1 = Gi x| H *)
(*     - Gi+1 is solvable *)

(* transitivity of galois (of normal & separable) *)
Lemma recurrence_step_galois (k : {subfield L}) :
  r \in k -> galois k K -> galois k (<<K; x>>%VS).
Proof.
Admitted.

(* return to the definition of solvable / transitivity *)
Lemma recurrence_step_solvable (k : {subfield L}) :
  r \in k -> galois k K -> solvable 'Gal(K / k) -> 
    solvable 'Gal(<<K; x>>%VS / k).
Proof.
Admitted.

End IntermediateLemmas.


Local Notation pure_extension_prime K E x n := 
  (pure_extension K E x n && prime n).
Local Notation radical_tower_prime K sE n A :=
  (path (fun (U V : {subfield L}) => [exists x : A, 
  [exists m : 'I_n, pure_extension_prime U V (val x) m]]) K sE).
Local Notation radical_extension_prime K E :=
  (exists2 n : nat, n > 0 & exists2 sE : seq {subfield L},
  last K sE == E & exists A : {fset L}, radical_tower_prime K sE n A).


(* Let p be a polynomial *)
(* Let K be a splitting field of p over k *)
(* p is solvable by radicals *)
(* - there exists a sequence x1,.., xn such that K is included in k(x1,..,xn) *)
(*   and a sequence of natural numbers m1,..,mn such that xi^mi is in *)
(*   k(x1,..xi-1) *)
(* - wlog all the mi are prime numbers (we can add intermediate fields) *)
Lemma radical_extension_primeP K E :
  radical_extension_prime K E <-> radical_extension K E.
Proof.
Admitted.

(* Exposing the list of exponents, and elements *)
Lemma solvable_by_radicals_primeP k K p :
  solvable_by_radicals k K p <-> (splittingFieldFor k p K ->
  exists n : nat, exists tn : nat ^ n, exists2 tx : L ^ n,
  (K <= <<k & (val tx)>>)%VS & [forall i : 'I_n, pure_extension_prime 
  <<k & (take i (val tx))>>%AS <<k & (take i.+1 (val tx))>>%AS (tx i) (tn i)]).
Proof.
Admitted.  

Section MainPart.

(* Let p be a polynomial *)
(* Let K be a splitting field of p over k *)
(* p is solvable by radicals *)
Variables (K k : {subfield L}) (P : {poly L}) (n : nat).
Variables (tn : nat ^ n) (tx : L ^ n) (r : L).
Hypothesis K_split : splittingFieldFor k P K.
Hypothesis p_solvable : solvable_by_radicals k K P.

(* - we can also add a m0 = (m1*..*mn)-th root of the unity at the beginning *)
Local Notation m := (\prod_(i < n) tn i).
Hypothesis r_pth_root : (m.-primitive_root r)%R.

(* in the recurrence : *)
(* - Let Fi = K(x0,..,xi) and Gi = Gal(Fi / K) *)
(*   - i = 0 : *)
(*     - F0 is cyclotomic *)
(*     - F0 is Galois and G0 is abelian *)
(*     - G0 is then solvable *)

(* cyclotomic extension *)

(* minPoly %| cyclotomic, then same arguments as in radical_extension_minPoly *)
Lemma cyclotomic_minPoly : minPoly k r = cyclotomic r m.
Proof.
Admitted.


(* using separable (separable_Fadjoin_seq & charf0_separable) *)
(* and probably normalFieldP *)
(* same as radical_extension_galois *)
Lemma galois_cyclotomic : galois k <<k; r>>%VS.
Proof.
Admitted.

(* using the definition, gal_adjoin_eq and prim_rootP *)
Lemma abelian_cyclotomic : abelian 'Gal(<<k; r>>%VS / k)%g.
Proof.
rewrite card_classes_abelian /classes.
apply/eqP; apply: card_in_imset => f g f_in g_in; rewrite -!orbitJ.
move/orbit_eqP/orbitP => [] h h_in <- {f f_in}; apply/eqP.
rewrite gal_adjoin_eq //= /conjg /= ?groupM ?groupV //.
rewrite ?galM ?memv_gal ?memv_adjoin //.
have hg_gal f : f \in 'Gal(<<k; r>>%VS / k)%g -> ((f r) ^+ m = 1)%R.
  move=> f_in; apply/prim_expr_order.
  have /and3P[subF _ NF] := galois_cyclotomic.
  rewrite  -(root_cyclotomic r_pth_root) -cyclotomic_minPoly.
  rewrite root_minPoly_gal // ?subF ?subvv ?memv_adjoin //.
have := svalP (prim_rootP r_pth_root (hg_gal _ g_in)); set ig := sval _ => hg.
have h1_in : (h^-1)%g \in 'Gal(<<k; r>>%VS / k)%g by rewrite ?groupV.
have := svalP (prim_rootP r_pth_root (hg_gal _ h1_in)); set ih1 := sval _ => hh1.
rewrite hh1 GRing.rmorphX /= hg GRing.exprAC -hh1 GRing.rmorphX /=.
by rewrite -galM ?memv_adjoin // mulVg gal_id.
Qed.


(* direct *)
Lemma solvable_nth_root : solvable 'Gal(<<k; r>>%VS / k).
Proof.
Admitted.

Local Notation ki i := <<<<k; r>> & (take i (val tx))>>%VS. 
Local Notation Gi i := ('Gal(ki i / k))%g.


(* - we proceed by recurrence on n, by proving that each extension k(x0,..,xn)*)
(*   of k is Galois and its Galois group is solvable. *)
(* - by Galois, k(x0,..,xn) is Galois over k (recurrence step) *)
(* using the cyclotomic extension for the initial step *)
(* using recurrence_step_galois and recurrence_step_solvable for the step *)
Lemma whole_recurrence : galois k (ki n) && solvable (Gi n).
Proof.
Admitted.

(* - Gal(K/k) = Gal(k(x0,..,xn)/k) / Gal(k(x0,..,xn)/K) *)
(* - then, Gal(K/k) is also solvable (quotient_sol) *)
Lemma solvable_Gal_Kk : solvable 'Gal(K / k).
Proof.
Admitted.

End MainPart.

(* Main lemma of part 2 *)
(* there is still the problem of the nth-root... but I don't know how to resolve it
here, as I don't see how we can explicitly get an upper_bound (which would be
enough) for the value of n *)
(* a solution would be to explicitly give an upper bound in solvable_by_radicals *)
Lemma part2 (k K : {subfield L}) (p : {poly L}) :
  splittingFieldFor k p K -> solvable_by_radicals k K p -> solvable 'Gal(K / k).
Proof.
Admitted.

End Part2.















Lemma AbelGalois (k K : {subfield L}) (p : {poly L}) :
  splittingFieldFor k p K ->
  solvable_by_radicals k K p <-> solvable 'Gal (K / k).
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

Lemma rp_roots : all (root (map_poly ratr p)) rp.
Proof.
Admitted.


(* This lemma should be divided into smaller parts                            *)
Definition pre_gal_perm (g : gal_of K) (i : 'I_d) : 'I_d.
Admitted.

Lemma gal_perm_is_perm (g : gal_of K) : injectiveb (finfun (pre_gal_perm g)).
Proof.
Admitted.

Definition gal_perm (g : gal_of K) := Perm (gal_perm_is_perm g).



Lemma injective_gal_perm : injective gal_perm.
Proof.
Admitted.

Lemma gal_perm_is_morphism :
  {in ('Gal(K / 1%AS))%G &, {morph gal_perm : x y / (x * y)%g >-> (x * y)%g}}.
Proof.
Admitted.

Canonical gal_perm_morphism :=  Morphism gal_perm_is_morphism.



Lemma injm_gal_perm : ('injm gal_perm)%g.
Proof.
Admitted.


(* Here it should also be divided                                             *)
Definition gal_orderd : gal_of K.
Admitted.

Lemma gal_orderp_orderd : #[gal_orderd]%g = d.
Proof.
Admitted.

Lemma permp_orderd : #[(gal_perm gal_orderd)]%g = d.
Proof.
(* morph_order & d_prime *)
Admitted.



(* Using the 2 complex roots                                                  *)
Definition gal_order2 : gal_of K.
Admitted.

Lemma gal_order2_order2 : #[gal_order2]%g = 2.
Proof.
Admitted.

Lemma perm2_order2 : #[(gal_perm gal_order2)]%g = 2.
Proof.
Admitted.



(* Missing lemma :                                                            *)
(* Sp is generated by a p-cycle and a transposition : how to state it ?       *)



Lemma surj_gal_perm : (gal_perm @* 'Gal (K / 1%AS) = 'Sym_('I_d))%g.
Proof.
Admitted.




Lemma isog_gal_perm : 'Gal (K / 1%AS) \isog ('Sym_('I_d)).
Proof.
(* isogP, surj_gal_perm & injm_gal_perm *)
Admitted.


End Example1.

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

(* Usually, this is done with Eisenstein's criterion, but I don't think it is *)
(* already formalized in mathcomp                                             *)
(***  By Cyril ?                                                            ***)
Lemma irreducible_ex : irreducible_poly poly_example.
Proof.
Admitted.


Lemma separable_ex : separable_poly poly_example.
Proof.
apply/coprimepP => q /(irredp_XsubCP irreducible_ex) [//| eqq].
have size_deriv_ex : size poly_example^`() = 5.
  rewrite !derivCE addr0 alg_polyC -scaler_nat /=.
  by rewrite size_addl ?size_scale ?size_opp ?size_polyXn ?size_polyC.
by rewrite gtNdvdp -?size_poly_eq0 ?size_deriv_ex ?(eqp_size eqd) ?size_poly_ex.
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


(* An example of how it could feel to use the proposed statement              *)
Lemma example_not_solvable_by_radicals :
  splittingFieldFor 1%AS (map_poly ratr poly_example) K ->
  ~ solvable_by_radicals 1%AS K (map_poly ratr poly_example).
Proof.
move=> K_splitP; rewrite (AbelGalois K_splitP).
have := (example1 K_splitP separable_ex irreducible_ex prime_ex count_roots_ex).
by move/isog_sol => ->; apply: not_solvable_Sym; rewrite card_ord size_poly_ex.
Qed.


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

(* I changed a little bit the statement your proposed as being solvable by    *)
(* radicals can't be obtain from a formula for only one root.                 *)
(* I also feel that giving both the coefficients of the polynomial and access *)
(* to the rationals is redundant.                                             *)
Lemma example_formula (p : {poly rat}) :
  splittingFieldFor 1%AS (map_poly ratr poly_example) K ->
  solvable_by_radicals 1%AS K (map_poly ratr p) <->
  {in root (map_poly ratr p), forall x, exists f : algformula, alg_eval f = x}.
Proof.
Admitted.

End Examples.