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


(* Can we have a direct definition for 'the splitting field of a polynomial'  *)
(* which is a {subfield L} ? But L must then be big enough                    *)

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


(* Part 1a : *)
(* If : *)
(* - G is abelian *)
(* - k contains the n-th roots of the unity *)
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

(* Part 1b : *)
(* If : *)
(* - G is solvable *)
(* - k contains the n-th roots of the unity *)
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

(* Part 1c : *)
(* If : *)
(* - G is solvable *)
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
	
End Part1.



Lemma AbelGalois (k : {subfield L}) (K : {subfield L}) (p : {poly L}) :
  splittingFieldFor k p K ->
  solvable_by_radicals k K p <-> solvable ('Gal (K / k)).
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