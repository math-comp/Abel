From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field polyrcf polyorder.
From Abel Require Import various.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope ring_scope.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

Lemma mem_rootsR (R : rcfType) (p : {poly R}) : p != 0 -> rootsR p =i root p.
Proof. by move=> x pneq0; rewrite -roots_on_rootsR. Qed.

Lemma rootsE (R : rcfType) a b (p : {poly R}) : p != 0 ->
  roots p a b = [seq x <- rootsR p | a < x < b].
Proof.
move=> p_neq0; symmetry; apply: roots_uniq => //.
  by move=> i; rewrite !inE/= mem_filter mem_rootsR.
by rewrite (sorted_filter lt_trans)// sorted_roots.
Qed.

Lemma size_root_leSderiv (R : rcfType) (p : {poly R}) :
  (size (rootsR p) <= (size (rootsR p^`())).+1)%N.
Proof.
set s := rootsR p; set n := size s.
have [->//|n_gt0] := posnP n; rewrite -[n]prednK// ltnS.
have sizep_gt1 : (size p > 1)%N.
  have /hasP[x] : has predT s by rewrite has_predT.
  by rewrite in_roots => /and3P[+ _ pN0] => /root_size_gt1->.
have dp_neq0 : p^`() != 0 by rewrite -size_poly_eq0 size_deriv -lt0n ltn_predRL.
have p_neq0 : p != 0 by apply: contraTneq sizep_gt1 => ->; rewrite size_poly0.
have Silt k (i : 'I_k.-1) : (i.+1 < k)%N by rewrite -ltn_predRL.
have slt (i : 'I_n.-1) : s`_i < s`_(i.+1) by apply/sortedP; rewrite ?sorted_roots.
have peq0 i : (i < n)%N -> p.[s`_i] = 0.
  by move=> i_lt; apply/rootP; rewrite -[root _ _]mem_rootsR// mem_nth.
have peq (i : 'I_n.-1) : p.[s`_i] = p.[s`_(i.+1)] by rewrite !peq0// ltnW.
have /all_sig2[r rs p'r] := rolle (slt _) (peq _).
have rtE (i : 'I_n.-1) : [tuple r i | i < n.-1]`_i = r i.
  by rewrite (nth_map i) ?size_enum_ord ?nth_ord_enum.
suff /(sorted_uniq lt_trans lt_irreflexive) : sorted <%R [tuple r i | i < _].
  move=> /uniq_leq_size/(_ _)/(leq_trans _)->//; first by rewrite ?size_tuple.
  by move=> _ /mapP[i _ ->]; rewrite mem_rootsR// [_ \in _]rootE p'r.
apply/(sortedP 0); rewrite size_tuple => i' i'lt.
pose i1 := Ordinal i'lt; pose i2 := Ordinal (ltnW i'lt).
by rewrite (rtE i1) (rtE i2) (@lt_trans _ _ s`_i1)// (itvP (rs _)).
Qed.
