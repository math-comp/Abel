From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Temp.

(* This is actually quite useless, I am not convinced anymore that we should keep it. *)
Lemma big_condT [R : Type] [idx : R] (op : Monoid.com_law idx)
    [I : finType] (A : {pred I}) (F : I -> R) :
    \big[op/idx]_(i in A | true) F i = \big[op/idx]_(i in A) F i.
Proof. by rewrite big_mkcondr. Qed.

(** Alternative: *)
(* Definition Zp_succ n : 'I_n -> 'I_n := if n is n.+1 then +%R ord_max else id. *)
(* The computational content would not be visible without the case distinction on n. Besides, this is not used anywhere anymore, so we can get rid of it. *)

Definition Zp_succ n (i : 'I_n) :=
  match i with
  | @Ordinal _ k klt => Ordinal (
      match n as n0 return (k < n0)%N -> (k.+1 %% n0 < n0)%N with
      | 0 => id
      | n0.+1 => fun=> ltn_pmod k.+1 (is_true_true : 0 < n0.+1)%N
      end klt)
  end.

(* J'ai l'impression que je veux garder la quantification sur $r$ dans la première hypothèse. Je laisse ma version dans various.v le temps qu'on en discute. *)
Lemma logn_prod [I : Type] (r : seq I) (P : pred I) (F : I -> nat) (p : nat) :
  (forall n,  P n -> (0 < F n)%N) ->
  (logn p (\prod_(n <- r | P n) F n) = \sum_(n <- r | P n) logn p (F n))%N.
Proof.
move=> F_gt0; elim/(big_load (fun n => (n > 0)%N)): _.
elim/big_rec2: _; first by rewrite logn1.
by move=> i m n Pi [n_gt0 <-]; rewrite muln_gt0 lognM ?F_gt0.
Qed.

End Temp.
