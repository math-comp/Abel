From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section Temp.

(* NB : rpredM and mulrPred uses that 1 is in the subset, which is useless.
  Predicates should be defined for {aspace aT}. *)







Definition Zp_succ n (i : 'I_n) :=
  match i with
  | @Ordinal _ k klt => Ordinal (
      match n as n0 return (k < n0)%N -> (k.+1 %% n0 < n0)%N with
      | 0 => id
      | n0.+1 => fun=> ltn_pmod k.+1 (is_true_true : 0 < n0.+1)%N
      end klt)
  end.





End Temp.
