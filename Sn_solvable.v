From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable.

Section Perm_solvable.

Variable T : finType.

Lemma not_solvable_Alt : 4 < #|T| -> ~ solvable 'Alt_T.
Proof.
move=> card_T Alt_solvable.
have/simple_Alt5 Alt_simple := card_T. 
have:= simple_sol_prime Alt_solvable Alt_simple.
have lt_T n : n <= 4 -> n < #|T| by move/leq_ltn_trans; apply.
have -> : #|('Alt_T)%G| = #|T|`! %/ 2 by rewrite -card_Alt ?mulKn ?lt_T. 
move/even_prime => [/eqP|]; apply/negP.
  rewrite neq_ltn leq_divRL // mulnC -[2 * 3]/(3`!).
  by apply/orP; right; apply/ltnW/fact_smonotone/lt_T.
by rewrite -dvdn2 dvdn_divRL dvdn_fact //=; apply/ltnW/lt_T. 
Qed.

Lemma not_solvable_Sym : 4 < #|T| -> ~ solvable 'Sym_T.
Proof.
move=> /not_solvable_Alt /negP/negbTE Alt_solvN.
by rewrite (series_sol (Alt_normal T)) Alt_solvN.
Qed.

End Perm_solvable.