From stdpp Require Import numbers.
From Coq Require Import ssreflect.
From machine_utils Require Export finz.

(* Some extra theorems *)
Lemma finz_even_mul2 {z} (n : finz.finz z) ( m : Z) :
  finz.of_z (2*m) = Some n ->
  Z.even n = true.
Proof.
  intros H.
  replace (Z.to_nat n) with (2 * Z.to_nat m) by solve_finz.
  apply finz_of_z_is_Some_spec in H.
  replace (@finz.to_z z n) with (2*m)%Z.
  replace (2 * m)%Z with (0 + 2 * m)%Z by lia.
  rewrite Z.even_add_mul_2.
  done.
Qed.

Lemma finz_of_z_add_None {z} (n : finz.finz z) (i : Z) :
  @finz.of_z z (n + i) = None ->
  (n + i)%f = None.
Proof.
  intros Hof_z.
  rewrite /finz.of_z in Hof_z.
  destruct ( Z.lt_dec (n+i)%Z z ); try solve_finz.
  destruct (Z.le_dec 0%Z (n+i)%Z); try solve_finz.
Qed.
