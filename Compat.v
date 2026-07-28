(* Compatibility layer for recent Rocq versions.

   The [Coq.Arith.Plus], [Coq.Arith.Mult], [Coq.Arith.Lt] ... modules used to
   export a large number of lemmas under their historical names.  Those names
   have been removed from the standard library in favour of the [Nat.*] ones.
   This file re-establishes exactly the names used by this development, so that
   the proof scripts below need no change. *)

Require Import Arith.
Require Import PeanoNat.
Require Import Lia.

Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof. lia. Qed.

Lemma plus_0_r : forall n : nat, n + 0 = n.
Proof. lia. Qed.

Lemma plus_Snm_nSm : forall n m : nat, S n + m = n + S m.
Proof. lia. Qed.

Lemma plus_le_compat : forall n m p q : nat, n <= m -> p <= q -> n + p <= m + q.
Proof. lia. Qed.

Lemma plus_le_compat_l : forall n m p : nat, n <= m -> p + n <= p + m.
Proof. lia. Qed.

Lemma plus_le_reg_l : forall n m p : nat, p + n <= p + m -> n <= m.
Proof. lia. Qed.

Lemma minus_n_O : forall n : nat, n = n - 0.
Proof. lia. Qed.

Lemma mult_comm : forall n m : nat, n * m = m * n.
Proof. exact Nat.mul_comm. Qed.

Lemma mult_assoc : forall n m p : nat, n * (m * p) = n * m * p.
Proof. exact Nat.mul_assoc. Qed.

Lemma mult_0_r : forall n : nat, n * 0 = 0.
Proof. exact Nat.mul_0_r. Qed.

Lemma mult_1_l : forall n : nat, 1 * n = n.
Proof. exact Nat.mul_1_l. Qed.

Lemma mult_1_r : forall n : nat, n * 1 = n.
Proof. exact Nat.mul_1_r. Qed.

Lemma le_trans : forall n m p : nat, n <= m -> m <= p -> n <= p.
Proof. lia. Qed.

Lemma le_lt_trans : forall n m p : nat, n <= m -> m < p -> n < p.
Proof. lia. Qed.

Lemma le_lt_or_eq : forall n m : nat, n <= m -> n < m \/ n = m.
Proof. lia. Qed.

Lemma le_not_lt : forall n m : nat, n <= m -> ~ m < n.
Proof. lia. Qed.

Lemma le_or_lt : forall n m : nat, n <= m \/ m < n.
Proof. lia. Qed.

Lemma lt_trans : forall n m p : nat, n < m -> m < p -> n < p.
Proof. lia. Qed.

Lemma lt_le_trans : forall n m p : nat, n < m -> m <= p -> n < p.
Proof. lia. Qed.

Lemma lt_le_weak : forall n m : nat, n < m -> n <= m.
Proof. lia. Qed.

Lemma lt_n_S : forall n m : nat, n < m -> S n < S m.
Proof. lia. Qed.

Lemma lt_S_n : forall n m : nat, S n < S m -> n < m.
Proof. lia. Qed.

Lemma lt_n_O : forall n : nat, ~ n < 0.
Proof. lia. Qed.

Lemma lt_asym : forall n m : nat, n < m -> ~ m < n.
Proof. lia. Qed.

Lemma lt_not_le : forall n m : nat, n < m -> ~ m <= n.
Proof. lia. Qed.

Lemma lt_plus_trans : forall n m p : nat, n < m -> n < m + p.
Proof. lia. Qed.

Lemma S_pred : forall n m : nat, m < n -> n = S (Nat.pred n).
Proof. lia. Qed.

Lemma plus_lt_compat_l : forall n m p : nat, n < m -> p + n < p + m.
Proof. lia. Qed.

Lemma plus_lt_compat_r : forall n m p : nat, n < m -> n + p < m + p.
Proof. lia. Qed.

Lemma plus_lt_compat : forall n m p q : nat, n < m -> p < q -> n + p < m + q.
Proof. lia. Qed.

Lemma plus_le_compat_r : forall n m p : nat, n <= m -> n + p <= m + p.
Proof. lia. Qed.

Lemma plus_lt_reg_l : forall n m p : nat, p + n < p + m -> n < m.
Proof. lia. Qed.

Lemma plus_reg_l : forall n m p : nat, p + n = p + m -> n = m.
Proof. lia. Qed.

Lemma plus_assoc : forall n m p : nat, n + (m + p) = n + m + p.
Proof. lia. Qed.

Lemma plus_assoc_reverse : forall n m p : nat, n + m + p = n + (m + p).
Proof. lia. Qed.

Lemma le_plus_l : forall n m : nat, n <= n + m.
Proof. lia. Qed.

Lemma le_plus_r : forall n m : nat, m <= n + m.
Proof. lia. Qed.

Lemma le_plus_trans : forall n m p : nat, n <= m -> n <= m + p.
Proof. lia. Qed.

Lemma le_antisym : forall n m : nat, n <= m -> m <= n -> n = m.
Proof. lia. Qed.

Lemma le_Sn_O : forall n : nat, ~ S n <= 0.
Proof. lia. Qed.

Lemma le_Sn_n : forall n : nat, ~ S n <= n.
Proof. lia. Qed.

Lemma le_O_n : forall n : nat, 0 <= n.
Proof. lia. Qed.

Lemma le_n_O_eq : forall n : nat, n <= 0 -> 0 = n.
Proof. lia. Qed.

Lemma lt_n_Sn : forall n : nat, n < S n.
Proof. lia. Qed.

Lemma lt_O_Sn : forall n : nat, 0 < S n.
Proof. lia. Qed.

Lemma neq_O_lt : forall n : nat, 0 <> n -> 0 < n.
Proof. lia. Qed.

Lemma lt_O_neq : forall n : nat, 0 < n -> 0 <> n.
Proof. lia. Qed.

Lemma minus_n_n : forall n : nat, 0 = n - n.
Proof. lia. Qed.

Lemma le_plus_minus : forall n m : nat, n <= m -> m = n + (m - n).
Proof. lia. Qed.

Lemma le_plus_minus_r : forall n m : nat, n <= m -> n + (m - n) = m.
Proof. lia. Qed.

Lemma minus_plus : forall n m : nat, n + m - n = m.
Proof. lia. Qed.

Lemma plus_minus : forall n m p : nat, n = m + p -> p = n - m.
Proof. lia. Qed.

Lemma mult_plus_distr_r : forall n m p : nat, (n + m) * p = n * p + m * p.
Proof. exact Nat.mul_add_distr_r. Qed.

Lemma mult_plus_distr_l : forall n m p : nat, n * (m + p) = n * m + n * p.
Proof. exact Nat.mul_add_distr_l. Qed.

Lemma mult_le_compat_l : forall n m p : nat, n <= m -> p * n <= p * m.
Proof. intros; apply Nat.mul_le_mono_l; assumption. Qed.

Lemma mult_le_compat_r : forall n m p : nat, n <= m -> n * p <= m * p.
Proof. intros; apply Nat.mul_le_mono_r; assumption. Qed.

Lemma mult_O_le : forall n m : nat, m = 0 \/ n <= m * n.
Proof.
  intros n [|m]; [ left; reflexivity | right ].
  simpl; apply Nat.le_add_r.
Qed.
