(* Copyright (c) 2013, Louis Parlant and Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import prelude.

Reserved Notation "Σ@{ i , k , n } s"
  (at level 20, i at level 1, k at level 1, n at level 1,
   right associativity, format "Σ@{ i , k , n }  s").
Fixpoint Ssigmas (i k n : nat) (s : Stream nat) : Stream nat :=
  match n with
  | 0 => Σ@{i,k} s
  | S n => Σ@{i,k} Σ@{S i,S k,n} s
  end
where "Σ@{ i , k , n } s" := (Ssigmas i k n s).
Instance: ∀ n k i, Proper (equal ==> equal) (Ssigmas i k n).
Proof. induction n; simpl; intros; solve_proper. Qed.

Inductive Rn : Stream nat → Stream nat → Prop :=
  | Rn_sig1 n : Rn (Σ@{1,2,n} #1) (nats ^^ S n)
  | Rn_sig2 n : Rn (Σ@{0,2,n} #1) (nats ⊙ (nats ⊕ #1) ^^ n)
  | Rn_refl s : Rn s s
  | Rn_plus a1 b1 a2 b2 : Rn a1 b1 → Rn a2 b2 → Rn (a1 ⊕ a2) (b1 ⊕ b2)
  | Rn_eq s t u v : s ≡ u → t ≡ v → Rn u v → Rn s t.

Instance: Proper (equal ==> equal ==> iff) Rn.
Proof. now split; apply Rn_eq. Qed.
Lemma Rn_mult_all_l n a b : Rn a b → Rn (#n ⊙ a) (#n ⊙ b).
Proof.
  induction n as [|n IH]; [rewrite !Smult_0_l; constructor |].
  rewrite repeat_S, !Smult_plus_distr_r, !Smult_1_l. repeat constructor; auto.
Qed.

(** Proposition 5.1 *)
Lemma nats_pow_head n : head (nats ^^ n) = 1.
Proof. now rewrite Spow_head, Sfrom_head, Nat.pow_1_l. Qed.

Fixpoint nat_seq (n : nat) : Stream nat :=
  match n with
  | 0 => nats ⊕ #1
  | S n => nats ⊙ (nats ⊕ #1) ^^ S n ⊕ nat_seq n
  end.
Lemma nats_pow_tail n : (nats ^^ S n)` ≡ nat_seq n.
Proof.
  rewrite Spow_tail, Snats_tail, Spow_S.
  induction n as [|n IH]; simpl; rewrite ?Spow_0, ?Spow_S, <-?IH; ring.
Qed.

(** Proposition 5.2 *)
Lemma Ssigmas_head_S i k n : head (Σ@{S i,k,n} #1) = 1.
Proof.
  revert i k. induction n as [|n IH]; intros i k; simpl.
  { now rewrite Ssigma_head_S. }
  now rewrite Ssigma_head_S, IH.
Qed.

Fixpoint sig_seq (i k n : nat) : Stream nat :=
  match n with
  | 0 => Σ@{i,k} #1 ⊕ #1
  | S n => Σ@{i,k,S n} #1 ⊕ sig_seq i k n
  end.
Lemma sigseq_S i k n :
  sig_seq i k (S n) ≡ Σ@{i,k} (sig_seq (S i) (S k) n) ⊕ #1.
Proof.
  simpl. revert i k. induction n as [|n IH]; intros i k; simpl.
  { rewrite Ssigma_plus. ring. }
  rewrite IH, !Ssigma_plus. ring.
Qed.
Lemma Ssigmas_S_tail i k n : (Σ@{S i,k,n} #1)` ≡ sig_seq i k n.
Proof.
  revert i k. induction n as [|n IH]; intros i k; simpl.
  { now rewrite Ssigma_tail_S. }
  now rewrite !Ssigma_tail_S, Ssigmas_head_S, IH, <-sigseq_S.
Qed.

(** Proposition 5.3 *)
Lemma nats_nats_pow_head n : head (nats ⊙ (nats ⊕ #1) ^^ n) = 2 ^ n.
Proof.
  rewrite !zip_with_head, Spow_head,
    zip_with_head, Sfrom_head, repeat_head; simpl; ring.
Qed.

Fixpoint bin (i j : nat) : nat :=
  match i, j with
  | i, O => 1
  | O, S j => 0
  | S i, S j => bin i (S j) + bin i j
  end.
Lemma bin_0 i : bin i 0 = 1.
Proof. now destruct i. Qed.
Lemma bin_overflow i j : i < j → bin i j = 0.
Proof.
  revert j; induction i as [|i IH]; intros [|j] ?; simpl; rewrite ?IH; omega.
Qed.
Lemma bin_diag i : bin i i = 1.
Proof.
  induction i as [|i IH]; simpl; auto. rewrite IH, bin_overflow; omega.
Qed.

Fixpoint bins (i j : nat) : nat :=
  match j with 
  | 0 => 1
  | S j => bin i (S j) + bins i j
  end.
Lemma bins_0 j : bins j 0 = 1.
Proof. induction j; simpl; auto. Qed.
Lemma bins_S i j : bins (S i) (S j) = bins i (S j) + bins i j.
Proof.
  simpl. rewrite <-!Nat.add_assoc, Nat.add_cancel_l.
  revert i. induction j as [|j IH]; intros i; simpl.
  { now rewrite bin_0. }
  transitivity (bin i (S j) + (bin i (S j) +
    (bins i j + bins i j))); [rewrite <-IH; ring|ring].
Qed.
Lemma bins_pred i j :
  0 < i →  0 < j → bins i j = bins (pred i) j + bins (pred i) (pred j).
Proof. intros. destruct i as [|i], j as [|j]; try omega. apply bins_S. Qed.
Lemma bins_SS i : bins (S i) (S i) = bins i i + bins i i.
Proof. rewrite bins_S; simpl. rewrite bin_overflow by omega. ring. Qed.
Lemma bins_diag i : bins i i = 2 ^ i.
Proof.
  induction i as [|i IH]; [easy|].
  rewrite Nat.pow_succ_r, bins_SS, IH by omega. ring.
Qed.

Fixpoint bins_seq (n j : nat) : Stream nat :=
  match j with
  | 0 => #bins n n ⊙ (nats ⊕ #1)
  | S j => #bins n (n - S j) ⊙ nats ⊙ (nats ⊕ #1) ^^ S j ⊕ bins_seq n j
  end.
Arguments bins _ _ : simpl never.
Arguments bins_seq _ _ : simpl never.
Definition bins_seq_0 n : bins_seq n 0 = #bins n n ⊙ (nats ⊕ #1) := eq_refl.
Definition bins_seq_S n j : bins_seq n (S j) =
  #bins n (n - S j) ⊙ nats ⊙ (nats ⊕ #1) ^^ S j ⊕ bins_seq n j := eq_refl.

Lemma bins_seq_SS_help n j :
  j < n → bins_seq (S n) (S j) ≡
    (nats ⊕ #2) ⊙ bins_seq n j ⊕ #bins n (n - S j) ⊙ nats ⊙ (nats ⊕ #1) ^^ S j.
Proof.
  induction j as [|j IH]; intros Hjn.
  { rewrite !bins_seq_S, !bins_seq_0, Nat.sub_succ, Nat.sub_0_r.
    rewrite bins_SS, (bins_pred (S n) n) by omega.
    rewrite !Nat.pred_succ, Spow_1, !(repeat_zip_with plus), (repeat_S 1).
    rewrite <-Nat.sub_1_r. ring. }
  rewrite bins_seq_S, Nat.sub_succ_l, IH, Spow_S, bins_S by omega.
  rewrite <-Nat.sub_succ_l, Nat.sub_succ, (repeat_zip_with plus) by omega.
  rewrite bins_seq_S, !(repeat_S 1). ring.
Qed.
Lemma bins_seq_SS n : bins_seq (S n) (S n) ≡ (nats ⊕ #2) ⊙ bins_seq n n.
Proof.
  destruct n as [|n].
  { rewrite bins_seq_S, !bins_seq_0. unfold bins; simpl.
    rewrite Spow_1, (repeat_S 1). ring. }
  rewrite bins_seq_S, bins_seq_SS_help, bins_seq_S by omega.
  rewrite !Nat.sub_diag, !bins_0, Spow_S, !(repeat_S 1). ring.
Qed.
Lemma nats_nats_pow_tail n : (nats ⊙ (nats ⊕ #1) ^^ n)` ≡ bins_seq n n.
Proof.
  rewrite zip_with_tail, Spow_tail, zip_with_tail, Snats_tail, repeat_tail.
  rewrite Splus_assoc, <-repeat_zip_with; simpl. induction n as [|n IH].
  { rewrite Spow_0, bins_seq_0. unfold bins; simpl. ring. }
  rewrite Spow_S, <-(Smult_assoc (nats ⊕ #1)), (Smult_comm (nats ⊕ #1)).
  now rewrite (Smult_assoc (nats ⊕ #2)), IH, bins_seq_SS.
Qed.

(** Proposition 5.4 *)
Lemma sigseq_0_head k n : head (sig_seq 0 (S k) n) = 2 ^ S n.
Proof.
  revert k. induction n as [|n IH]; intros k; simpl; [easy|].
  rewrite zip_with_head, Ssigma_head_0, Ssigmas_S_tail.
  rewrite Nat.pow_succ_r, !IH by omega. ring.
Qed.
Lemma Ssigmas_0_head k n : head (Σ@{0,k,n} #1) = 2 ^ n.
Proof.
  destruct n as [|n]; simpl; [easy|].
  now rewrite Ssigma_head_0, Ssigmas_S_tail, sigseq_0_head.
Qed.

Fixpoint bins_sig_seq (n k j : nat) : Stream nat :=
  match j with
  | 0 => #bins n n ⊙ (Σ@{k - 2,k} #1 ⊕ #1)
  | S j => #bins n (n - S j) ⊙ Σ@{k - 2,k,S j} #1 ⊕ bins_sig_seq n k j
  end.
Arguments bins_sig_seq _ _ _ : simpl never.
Definition bins_sig_seq_0 n k :
  bins_sig_seq n k 0 = #bins n n ⊙ (Σ@{k - 2,k} #1 ⊕ #1) := eq_refl.
Definition bins_sig_seq_S n k j : bins_sig_seq n k (S j) =
  #bins n (n - S j) ⊙ Σ@{k - 2,k,S j} #1 ⊕ bins_sig_seq n k j := eq_refl.

Lemma bins_sig_seq_SS_help n k j :
  2 ≤ k → j < n → bins_sig_seq (S n) k (S j) ≡
    Σ@{(k - 2),k} bins_sig_seq n (S k) j ⊕ bins_sig_seq n k j
    ⊕ #bins n (n - S j) ⊙ Σ@{(k - 2),k,S j} #1 ⊕ #bins n n.
Proof.
  intros Hk. induction j as [|j IH]; intros Hjn.
  { rewrite bins_sig_seq_S, !bins_sig_seq_0; simpl.
    rewrite Nat.sub_0_r, <-Nat.sub_succ_l, Nat.sub_succ by easy.
    rewrite bins_SS, (repeat_zip_with plus), Smult_plus_distr_r.
    rewrite Ssigma_mult, Ssigma_plus, (Smult_plus_distr_l (#bins n n)).
    rewrite bins_pred, !Nat.pred_succ, <-Nat.sub_1_r by omega.
    rewrite (repeat_zip_with plus). ring. }
  rewrite bins_sig_seq_S, Nat.sub_succ_l, IH, bins_S by omega; simpl.
  rewrite <-!Nat.sub_succ_l, !Nat.sub_succ, Nat.sub_0_r by omega.
  rewrite (repeat_zip_with plus).
  rewrite !bins_sig_seq_S, Ssigma_plus, Ssigma_mult; simpl.
  rewrite <-!Nat.sub_succ_l, !Nat.sub_succ, Nat.sub_0_r by omega. ring.
Qed.
Lemma bins_sig_seq_SS n k :
  2 ≤ k → bins_sig_seq (S n) k (S n) ≡
    Σ@{(k - 2),k} bins_sig_seq n (S k) n ⊕ bins_sig_seq n k n ⊕ #bins n n.
Proof.
  intros Hk. destruct n as [|n].
  { rewrite bins_sig_seq_S, !bins_sig_seq_0. unfold bins, pow; simpl.
    rewrite <-Nat.sub_succ_l, Nat.sub_succ by easy.
    rewrite !(repeat_S 1). rewrite Ssigma_mult, Ssigma_plus. ring. }
  rewrite bins_sig_seq_S, bins_sig_seq_SS_help by omega.
  rewrite !bins_sig_seq_S; simpl. rewrite !Nat.sub_diag, !bins_0.
  rewrite <-!Nat.sub_succ_l, !Nat.sub_succ, Nat.sub_0_r by omega.
  rewrite Ssigma_plus, Ssigma_mult. ring.
Qed.
Lemma Ssigmas_0_tail n k : 2 ≤ k → (Σ@{0,k,n} #1)` ≡ bins_sig_seq n k n.
Proof.
  intros Hk. destruct n as [|n]; simpl.
  { rewrite bins_sig_seq_0, Ssigma_tail_0, !repeat_tail, repeat_head.
    unfold bins; simpl. ring. }
  rewrite Ssigma_tail_0, Ssigmas_S_tail, sigseq_0_head.
  revert k Hk. induction n as [|n IH]; intros k Hk; simpl.
  { rewrite bins_sig_seq_S, bins_sig_seq_0.
    rewrite zip_with_tail, Ssigma_tail_0, !repeat_tail, repeat_head.
    unfold bins, pow; simpl. rewrite !Ssigma_plus, (repeat_S 1).
    rewrite <-Nat.sub_succ_l, Nat.sub_succ by easy. ring. }
  rewrite zip_with_tail, Ssigma_tail_0, Ssigmas_S_tail, sigseq_0_head.
  rewrite IH, Ssigma_plus by omega.
  rewrite Nat.pow_succ_r by omega; simpl; rewrite Nat.add_0_r.
  rewrite repeat_zip_with, Splus_assoc, <-(Splus_assoc _ (#_)), IH by easy.
  now rewrite (bins_sig_seq_SS (S n)), bins_diag, Splus_assoc by easy.
Qed.

(** The final theorem *)
Lemma bisimulation_Rn : bisimulation Rn.
Proof.
  intros s t Hst; split.
  { induction Hst.
    * now rewrite Ssigmas_head_S, nats_pow_head.
    * now rewrite Ssigmas_0_head, nats_nats_pow_head.
    * easy.
    * rewrite !zip_with_head; congruence.
    * now rewrite H, H0. }
  induction Hst.
  * rewrite nats_pow_tail, Ssigmas_S_tail. induction n as [|n IH]; simpl.
    { repeat constructor. rewrite <-(Smult_1_r nats). apply (Rn_sig2 0). }
    constructor; auto. apply (Rn_sig2 (S n)).
  * rewrite Ssigmas_0_tail, nats_nats_pow_tail by easy.
    generalize n at 1 3. induction n as [|j IH]; intros n; simpl.
    { apply Rn_mult_all_l; repeat constructor.
      rewrite <-(Smult_1_r nats). apply (Rn_sig2 0). }
    constructor; auto. rewrite Smult_assoc.
    apply Rn_mult_all_l, (Rn_sig2 (S j)).
  * constructor.
  * now constructor.
  * now rewrite H, H0.
Qed.
Theorem Moessner n : Σ@{1,2,n} #1 ≡ nats ^^ S n.
Proof. apply (bisimulation_equal _ _ _ bisimulation_Rn). constructor. Qed.
