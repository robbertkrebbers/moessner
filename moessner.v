(* Copyright (c) 2013, Louis Parlant and Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import prelude.

Reserved Notation "Σ@{ i , k , n } s"
  (at level 20, i at level 1, k at level 1, n at level 1,
   right associativity, format "Σ@{ i , k , n }  s").
Fixpoint Ssigmas (i k n : nat) (s : Stream Z) : Stream Z :=
  match n with
  | O => Σ@{i,k} s
  | S n => Σ@{i,k} Σ@{S i,S k,n} s
  end
where "Σ@{ i , k , n } s" := (Ssigmas i k n s).
Instance: ∀ n i k, Proper (equal ==> equal) (Ssigmas i k n).
Proof. induction n; simpl; intros; solve_proper. Qed.
Lemma Ssigmas_S_alt i k n s : Σ@{i,k,S n} s = Σ@{i,k,n} Σ@{S(i+n),S(k+n)} s.
Proof.
  revert i k; simpl. induction n as [|n IH]; intros i k; simpl.
  { now rewrite !Nat.add_0_r. }
  now rewrite IH, !Nat.add_succ_r.
Qed.
Lemma Ssigmas_plus s t i k n : Σ@{i,k,n} (s ⊕ t) ≡ Σ@{i,k,n} s ⊕ Σ@{i,k,n} t.
Proof.
  revert i k.
  now induction n as [|n IH]; intros; simpl; rewrite ?IH, ?Ssigma_plus.
Qed.
Lemma Ssigmas_0 i k n : Σ@{i,k,n} #0 ≡ #0.
Proof.
  revert i k.
  now induction n as [|n IH]; intros; simpl; rewrite ?IH, ?Ssigma_0.
Qed.
Lemma Ssigmas_mult n' s i k n : Σ@{i,k,n} (#n' ⊙ s) ≡ #n' ⊙ Σ@{i,k,n} s.
Proof.
  revert i k.
  now induction n as [|n IH]; intros; simpl; rewrite ?IH, ?Ssigma_mult.
Qed.

Inductive Rn : relation (Stream Z) :=
  | Rn_sig1 n : Rn (Σ@{1,2,n} #1) (nats ^^ S n)
  | Rn_sig2 n : Rn (Σ@{0,2,n} #1) (nats ⊙ (#1 ⊕ nats) ^^ n)
  | Rn_refl s : Rn s s
  | Rn_plus s1 s2 t1 t2 : Rn s1 t1 → Rn s2 t2 → Rn (s1 ⊕ s2) (t1 ⊕ t2)
  | Rn_mult n s t : Rn s t → Rn (#n ⊙ s) (#n ⊙ t)
  | Rn_eq s1 s2 t1 t2 : s1 ≡ s2 → t1 ≡ t2 → Rn s1 t1 → Rn s2 t2.

Instance: Proper (equal ==> equal ==> iff) Rn.
Proof. now split; apply Rn_eq. Qed.

(** Proposition 5.1 *)
Lemma nats_pow_head n : head (nats ^^ n) = 1.
Proof. now rewrite Spow_head, Sfrom_head, Z.pow_1_l by omega. Qed.

Fixpoint nat_seq (n : nat) : Stream Z :=
  match n with
  | O => #1 ⊕ nats
  | S n => nats ⊙ (#1 ⊕ nats) ^^ S n ⊕ nat_seq n
  end.
Lemma nats_pow_tail n : (nats ^^ S n)` ≡ nat_seq n.
Proof.
  rewrite Spow_tail, Sfrom_tail, Spow_S.
  induction n as [|n IH]; simpl; rewrite ?Spow_0, ?Spow_S, <-?IH; ring.
Qed.

(** Proposition 5.2 *)
Lemma Ssigmas_head_S i k n : head (Σ@{S i,k,n} #1) = 1.
Proof.
  revert i k. induction n as [|n IH]; intros i k; simpl.
  { now rewrite Ssigma_head_S. }
  now rewrite Ssigma_head_S, IH.
Qed.

Fixpoint sig_seq (i k n : nat) : Stream Z :=
  match n with
  | O => #1 ⊕ Σ@{i,k} #1
  | S n => Σ@{i,k,S n} #1 ⊕ sig_seq i k n
  end.
Lemma sigseq_S i k n : sig_seq i k (S n) ≡ #1 ⊕ Σ@{i,k} sig_seq (S i) (S k) n.
Proof.
  simpl. revert i k. induction n as [|n IH]; intros i k; simpl.
  { rewrite Ssigma_plus. ring. }
  rewrite IH, !Ssigma_plus. ring.
Qed.
Lemma Ssigmas_S_tail i k n : (Σ@{S i,k,n} #1)` ≡ sig_seq i k n.
Proof.
  revert i k. induction n as [|n IH]; intros i k; simpl.
  { rewrite Ssigma_tail_S, repeat_tail, repeat_head. ring. }
  now rewrite !Ssigma_tail_S, Ssigmas_head_S, IH, <-sigseq_S.
Qed.

(** Proposition 5.3 *)
Lemma nats_nats_pow_head n : head (nats ⊙ (#1 ⊕ nats) ^^ n) = 2 ^ n.
Proof.
  now rewrite !zip_with_head, Spow_head,
    zip_with_head, Sfrom_head, repeat_head, Z.mul_1_l.
Qed.

Fixpoint bin (n i : nat) : Z :=
  match n, i with
  | n, O => 1
  | O, S i => 0
  | S n, S i => bin n (S i) + bin n i
  end.
Lemma bin_0 n : bin n 0 = 1.
Proof. now destruct n. Qed.
Lemma bin_overflow n i : (n < i)%nat → bin n i = 0.
Proof.
  revert i; induction n as [|n IH]; intros [|i] ?; simpl; rewrite ?IH; omega.
Qed.
Lemma bin_diag n : bin n n = 1.
Proof.
  induction n as [|n IH]; simpl; auto. rewrite IH, bin_overflow; omega.
Qed.

Fixpoint bins (n i : nat) : Z :=
  match i with O => 1 | S i => bin n (S i) + bins n i end.
Lemma bins_0 n : bins n 0 = 1.
Proof. induction n; simpl; auto. Qed.
Lemma bins_S n i : bins (S n) (S i) = bins n (S i) + bins n i.
Proof.
  simpl. rewrite <-!Z.add_assoc, Z.add_cancel_l.
  revert n. induction i as [|i IH]; intros n; simpl; [now rewrite bin_0 |].
  transitivity (bin n (S i) + (bin n (S i) +
    (bins n i + bins n i))); [rewrite <-IH; ring|ring].
Qed.
Lemma bins_pred n i :
  (0 < n)%nat → (0 < i)%nat →
  bins n i = bins (pred n) i + bins (pred n) (pred i).
Proof. intros. destruct n as [|n], i as [|i]; try omega. apply bins_S. Qed.
Lemma bins_SS n : bins (S n) (S n) = bins n n + bins n n.
Proof. rewrite bins_S; simpl. rewrite bin_overflow by omega. ring. Qed.
Lemma bins_diag n : bins n n = 2 ^ n.
Proof.
  induction n as [|n IH]; [easy|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r, bins_SS, IH by omega. ring.
Qed.

Fixpoint bins_seq (n j : nat) : Stream Z :=
  match j with
  | O => #bins n n ⊙ (#1 ⊕ nats)
  | S j => #bins n (n - S j) ⊙ nats ⊙ (#1 ⊕ nats) ^^ S j ⊕ bins_seq n j
  end.
Arguments bins _ _ : simpl never.
Arguments bins_seq _ _ : simpl never.
Definition bins_seq_0 n :
  bins_seq n 0 = #bins n n ⊙ (#1 ⊕ nats) := eq_refl.
Definition bins_seq_S n j : bins_seq n (S j) =
  #bins n (n - S j) ⊙ nats ⊙ (#1 ⊕ nats) ^^ S j ⊕ bins_seq n j := eq_refl.

Lemma bins_seq_SS_help n j :
  (j < n)%nat → bins_seq (S n) (S j) ≡
    (nats ⊕ #2) ⊙ bins_seq n j ⊕ #bins n (n - S j) ⊙ nats ⊙ (#1 ⊕ nats) ^^ S j.
Proof.
  induction j as [|j IH]; intros Hjn.
  { rewrite !bins_seq_S, !bins_seq_0, Nat.sub_succ, Nat.sub_0_r.
    rewrite bins_SS, (bins_pred (S n) n) by omega.
    rewrite !Nat.pred_succ, Spow_1, !(repeat_zip_with Z.add).
    rewrite <-Nat.sub_1_r, repeat_2. ring. }
  rewrite bins_seq_S, Nat.sub_succ_l, IH, Spow_S, bins_S by omega.
  rewrite <-Nat.sub_succ_l, Nat.sub_succ by omega.
  rewrite (repeat_zip_with Z.add), bins_seq_S, !repeat_2  by omega. ring.
Qed.
Lemma bins_seq_SS n : bins_seq (S n) (S n) ≡ (#2 ⊕ nats) ⊙ bins_seq n n.
Proof.
  destruct n as [|n].
  { rewrite bins_seq_S, !bins_seq_0. unfold bins; simpl.
    rewrite Z.add_0_l, Spow_1, repeat_2, repeat_zip_with. ring. }
  rewrite bins_seq_S, bins_seq_SS_help, bins_seq_S by omega.
  rewrite !Nat.sub_diag, !bins_0, Spow_S, !repeat_2. ring.
Qed.
Lemma nats_nats_pow_tail n : (nats ⊙ (#1 ⊕ nats) ^^ n)` ≡ bins_seq n n.
Proof.
  rewrite zip_with_tail, Spow_tail, zip_with_tail, Sfrom_tail, repeat_tail.
  rewrite <-Splus_assoc, <-repeat_2. induction n as [|n IH].
  { rewrite Spow_0, bins_seq_0. unfold bins; simpl. ring. }
  rewrite Spow_S, <-(Smult_assoc (#1 ⊕ nats)), (Smult_comm (#1 ⊕ nats)).
  now rewrite (Smult_assoc (#2 ⊕ nats)), IH, bins_seq_SS.
Qed.

(** Proposition 5.4 *)
Lemma sigseq_0_head k n : head (sig_seq 0 (S k) n) = 2 ^ S n.
Proof.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by omega.
  revert k. induction n as [|n IH]; intros k; simpl; [easy|].
  rewrite Zpos_P_of_succ_nat, Z.pow_succ_r by omega.
  rewrite zip_with_head, Ssigma_head_0, Ssigmas_S_tail, !IH. ring.
Qed.
Lemma Ssigmas_0_head k n : head (Σ@{0,k,n} #1) = 2 ^ n.
Proof.
  destruct n as [|n]; simpl; [easy|].
  now rewrite Ssigma_head_0, Ssigmas_S_tail, sigseq_0_head.
Qed.

Fixpoint bins_sig_seq (n k j : nat) : Stream Z :=
  match j with
  | O => #bins n n ⊙ (#1 ⊕ Σ@{k - 2,k} #1)
  | S j => #bins n (n - S j) ⊙ Σ@{k - 2,k,S j} #1 ⊕ bins_sig_seq n k j
  end.
Arguments bins_sig_seq _ _ _ : simpl never.
Definition bins_sig_seq_0 n k :
  bins_sig_seq n k 0 = #bins n n ⊙ (#1 ⊕ Σ@{k - 2,k} #1) := eq_refl.
Definition bins_sig_seq_S n k j : bins_sig_seq n k (S j) =
  #bins n (n - S j) ⊙ Σ@{k - 2,k,S j} #1 ⊕ bins_sig_seq n k j := eq_refl.

Lemma bins_sig_seq_SS_help n k j :
  (2 ≤ k)%nat → (j < n)%nat → bins_sig_seq (S n) k (S j) ≡
    Σ@{(k - 2),k} bins_sig_seq n (S k) j ⊕ bins_sig_seq n k j
    ⊕ #bins n (n - S j) ⊙ Σ@{(k - 2),k,S j} #1 ⊕ #bins n n.
Proof.
  intros Hk. induction j as [|j IH]; intros Hjn.
  { rewrite bins_sig_seq_S, !bins_sig_seq_0; simpl.
    rewrite Nat.sub_0_r, <-Nat.sub_succ_l, Nat.sub_succ by easy.
    rewrite bins_SS, (repeat_zip_with Z.add), Smult_plus_distr_r.
    rewrite Ssigma_mult, Ssigma_plus, (Smult_plus_distr_l (#bins n n)).
    rewrite bins_pred, !Nat.pred_succ, <-Nat.sub_1_r by omega.
    rewrite (repeat_zip_with Z.add). ring. }
  rewrite bins_sig_seq_S, Nat.sub_succ_l, IH, bins_S by omega; simpl.
  rewrite <-!Nat.sub_succ_l, !Nat.sub_succ, Nat.sub_0_r by omega.
  rewrite (repeat_zip_with Z.add).
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
    rewrite !repeat_2. rewrite Ssigma_mult, Ssigma_plus. ring. }
  rewrite bins_sig_seq_S, bins_sig_seq_SS_help by omega.
  rewrite !bins_sig_seq_S; simpl. rewrite !Nat.sub_diag, !bins_0.
  rewrite <-!Nat.sub_succ_l, !Nat.sub_succ, Nat.sub_0_r by omega.
  rewrite Ssigma_plus, Ssigma_mult. ring.
Qed.
Lemma Ssigmas_0_tail k n : 2 ≤ k → (Σ@{0,k,n} #1)` ≡ bins_sig_seq n k n.
Proof.
  intros Hk. destruct n as [|n]; simpl.
  { rewrite bins_sig_seq_0, Ssigma_tail_0, !repeat_tail, repeat_head.
    unfold bins; simpl. ring. }
  rewrite Ssigma_tail_0, Ssigmas_S_tail, sigseq_0_head.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by omega.
  revert k Hk. induction n as [|n IH]; intros k Hk; simpl.
  { rewrite bins_sig_seq_S, bins_sig_seq_0.
    rewrite zip_with_tail, Ssigma_tail_0, !repeat_tail, repeat_head.
    unfold bins; simpl. rewrite Z.pow_0_r, Z.add_0_l, !repeat_zip_with.
    rewrite !Ssigma_plus, repeat_2.
    rewrite <-Nat.sub_succ_l, Nat.sub_succ by easy. ring. }
  rewrite Zpos_P_of_succ_nat, Z.pow_succ_r by omega.
  rewrite zip_with_tail, Ssigma_tail_0, Ssigmas_S_tail, sigseq_0_head.
  rewrite (bins_sig_seq_SS (S n)), bins_diag, Splus_assoc, <-!IH by omega.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by omega.
  rewrite !Ssigma_plus, !(repeat_zip_with Z.mul), !repeat_2. ring.
Qed.

Lemma Rn_sig_seq_nat_seq n : Rn (sig_seq 0 2 n) (nat_seq n).
Proof.
  induction n as [|n IH]; simpl.
  { repeat constructor. rewrite <-(Smult_1_r nats). apply (Rn_sig2 0). }
  constructor; auto. apply (Rn_sig2 (S n)).
Qed.
Lemma Rn_bins_sig_seq_bins_seq n i : Rn (bins_sig_seq n 2 i) (bins_seq n i).
Proof.
  induction i as [|i IH]; simpl.
    { apply Rn_mult; repeat constructor.
      rewrite <-(Smult_1_r nats). apply (Rn_sig2 0). }
  constructor; auto. rewrite Smult_assoc. apply Rn_mult, (Rn_sig2 (S i)).
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
    * rewrite !zip_with_head; congruence.
    * now rewrite <-H, <-H0. }
  induction Hst.
  * rewrite nats_pow_tail, Ssigmas_S_tail. apply Rn_sig_seq_nat_seq.
  * rewrite Ssigmas_0_tail, nats_nats_pow_tail by easy.
    apply Rn_bins_sig_seq_bins_seq.
  * constructor.
  * now constructor.
  * now constructor.
  * now rewrite <-H, <-H0.
Qed.

Theorem Moessner n : Σ@{1,2,n} #1 ≡ nats ^^ S n.
Proof.
  eapply bisimulation_equal, Rn_sig1.
  apply bisimulation_Rn.
Qed.
Theorem Moessner_alt n : Σ@{1,2,n} nats ≡ nats ^^ S (S n).
Proof.
  rewrite <-Moessner, Ssigmas_S_alt.
  unfold Ssigma. now rewrite Sdrop_repeat, Ssum_1.
Qed.

Lemma Moessner_ext_help a d : Σ (a ::: #d) ≡ #d ⊙ nats ⊕ #(a - d).
Proof.
  constructor.
  { rewrite Ssum_head, !zip_with_head, !repeat_head, Sfrom_head.
    rewrite SCons_head. ring. }
  rewrite Ssum_tail, !zip_with_tail, !repeat_tail, Sfrom_tail.
  rewrite SCons_head, SCons_tail, Ssum_repeat, repeat_zip_with. ring.
Qed.

Corollary Moessner_ext a d n :
  Σ@{1,2,n} (a ::: #d) ≡ Σ (a ::: #d) ⊙ nats ^^ n.
Proof.
  destruct n as [|n]; rewrite ?Ssigmas_S_alt; simpl; unfold Ssigma.
  { rewrite <-(head_tail (D@{_,_} _)), Sdrop_head_S, Sdrop_tail_S.
    rewrite SCons_head, SCons_tail, Sdrop_repeat,
      !Moessner_ext_help, Spow_0. ring. }
  rewrite <-(head_tail (D@{_,_} _)), Sdrop_head_S, Sdrop_tail_S.
  rewrite SCons_head, SCons_tail, Sdrop_repeat, !Moessner_ext_help.
  rewrite <-(Smult_1_r (#(a - d))) at 1.
  rewrite !Ssigmas_plus, !Ssigmas_mult, Moessner, Moessner_alt.
  rewrite !Spow_S. ring.
Qed.
