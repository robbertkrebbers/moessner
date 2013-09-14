(* Copyright (c) 2013, Louis Parlant and Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import prelude.

Inductive R2 : relation (Stream Z) :=
  | R2_base12 : R2 (Σ@{1,2} #1) nats
  | R2_base02 : R2 (Σ@{0,2} #1) nats
  | R2_base2132 : R2 (Σ@{1,2} Σ@{2,3} #1) (nats ^^ 2)
  | R2_base2031 : R2 (Σ@{0,2} Σ@{1,3} #1) (nats ⊙ (#1 ⊕ nats))
  | R2_refl s : R2 s s
  | R2_plus s1 s2 t1 t2 : R2 s1 t1 → R2 s2 t2 → R2 (s1 ⊕ s2) (t1 ⊕ t2)
  | R2_eq s1 s2 t1 t2 : s1 ≡ s2 → t1 ≡ t2 → R2 s1 t1 → R2 s2 t2.

Instance: Proper (equal ==> equal ==> iff) R2.
Proof. now split; apply R2_eq. Qed.

Lemma nats_pow_tail : (nats ^^ 2)` ≡ #1 ⊕ nats ⊕ nats ⊙ (#1 ⊕ nats).
Proof. rewrite Spow_tail, Sfrom_tail, Spow_S, Spow_1; ring. Qed.
Lemma nats_nats_pow_tail :
  (nats ⊙ (#1 ⊕ nats))` ≡ #1 ⊕ #1  ⊕ nats ⊕ nats ⊕ (nats ⊙ (#1 ⊕ nats)).
Proof. rewrite !zip_with_tail, Sfrom_tail, repeat_tail; ring. Qed.
Lemma Ssigma2132_tail :
  (Σ@{1,2} Σ@{2,3} #1)` ≡ #1 ⊕ Σ@{0,2} #1 ⊕ Σ@{0,2} Σ@{1,3} #1.
Proof.
  rewrite !Ssigma_tail_S, Ssigma_head_S, Ssigma_plus,
    repeat_tail, repeat_head. ring.
Qed.
Lemma Ssigma2031_tail :
  (Σ@{0,2} Σ@{1,3}#1)` ≡ #1 ⊕ #1 ⊕ Σ@{0,2} #1 ⊕ Σ@{0,2} #1 ⊕ Σ@{0,2} Σ@{1,3} #1.
Proof.
  rewrite Ssigma_tail_0, Ssigma_tail_S, zip_with_tail, zip_with_head; simpl.
  rewrite !repeat_head, repeat_tail, Ssigma_tail_0.
  rewrite !repeat_tail, repeat_head, !Ssigma_plus, repeat_2; simpl. ring.
Qed.

Lemma bisimulation_R2 : bisimulation R2.
Proof.
  intros s t Hst. split.
  { induction Hst.
    * now rewrite Ssigma_head_S.
    * now rewrite Ssigma_head_0.
    * now rewrite !Ssigma_head_S.
    * now rewrite Ssigma_head_0, Ssigma_tail_S, zip_with_head, Ssigma_head_0.
    * easy.
    * rewrite !zip_with_head; congruence.
    * now rewrite <-H, <-H0. }
  induction Hst.
  * rewrite Ssigma_tail_S, Sfrom_tail. repeat constructor.
  * rewrite Ssigma_tail_0, Sfrom_tail. repeat constructor.
  * rewrite Ssigma2132_tail, nats_pow_tail. repeat constructor.
  * rewrite Ssigma2031_tail, nats_nats_pow_tail. repeat constructor.
  * constructor.
  * simpl. now repeat constructor.
  * now rewrite <-H, <-H0.
Qed.
Theorem Moessner_case2 : Σ@{1,2} Σ@{2,3} #1 ≡ nats ^^ 2.
Proof. apply (bisimulation_equal _ _ _ bisimulation_R2). constructor. Qed.
