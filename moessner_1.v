(* Copyright (c) 2013, Louis Parlant and Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import prelude.

Inductive R1 : relation (Stream nat) :=
  | R1_base12 : R1 (Σ@{1,2} (#1)) nats
  | R1_base02 : R1 (Σ@{0,2} (#1)) nats
  | R1_refl s : R1 s s
  | R1_plus s1 s2 t1 t2 : R1 s1 t1 → R1 s2 t2 → R1 (s1 ⊕ s2) (t1 ⊕ t2)
  | R1_eq s1 s2 t1 t2 : s1 ≡ s2 → t1 ≡ t2 → R1 s1 t1 → R1 s2 t2.

Instance: Proper (equal ==> equal ==> iff) R1.
Proof. now split; apply R1_eq. Qed.

Lemma bisimulation_R1 : bisimulation R1.
Proof.
  intros s t Hst; split.
  { induction Hst.
    * now rewrite Ssigma_head_S.
    * now rewrite Ssigma_head_0.
    * easy.
    * rewrite !zip_with_head; congruence.
    * now rewrite <-H, <-H0. }
  induction Hst.
  * rewrite Ssigma_tail_S, Snats_tail. repeat constructor.
  * rewrite Ssigma_tail_0, Snats_tail. repeat constructor.
  * constructor.
  * now constructor.
  * now rewrite <-H, <-H0.
Qed.
Theorem Moessner_case1 : Σ@{1,2} #1 ≡ nats ^^ 1.
Proof.
  apply (bisimulation_equal _ _ _ bisimulation_R1). rewrite Spow_1. constructor.
Qed.
