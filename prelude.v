(* Copyright (c) 2013, Louis Parlant and Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export Utf8.
Require Export Arith Omega Setoid Morphisms List NPeano ZArith BinInt.

Open Scope Z_scope.
Coercion Z.of_nat : nat >-> Z.
Arguments Z.pow _ _ : simpl never.
Arguments Z.add _ _ : simpl never.
Arguments Z.mul _ _ : simpl never.

CoInductive Stream (A : Type) : Type := SCons : A → Stream A → Stream A.
Arguments SCons {_} _ _.
Infix ":::" := SCons (at level 60, right associativity).

Definition head {A} (s : Stream A) : A := match s with x ::: _ => x end.
Definition tail {A} (s : Stream A) : Stream A := match s with _ ::: s => s end.
Notation "s `" := (tail s) (at level 10, format "s `").
Arguments head _ _ : simpl never.
Arguments tail _ _ : simpl never.

Reserved Infix "!!" (at level 20).
Fixpoint elt {A} (s : Stream A) (i : nat) : A :=
  match i with O => head s | S i => s` !! i end
where "s !! i" := (elt s i).

Reserved Infix "≡" (at level 70).
CoInductive equal {A} (s t : Stream A) : Prop :=
  make_equal : head s = head t →  s` ≡ t` → s ≡ t
where "s ≡ t" := (@equal _ s t).

Reserved Notation "# x" (at level 15).
CoFixpoint repeat {A} (x : A) : Stream A := x ::: # x
where "# x" := (repeat x).
Reserved Notation "D@{ i , k } s"
  (at level 20, i at level 2, k at level 1, right associativity,
   format "D@{ i , k }  s").
CoFixpoint Sdrop {A} (i k : nat) (s : Stream A) : Stream A :=
  match i with 
  | O => head (s`) ::: D@{k-2,k} s``
  | S i => head s ::: D@{i,k} s`
  end
where "D@{ i , k } s" := (Sdrop i k s).

Section Stream_theorems.
  Context {A:Type}.
  Implicit Types x y : A.
  Implicit Types s t : Stream A.

  Definition SCons_head x s : head (x ::: s) = x := eq_refl.
  Definition SCons_tail x s : (x ::: s)` = s := eq_refl.
  Definition repeat_head x : head (#x) = x := eq_refl.
  Definition repeat_tail x : (#x)` = #x := eq_refl.
  Definition Sdrop_head_0 k s : head (D@{0,k} s) = head (s`) := eq_refl.
  Definition Sdrop_head_S i k s : head (D@{S i,k} s) = head s := eq_refl.
  Definition Sdrop_tail_0 k s : (D@{0,k} s)` = D@{k-2,k} s`` := eq_refl.
  Definition Sdrop_tail_S i k (s : Stream A) :
    (D@{S i,k} s)` = D@{i,k} s` := eq_refl.

  Lemma head_tail s : head s ::: tail s = s.
  Proof. now destruct s. Qed.

  Global Instance equal_equivalence : Equivalence (@equal A).
  Proof.
    split.
    * now cofix; intros [??]; constructor.
    * now cofix; intros ?? [??]; constructor.
    * cofix; intros ??? [??] [??]; constructor; etransitivity; eauto.
  Qed.

  Global Instance SCons_proper x : Proper (equal ==> equal) (SCons x).
  Proof. now constructor. Qed.
  Global Instance head_proper : Proper (equal ==> eq) (@head A).
  Proof. now intros ?? [??]. Qed.
  Global Instance tail_proper : Proper (equal ==> equal) (@tail A).
  Proof. now intros ?? [??]. Qed.
  Global Instance elt_proper : Proper (equal ==> eq ==> eq) (@elt A).
  Proof.
    intros s t Hst i ? <-. revert s t Hst.
    induction i as [|i IH]; intros; simpl. apply Hst. apply IH, Hst.
  Qed.
  Global Instance Sdrop_proper i k : Proper (equal ==> equal) (@Sdrop A i k).
  Proof.
    intros s t Hst; revert s t Hst i k.
    cofix CH; intros s t [Hhd Htl] [|i] ?; constructor; simpl.
    * now rewrite Sdrop_head_0, Htl.
    * apply CH. now rewrite Htl.
    * easy.
    * now apply CH.
  Qed.

  Lemma equal_elt s t : s ≡ t ↔ ∀ i, s !! i = t !! i.
  Proof.
    split; [now intros Hst i; rewrite Hst|].
    revert s t. cofix; intros s t Hst; constructor.
    * apply (Hst 0%nat).
    * apply equal_elt, (λ i, Hst (S i)).
  Qed.

  Definition bisimulation (R : relation (Stream A)) : Prop :=
    ∀ s t, R s t → head s = head t ∧ R (s`) (t`).

  Lemma equal_bisimulation : bisimulation (@equal A).
  Proof. intros s t Hst. now rewrite Hst. Qed.
  Lemma bisimulation_equal R s t : bisimulation R → R s t → s ≡ t.
  Proof.
    intros Hbi. revert s t; cofix CH; constructor.
    * now apply Hbi.
    * now apply CH, Hbi.
  Qed.
  Lemma bisimulation_principle s t : s ≡ t ↔ ∃ R, bisimulation R ∧ R s t.
  Proof.
    split.
    * exists equal; auto using equal_bisimulation.
    * intros (?&?&?); eauto using bisimulation_equal.
  Qed.

  Lemma repeat_elt x i : #x !! i = x.
  Proof. induction i; simpl; auto. Qed.
  Lemma Sdrop_repeat i k x : D@{i,k} #x ≡ #x.
  Proof.
    revert i k.
    cofix CH; intros [|i] k; constructor; first [easy|apply CH].
  Qed.
End Stream_theorems.

CoFixpoint map {A B} (f : A → B) (s : Stream A) : Stream B :=
  f (head s) ::: map f (s`).

Section map.
  Context {A B} (f : A → B).

  Definition map_head s : head (map f s) = f (head s) := eq_refl.
  Definition map_tail s : (map f s)` = map f (s`) := eq_refl.

  Lemma map_elt s i : map f s !! i = f (s !! i).
  Proof.
    revert s. induction i; intros; simpl;
      rewrite ?map_head, ?map_tail; auto.
  Qed.
  Global Instance: Proper (equal ==> equal) (map f).
  Proof.
    intros s1 s2 Hs; apply equal_elt; intros. now rewrite !map_elt, Hs.
  Qed.
  Lemma repeat_map x : #f x ≡ map f (#x).
  Proof. apply equal_elt; intros i. now rewrite map_elt, !repeat_elt. Qed.
  Lemma Sdrop_map s k i : D@{i,k} (map f s) ≡ map f (D@{i,k} s).
  Proof.
    revert s k i. cofix; intros s k [|i]; constructor.
    * easy.
    * now rewrite Sdrop_tail_0, !map_tail, !Sdrop_tail_0.
    * easy.
    * now rewrite Sdrop_tail_S, !map_tail, !Sdrop_tail_S.
  Qed.
End map.

CoFixpoint zip_with {A B C} (f : A → B → C) (s : Stream A)
  (t : Stream B) : Stream C := f (head s) (head t) ::: zip_with f (s`) (t`).

Section zip_with.
  Context {A B C} (f : A → B → C).

  Definition zip_with_head s t :
    head (zip_with f s t) = f (head s) (head t) := eq_refl.
  Definition zip_with_tail s t :
    (zip_with f s t)` = zip_with f (s`) (t`) := eq_refl.

  Lemma zip_with_elt s t i : zip_with f s t !! i = f (s !! i) (t !! i).
  Proof.
    revert s t. induction i; intros; simpl;
      rewrite ?zip_with_head, ?zip_with_tail; auto.
  Qed.
  Global Instance: Proper (equal ==> equal ==> equal) (zip_with f).
  Proof.
    intros s1 s2 Hs t1 t2 Ht; apply equal_elt; intros.
    now rewrite !zip_with_elt, Hs, Ht.
  Qed.
  Lemma repeat_zip_with x y : #f x y ≡ zip_with f (#x) (#y).
  Proof. apply equal_elt; intros i. now rewrite zip_with_elt, !repeat_elt. Qed.
  Lemma Sdrop_zip_with s t k i :
    D@{i,k} (zip_with f s t) ≡ zip_with f (D@{i,k} s) (D@{i,k} t).
  Proof.
    revert s t k i. cofix; intros s t k [|i]; constructor.
    * easy.
    * now rewrite Sdrop_tail_0, !zip_with_tail, !Sdrop_tail_0.
    * easy.
    * now rewrite Sdrop_tail_S, !zip_with_tail, !Sdrop_tail_S.
  Qed.
End zip_with.

(** Operations on streams of naturals *)
Infix "⊕" := (zip_with Z.add) (at level 50, left associativity).
Infix "⊖":= (zip_with Z.sub) (at level 50, left associativity).
Infix "⊙" := (zip_with Z.mul) (at level 40, left associativity).
Notation "⊖ s":= (map Z.opp s) (at level 20).

Reserved Notation "s ^^ n" (at level 30, right associativity).
Fixpoint Spow (s : Stream Z) (n : nat) : Stream Z :=
  match n with O => #1 | S n => s ⊙ s ^^ n end
where "s ^^ n" := (Spow s n).

CoFixpoint Sfrom (i : Z) : Stream Z := i ::: Sfrom (1 + i).
Notation nats := (Sfrom 1).

CoFixpoint Ssum (i : Z) (s : Stream Z) : Stream Z :=
  head s + i ::: Ssum (head s + i) (s`).
Notation "'Σ' s" := (Ssum 0 s) (at level 20, format "Σ  s").
Definition Ssigma (i k : nat) (s : Stream Z) : Stream Z := Σ D@{i,k} s.
Notation "Σ@{ i , k } s" := (Ssigma i k s)
  (at level 20, i at level 1, k at level 1, right associativity,
   format "Σ@{ i , k }  s").

Definition Sfrom_head i : head (Sfrom i) = i := eq_refl.
Definition Sfrom_tail_ i : (Sfrom i)` = Sfrom (1 + i) := eq_refl.
Lemma Sfrom_elt n i : Sfrom n !! i = n + i.
Proof.
  revert n. induction i as [|i IH]; intros n; simpl.
  { rewrite Sfrom_head. ring. }
  rewrite Zpos_P_of_succ_nat, <-Z.add_1_l, Sfrom_tail_, IH. ring.
Qed.
Lemma Sfrom_plus n m : Sfrom (n + m) ≡ #n ⊕ Sfrom m.
Proof.
  apply equal_elt; intros i.
  rewrite zip_with_elt, !Sfrom_elt, !repeat_elt. ring.
Qed.
Lemma Sfrom_tail n : (Sfrom n)` ≡ #1 ⊕ Sfrom n.
Proof. now rewrite Sfrom_tail_, Sfrom_plus. Qed.

Lemma stream_ring_theory :
  ring_theory (#0) (#1) (zip_with Z.add) (zip_with Z.mul)
    (zip_with Z.sub) (map Z.opp) equal.
Proof.
  split; intros; apply equal_elt; intros;
    rewrite ?zip_with_elt, ?map_elt, ?repeat_elt; ring.
Qed.
Add Ring stream : stream_ring_theory.

Lemma Splus_0_l s : #0 ⊕ s ≡ s. Proof. ring. Qed.
Lemma Splus_0_r s : s ⊕ #0 ≡ s. Proof. ring. Qed.
Lemma Smult_0_l s : #0 ⊙ s ≡ #0. Proof. ring. Qed.
Lemma Smult_0_r s : s ⊙ #0 ≡ #0. Proof. ring. Qed.
Lemma Smult_1_l s : #1 ⊙ s ≡ s. Proof. ring. Qed.
Lemma Smult_1_r s : s ⊙ #1 ≡ s. Proof. ring. Qed.
Lemma Splus_assoc s t u : s ⊕ t ⊕ u ≡ s ⊕ (t ⊕ u). Proof. ring. Qed.
Lemma Smult_assoc s t u : s ⊙ t ⊙ u ≡ s ⊙ (t ⊙ u). Proof. ring. Qed.
Lemma Splus_comm s t : s ⊕ t ≡ t ⊕ s. Proof. ring. Qed.
Lemma Smult_comm s t : s ⊙ t ≡ t ⊙ s. Proof. ring. Qed.
Lemma Smult_plus_distr_l s t u : s ⊙ (t ⊕ u) ≡ (s ⊙ t) ⊕ (s ⊙ u).
Proof. ring. Qed.
Lemma Smult_plus_distr_r s t u : (t ⊕ u) ⊙ s ≡ (t ⊙ s) ⊕ (u ⊙ s).
Proof. ring. Qed.
Lemma repeat_2 : #2 ≡ #1 ⊕ #1.
Proof. now rewrite <-repeat_zip_with. Qed.

Lemma Spow_head s n : head (s ^^ n) = head s ^ n.
Proof.
  induction n as [|n IH]; simpl; [easy|].
  rewrite Zpos_P_of_succ_nat, Z.pow_succ_r by omega.
  now rewrite zip_with_head, IH.
Qed.
Lemma Spow_tail s n : (s ^^ n)` = s` ^^ n.
Proof.
  induction n as [|n IH]; simpl; [easy|]. now rewrite zip_with_tail, IH.
Qed.
Lemma Spow_elt s n i : (s ^^ n) !! i = (s !! i) ^ n.
Proof.
  induction n as [|n IH]; simpl; [now rewrite repeat_elt |].
  rewrite Zpos_P_of_succ_nat, Z.pow_succ_r by omega.
  now rewrite zip_with_elt, IH.
Qed.
Instance: Proper (equal ==> eq ==> equal) Spow.
Proof.
  intros s t Hst n ? <-. now apply equal_elt; intro; rewrite !Spow_elt, Hst.
Qed.

Arguments Spow _ _ : simpl never.
Definition Spow_0 s : s ^^ 0 = #1 := eq_refl.
Definition Spow_S s n : s ^^ S n = s ⊙ s ^^ n := eq_refl.
Lemma Spow_1 s : s ^^ 1 ≡ s.
Proof. rewrite !Spow_S, Spow_0; ring. Qed.

Definition Ssum_head_ b s : head (Ssum b s) = head s + b := eq_refl.
Definition Ssum_tail_ b s : (Ssum b s)` = Ssum (head s + b) (s`) := eq_refl.
Instance Ssum_aux_proper b : Proper (equal ==> equal) (Ssum b).
Proof.
  revert b. cofix; intros ??? [Hhd Htl]; constructor; simpl.
  { now rewrite !Ssum_head_, Hhd. }
  rewrite !Ssum_tail_, Hhd. now apply (Ssum_aux_proper (_ + _)).
Qed.
Lemma Ssum_move b s : Ssum b s ≡ #b ⊕ Σ s.
Proof.
  apply equal_elt. intros i. rewrite zip_with_elt, repeat_elt.
  revert b s. induction i as [|i IH]; intros b s; simpl.
  { rewrite !Ssum_head_. ring. }
  rewrite !Ssum_tail_, (IH (_ + b)), (IH (_ + 0)). ring.
Qed.
Lemma Ssum_head s : head (Σ s) = head s.
Proof. now rewrite Ssum_head_, Z.add_0_r. Qed.
Lemma Ssum_tail s : (Σ s)` ≡ #head s ⊕ Σ s`.
Proof. now rewrite Ssum_tail_, Ssum_move, Z.add_0_r. Qed.
Lemma Ssum_plus s t : Σ (s ⊕ t) ≡ Σ s ⊕ Σ t.
Proof.
  apply equal_elt. intros i. rewrite zip_with_elt.
  revert s t. induction i as [|i IH]; intros s t; simpl.
  { now rewrite !Ssum_head, zip_with_head. }
  rewrite !Ssum_tail, zip_with_tail, !zip_with_elt, IH.
  rewrite !repeat_elt, zip_with_head. ring.
Qed.
Lemma Ssum_0 : Σ #0 ≡ #0.
Proof. cofix. now constructor. Qed.
Lemma Ssum_mult n s : Σ (#n ⊙ s) ≡ #n ⊙ Σ s.
Proof.
  apply equal_elt. intros i. rewrite zip_with_elt.
  revert s. induction i as [|i IH]; intros s; simpl.
  { now rewrite !Ssum_head, zip_with_head. }
  rewrite !Ssum_tail, zip_with_tail, repeat_tail, !zip_with_elt, IH.
  rewrite !zip_with_head, repeat_head, !repeat_elt. ring.
Qed.
Lemma Ssum_1 : Σ #1 ≡ nats.
Proof.
  apply equal_elt. intros i. rewrite Sfrom_elt. simpl.
  induction i as [|i IH]; simpl; [easy|].
  now rewrite Zpos_P_of_succ_nat, <-Z.add_1_l, Ssum_tail,
    repeat_tail, repeat_head, zip_with_elt, IH, repeat_elt.
Qed.
Lemma Ssum_repeat n : Σ #n ≡ #n ⊙ nats.
Proof. rewrite <-(Smult_1_r (#n)), Ssum_mult, Ssum_1. ring. Qed.

Instance Ssigma_proper i k : Proper (equal ==> equal) (Ssigma i k).
Proof. unfold Ssigma. solve_proper. Qed.
Lemma Ssigma_head_0 s k : head (Σ@{0,k} s) = head (s`).
Proof. unfold Ssigma. rewrite Ssum_head, Sdrop_head_0. ring. Qed.
Lemma Ssigma_head_S s i k : head (Σ@{S i,k} s) = head s.
Proof. unfold Ssigma; rewrite Ssum_head, Sdrop_head_S. ring. Qed.
Lemma Ssigma_tail_0 s k : (Σ@{0,k} s)` ≡ #head (s`) ⊕ Σ@{k-2,k} s``.
Proof. unfold Ssigma. rewrite Ssum_tail, Sdrop_tail_0, Sdrop_head_0. ring. Qed.
Lemma Ssigma_tail_S s i k : (Σ@{S i,k} s)` ≡ #head s ⊕ Σ@{i,k} s`.
Proof. unfold Ssigma. rewrite Ssum_tail, Sdrop_tail_S, Sdrop_head_S. ring. Qed.
Lemma Ssigma_plus s t i k : Σ@{i,k} (s ⊕ t) ≡ Σ@{i,k} s ⊕ Σ@{i,k} t.
Proof. unfold Ssigma. now rewrite Sdrop_zip_with, Ssum_plus. Qed.
Lemma Ssigma_0 i k : Σ@{i,k} #0 ≡ #0.
Proof. unfold Ssigma. now rewrite Sdrop_repeat, Ssum_0. Qed.
Lemma Ssigma_mult n s i k : Σ@{i,k} (#n ⊙ s) ≡ #n ⊙ Σ@{i,k} s.
Proof. unfold Ssigma. now rewrite Sdrop_zip_with, Sdrop_repeat, Ssum_mult. Qed.
Lemma Ssigma_1 i k : Σ@{i,k} #1 ≡ nats.
Proof. unfold Ssigma. now rewrite Sdrop_repeat, Ssum_1. Qed.
Lemma Ssigma_repeat i k n : Σ@{i,k} #n ≡ #n ⊙ nats.
Proof. unfold Ssigma. now rewrite Sdrop_repeat, Ssum_repeat. Qed.
