(* Copyright (c) 2012-2013, Louis Parlant and Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export Utf8.
Require Export Arith Omega Setoid Morphisms List NPeano.

Arguments pow _ _ : simpl never.

CoInductive Stream (A : Type) : Type :=
  SCons : A → Stream A → Stream A.
Arguments SCons {_} _ _.
Infix ":::" := SCons (at level 60, right associativity).

Definition head {A} (s : Stream A) : A :=
  match s with x ::: _ => x end.
Definition tail {A} (s : Stream A) : Stream A :=
  match s with _ ::: t => t end.
Notation "s `" := (tail s) (at level 10, format "s `").
Arguments head _ _ : simpl never.
Arguments tail _ _ : simpl never.

Reserved Infix "!!" (at level 20).
Fixpoint elt {A} (i : nat) (s : Stream A) : A :=
  match i with 0 => head s | S i => s` !! i end
where "s !! i" := (elt i s).

Reserved Infix "≡" (at level 70).
CoInductive equal {A:Type} (s t : Stream A) : Prop :=
  make_equal : head s = head t →  s` ≡ t` → s ≡ t
where "s ≡ t" := (@equal _ s t).

CoFixpoint Sall {A} (x : A) : Stream A := x ::: Sall x.
Notation "# x" := (Sall x) (at level 15).

Section Stream_theorems.
  Context {A:Type}.
  Implicit Types x y : A.
  Implicit Types s t : Stream A.

  Global Instance equal_equivalence : Equivalence (@equal A).
  Proof.
    split.
    * now cofix; intros [??]; constructor.
    * now cofix; intros ?? [??]; constructor.
    * cofix; intros ??? [??] [??]; constructor; etransitivity; eauto.
  Qed.

  Global Instance SCons_proper : Proper (eq ==> equal ==> equal) (@SCons A).
  Proof. now constructor. Qed.
  Global Instance head_proper : Proper (equal ==> eq) (@head A).
  Proof. now intros ?? [??]. Qed.
  Global Instance tail_proper : Proper (equal ==> equal) (@tail A).
  Proof. now intros ?? [??]. Qed.
  Global Instance elt_proper n : Proper (equal ==> eq) (@elt A n).
  Proof. induction n; intros ?? [??]; simpl; auto. Qed.

  Lemma equal_elt s t : s ≡ t ↔ ∀ i, s !! i = t !! i.
  Proof.
    split; [now intros Hst i; rewrite Hst|].
    revert s t. cofix; intros s t Hst; constructor.
    * apply (Hst 0).
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

  Definition Sall_head x : head (#x) = x := eq_refl.
  Definition Sall_tail x : (#x)` = #x := eq_refl.
  Lemma Sall_elt x i : #x !! i = x.
  Proof. induction i; simpl; auto. Qed.
End Stream_theorems.

CoFixpoint zip_with {A B C} (f : A → B → C) (s : Stream A)
  (t : Stream B) : Stream C := f (head s) (head t) ::: zip_with f (s`) (t`).

Section zip_with.
  Context {A B C} (f : A → B → C).

  Lemma zip_with_head s t : head (zip_with f s t) = f (head s) (head t).
  Proof. reflexivity. Qed.
  Lemma zip_with_tail s t : (zip_with f s t)` = zip_with f (s`) (t`).
  Proof. reflexivity. Qed.

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
  Lemma Sall_zip_with x y : #f x y ≡ zip_with f (#x) (#y).
  Proof. apply equal_elt; intros i. now rewrite zip_with_elt, !Sall_elt. Qed.
End zip_with.

(** Operations on streams of naturals *)
Infix "⊕" := (zip_with plus) (at level 50, left associativity).
Infix "⊙" := (zip_with mult) (at level 40, left associativity).

CoFixpoint Sfrom (n : nat) : Stream nat := n ::: Sfrom (S n).
Notation nats := (Sfrom 1).
Fixpoint Spow (s : Stream nat) (n : nat) : Stream nat :=
  match n with 0 => #1 | S n => s ⊙ Spow s n end.
Notation "s ^^ n" := (Spow s n) (at level 30, right associativity).
CoFixpoint Ssum (b : nat) (s : Stream nat) : Stream nat :=
  head s + b ::: Ssum (head s + b) (s`).
Notation "'Σ' s" := (Ssum 0 s) (at level 20, format "Σ  s").
Reserved Notation "D@{ i , k } s"
  (at level 20, i at level 2, k at level 1, right associativity,
   format "D@{ i , k }  s").
CoFixpoint Sdrop (i k : nat) (s : Stream nat) : Stream nat :=
  match i with 
  | 0 => head (s`) ::: D@{k-2,k} (s``)
  | S i => head s ::: D@{i,k} (s`)
  end
where "D@{ i , k } s" := (Sdrop i k s).
Definition Ssigma (i k : nat) (s : Stream nat) : Stream nat := Σ (D@{i,k} s).
Notation "Σ@{ i , k } s" := (Ssigma i k s)
  (at level 20, i at level 1, k at level 1, right associativity,
   format "Σ@{ i , k }  s").

Definition Sfrom_head n : head (Sfrom n) = n := eq_refl.
Definition Sfrom_tail n : (Sfrom n)` = Sfrom (S n) := eq_refl.
Lemma Sfrom_elt n i : Sfrom n !! i = n + i.
Proof.
  revert n. induction i as [|i IH]; intros n; simpl.
  { rewrite Sfrom_head. ring. }
  rewrite Sfrom_tail, IH. ring.
Qed.
Lemma Sfrom_plus n m : Sfrom (n + m) ≡ #n ⊕ Sfrom m.
Proof.
  apply equal_elt; intros i.
  rewrite zip_with_elt, !Sfrom_elt, !Sall_elt. ring.
Qed.
Lemma Sfrom_S n : Sfrom (S n) ≡ #1 ⊕ Sfrom n.
Proof. apply (Sfrom_plus 1). Qed.
Lemma Sall_S n : #S n ≡ #1 ⊕ Sall n.
Proof. apply (Sall_zip_with plus 1). Qed.

Lemma stream_semi_ring_theory :
  semi_ring_theory (#0) (#1) (zip_with plus) (zip_with mult) equal.
Proof.
  split; intros; apply equal_elt; intros;
    rewrite ?zip_with_elt, ?Sall_elt; ring.
Qed.
Add Ring stream : stream_semi_ring_theory.
Lemma Splus_0_l s : #0 ⊕ s ≡ s.
Proof. ring. Qed.
Lemma Splus_0_r s : s ⊕ #0 ≡ s.
Proof. ring. Qed.
Lemma Smult_0_l s : #0 ⊙ s ≡ #0.
Proof. ring. Qed.
Lemma Smult_0_r s : s ⊙ #0 ≡ #0.
Proof. ring. Qed.
Lemma Smult_1_l s : #1 ⊙ s ≡ s.
Proof. ring. Qed.
Lemma Smult_1_r s : s ⊙ #1 ≡ s.
Proof. ring. Qed.
Lemma Splus_assoc s t u : s ⊕ t ⊕ u ≡ s ⊕ (t ⊕ u).
Proof. ring. Qed.
Lemma Smult_assoc s t u : s ⊙ t ⊙ u ≡ s ⊙ (t ⊙ u).
Proof. ring. Qed.
Lemma Splus_comm s t : s ⊕ t ≡ t ⊕ s.
Proof. ring. Qed.
Lemma Smult_comm s t : s ⊙ t ≡ t ⊙ s.
Proof. ring. Qed.
Lemma Smult_plus_distr_l s t u : s ⊙ (t ⊕ u) ≡ (s ⊙ t) ⊕ (s ⊙ u).
Proof. ring. Qed.
Lemma Smult_plus_distr_r s t u : (t ⊕ u) ⊙ s ≡ (t ⊙ s) ⊕ (u ⊙ s).
Proof. ring. Qed.
Lemma Snats_tail : nats` ≡ nats ⊕ #1.
Proof. rewrite Sfrom_tail, Sfrom_S. ring. Qed.

Lemma Spow_head s n : head (s ^^ n) = head s ^ n.
Proof.
  induction n as [|n IH]; simpl. easy. now rewrite zip_with_head, IH.
Qed.
Lemma Spow_tail s n : (s ^^ n)` = s` ^^ n.
Proof.
  induction n as [|n IH]; simpl. easy. now rewrite zip_with_tail, IH.
Qed.
Lemma Spow_elt s n i : (s ^^ n) !! i = (s !! i) ^ n.
Proof.
  induction n as [|n IH]; simpl; [now rewrite Sall_elt |].
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

Definition Ssum_head b s : head (Ssum b s) = head s + b := eq_refl.
Definition Ssum_tail b s : (Ssum b s)` = Ssum (head s + b) (s`) := eq_refl.
Instance Ssum_aux_proper b : Proper (equal ==> equal) (Ssum b).
Proof.
  revert b. cofix; intros ??? [Hhd Htl]; constructor; simpl.
  { now rewrite !Ssum_head, Hhd. }
  rewrite !Ssum_tail, Hhd. now apply (Ssum_aux_proper (_ + _)).
Qed.
Lemma Ssum_move b s : Ssum b s ≡ #b ⊕ Σ s.
Proof.
  apply equal_elt. intros i. rewrite zip_with_elt, Sall_elt.
  revert b s. induction i as [|i IH]; intros b s; simpl.
  { rewrite !Ssum_head. ring. }
  rewrite !Ssum_tail, (IH (_ + b)), (IH (_ + 0)). ring.
Qed.
Lemma Ssum_aux_one b s : Ssum b s ⊕ #1 ≡ Ssum (S b) s.
Proof. rewrite (Ssum_move b), (Ssum_move (S b)), (Sall_S b). ring. Qed.
Lemma Splus_sum_aux s t a b :
  Ssum a s ⊕ Ssum b t ≡ Ssum (a + b) (s ⊕ t).
Proof.
  apply equal_elt. intros i. rewrite zip_with_elt.
  revert a b s t. induction i as [|i IH]; intros a b s t; simpl.
  { rewrite !Ssum_head, zip_with_head. ring. }
  rewrite !Ssum_tail, zip_with_head, zip_with_tail, IH.
  do 2 f_equal; ring.
Qed.
Lemma Ssum_plus s t : Σ (s ⊕ t) ≡ Σ s ⊕ Σ t.
Proof. now rewrite Splus_sum_aux. Qed.
Lemma Ssum_0 : Σ #0 ≡ #0.
Proof. cofix. now constructor. Qed.
Lemma Ssum_mult n s : Σ (#n ⊙ s) ≡ #n ⊙ Σ s.
Proof.
  induction n as [|n IH].
  { now rewrite !Smult_0_l, Ssum_0. }
  now rewrite Sall_S, !Smult_plus_distr_r, !Smult_1_l, Ssum_plus, IH.
Qed.

Definition Sdrop_head_0 s k : head (D@{0,k} s) = head (s`) := eq_refl.
Definition Sdrop_head_S s i k : head (D@{S i,k} s) = head s := eq_refl.
Definition Sdrop_tail_0 s k : (D@{0,k} s)` = D@{k-2,k} (s``) := eq_refl.
Definition Sdrop_tail_S s i k : (D@{S i,k} s)` = D@{i,k} (s`) := eq_refl.

Instance Sdrop_proper : Proper (eq ==> eq ==> equal ==> equal) Sdrop.
Proof.
  intros i ? <- k ? <- s t Hst; revert s t Hst i k.
  cofix; intros s t [Hhd Htl] [|i] ?; constructor; simpl.
  * now rewrite Sdrop_head_0, Htl.
  * apply Sdrop_proper. now rewrite Htl.
  * easy.
  * now apply Sdrop_proper.
Qed.
Lemma Sdrop_plus s t k i : D@{i,k} (s ⊕ t) ≡ D@{i,k} s ⊕ D@{i,k} t.
Proof.
  revert s t k i. cofix; intros s t k [|i]; constructor.
  * easy.
  * now rewrite Sdrop_tail_0, !zip_with_tail, !Sdrop_tail_0.
  * easy.
  * now rewrite Sdrop_tail_S, !zip_with_tail, !Sdrop_tail_S.
Qed.
Lemma Sdrop_all i k n : D@{i,k} #n ≡ #n.
Proof.
  revert i k. cofix; intros [|i] k;
    constructor; first [easy | apply Sdrop_all].
Qed.
Lemma Sdrop_mult n s i k : D@{i,k} (#n ⊙ s) ≡ #n ⊙ D@{i,k} s.
Proof.
  induction n as [|n IH].
  { now rewrite !Smult_0_l, Sdrop_all. }
  now rewrite Sall_S, !Smult_plus_distr_r, !Smult_1_l, Sdrop_plus, IH.
Qed.

Instance Ssigma_proper : Proper (eq ==> eq ==> equal ==> equal) Ssigma.
Proof. unfold Ssigma. solve_proper. Qed.
Lemma Ssigma_head_0 s k : head (Σ@{0,k} s) = head (s`).
Proof. unfold Ssigma. rewrite Ssum_head, Sdrop_head_0. ring. Qed.
Lemma Ssigma_head_S s i k : head (Σ@{S i,k} s) = head s.
Proof. unfold Ssigma; rewrite Ssum_head, Sdrop_head_S. ring. Qed.
Lemma Ssigma_tail_0 s k :
  (Σ@{0,k} s)` ≡ Σ@{k-2,k} (s``) ⊕ Sall (head (s`)).
Proof.
  unfold Ssigma. rewrite Ssum_tail, Sdrop_tail_0, Sdrop_head_0,
    Ssum_move, Sall_zip_with. ring.
Qed.
Lemma Ssigma_tail_S s i k :
  (Σ@{S i,k} s)` ≡ Σ@{i,k} (s`) ⊕ Sall (head s).
Proof.
  unfold Ssigma. rewrite Ssum_tail, Sdrop_tail_S, Sdrop_head_S,
    Ssum_move, Sall_zip_with. ring.
Qed.
Lemma Ssigma_plus s t i k : Σ@{i,k} (s ⊕ t) ≡ Σ@{i,k} s ⊕ Σ@{i,k} t.
Proof. unfold Ssigma. now rewrite Sdrop_plus, Ssum_plus. Qed.
Lemma Ssigma_0 i k : Σ@{i,k} #0 ≡ #0.
Proof. unfold Ssigma. now rewrite Sdrop_all, Ssum_0. Qed.
Lemma Ssigma_mult n s i k : Σ@{i,k} (#n ⊙ s) ≡ #n ⊙ Σ@{i,k} s.
Proof. unfold Ssigma. now rewrite Sdrop_mult, Ssum_mult. Qed.
