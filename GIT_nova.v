From Coq.Bool Require Export Bool.
From Coq.micromega Require Export Lia.
From Coq.Lists Require Export List.
From Coq.Arith Require Export PeanoNat.
From Coq.Program Require Export Equality.

Module Goedel's_Incompleteness_Theorem.

Import ListNotations.

Section Preliminaries.

Lemma div_mod_uniqueness :
  forall a : nat,
  forall b : nat,
  forall q : nat,
  forall r : nat,
  a = b * q + r ->
  r < b ->
  a / b = q /\ a mod b = r.
Proof with lia.
  assert (forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
  { intros x y; constructor.
    - intros H; induction H.
      + exists 0...
      + destruct IHle as [z H0]; exists (S z)...
    - intros H; destruct H as [z H]...
  }
  intros a b q r H1 H2.
  assert (H0 : a = b * (a / b) + (a mod b)). { apply (Nat.div_mod a b)... }
  assert (H3 : 0 <= a mod b < b). { apply (Nat.mod_bound_pos a b)... }
  assert (H4 : ~ q > a / b).
  { intros H4.
    assert (H5 : exists z : nat, q = S (a / b + z)). { apply (H q (a / b))... }
    destruct H5 as [z H5].
    cut (b * q + r >= b * S (a / b) + r)...
  }
  assert (H5 : ~ q < a / b).
  { intros H5.
    assert (H6 : exists z : nat, a / b = S (q + z)). { apply (H (a / b) q)... }
    destruct H6 as [z H6].
    cut (b * q + a mod b >= b * S (a / b) + a mod b)...
  }
  cut (q = a / b)...
Qed.

Fixpoint first_nat (p : nat -> bool) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => if p (first_nat p n') then first_nat p n' else n
  end
.

Theorem well_ordering_principle : 
  forall p : nat -> bool,
  forall n : nat,
  p n = true ->
  let m := first_nat p n in
  p m = true /\ (forall i : nat, p i = true -> i >= m).
Proof with eauto.
  intros p n H3 m.
  assert (forall x : nat, p x = true -> p (first_nat p x) = true).
  { induction x...
    simpl.
    destruct (p (first_nat p x)) eqn:H0...
  }
  constructor...
  intros i H4.
  enough (forall x : nat, first_nat p x <= x).
  enough (forall x : nat, p (first_nat p x) = true -> (forall y : nat, x < y -> first_nat p x = first_nat p y)).
  enough (forall x : nat, forall y : nat, p y = true -> first_nat p x <= y)...
  - intros x y H2.
    destruct (Compare_dec.le_lt_dec x y).
    + eapply Nat.le_trans...
    + replace (first_nat p x) with (first_nat p y)...
  - intros x H1 y H2.
    induction H2; simpl.
    + rewrite H1...
    + rewrite <- IHle.
      rewrite H1...
  - induction x...
    simpl.
    destruct (p (first_nat p x)) eqn:H0...
Qed.

Fixpoint sum_from_0_to (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_from_0_to n'
  end
.

Theorem sum_from_0_to_is :
  forall n : nat,
  2 * sum_from_0_to n = n * (S n).
Proof.
  intros n; induction n.
  - intuition.
  - simpl in *; lia.
Qed.

Fixpoint cantor_pairing (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 0)
  | S n' =>
    match cantor_pairing n' with
    | (0, y) => (S y, 0)
    | (S x, y) => (x, S y)
    end
  end
.

Lemma cantor_pairing_is_surjective :
  forall x : nat,
  forall y : nat,
  (x, y) = cantor_pairing (sum_from_0_to (x + y) + y).
Proof.
  cut (forall z : nat, forall y : nat, forall x : nat, z = x + y -> (x, y) = cantor_pairing (sum_from_0_to z + y)); eauto.
  intros z; induction z.
  - intros y x H; assert (H0 : x = 0) by lia; assert (H1 : y = 0) by lia; subst; eauto.
  - intros y; induction y.
    + intros x H.
      assert (H0 : x = S z) by lia.
      subst; simpl cantor_pairing; destruct (cantor_pairing (z + sum_from_0_to z + 0)) eqn: H0.
      assert (H1 : (0, z) = cantor_pairing (sum_from_0_to z + z)) by (apply IHz; reflexivity).
      rewrite Nat.add_0_r in H0; rewrite Nat.add_comm in H0; rewrite H0 in H1.
      inversion H1; subst; reflexivity.
    + intros x H.
      assert (H0 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)) by (apply (IHy (S x)); lia).
      assert (H1 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y) by (simpl; lia).
      simpl; rewrite H1; rewrite <- H0; eauto.
Qed.

Lemma cantor_pairing_is_injective :
  forall n : nat,
  forall x : nat,
  forall y : nat,
  cantor_pairing n = (x, y) ->
  n = sum_from_0_to (x + y) + y.
Proof.
  intros n; induction n.
  - simpl; intros x y H; inversion H; subst; reflexivity.
  - simpl; intros x y H; destruct (cantor_pairing n) as [x' y'] eqn: H0; destruct x'.
    + inversion H; subst; repeat (rewrite Nat.add_0_r); simpl; rewrite (IHn 0 y' eq_refl); rewrite Nat.add_0_l; lia.
    + inversion H; subst; rewrite (IHn (S x) y' eq_refl); assert (H1 : forall x' : nat, S x' + y' = x' + S y') by lia; repeat (rewrite H1); lia.
Qed.

Theorem cantor_pairing_is :
  forall n : nat,
  forall x : nat,
  forall y : nat,
  cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
Proof.
  intros n x y; constructor.
  - apply (cantor_pairing_is_injective n x y).
  - intros H; subst; rewrite (cantor_pairing_is_surjective x y); reflexivity.
Qed.

End Preliminaries.

Section Arithmetic.

Definition w : Set :=
  nat
.

Fixpoint Arity (n : nat) (A : Type) : Type :=
  match n with
  | 0 => A
  | S n' => w -> Arity n' A
  end
.

Fixpoint universal (n : nat) : Arity n Prop -> Prop :=
  match n with
  | 0 => fun P : Prop => P
  | S n' => fun P : w -> Arity n' Prop => forall m : nat, universal n' (P m)
  end
.

Fixpoint pureArity {A : Type} (n : nat) : A -> Arity n A :=
  match n with
  | 0 => fun x : A => x
  | S n' => fun x : A => fun m : w => pureArity n' x
  end
.

Fixpoint apArity {A : Type} {B : Type} (n : nat) : Arity n (A -> B) -> Arity n A -> Arity n B :=
  match n with
  | 0 => fun f : A -> B => fun x : A => f x
  | S n' => fun f : w -> Arity n' (A -> B) => fun x : w -> Arity n' A => fun m : w => apArity n' (f m) (x m)
  end
.

Fixpoint Arity_dec (n : nat) : Arity n Prop -> Arity n Prop -> Set :=
  match n with
  | 0 => fun P : Prop => fun Q : Prop => {P} + {Q}
  | S n' => fun P : w -> Arity n' Prop => fun Q : w -> Arity n' Prop => forall m : w, Arity_dec n' (P m) (Q m)
  end
.

Fixpoint Arity_ite {A : Type} (n : nat) : forall P : Arity n Prop, forall Q : Arity n Prop, Arity_dec n P Q -> Arity n A -> Arity n A -> Arity n A :=
  match n with
  | 0 => fun P : Prop => fun Q : Prop => fun PQ_dec : {P} + {Q} => fun val1 : A => fun val2 : A => if PQ_dec then val1 else val2
  | S n' => fun P : w -> Arity n' Prop => fun Q : w -> Arity n' Prop => fun PQ_dec : forall m : nat, Arity_dec n' (P m) (Q m) => fun val1 : w -> Arity n' A => fun val2 : w -> Arity n' A => fun m : w => Arity_ite n' (P m) (Q m) (PQ_dec m) (val1 m) (val2 m)
  end
.

Lemma Arity_ite_is {A : Type} :
  forall n : nat,
  forall R : Arity n Prop,
  forall R_dec : Arity_dec n R (apArity n (pureArity n (fun r : Prop => ~ r)) R),
  forall val1 : Arity n A,
  forall val2 : Arity n A,
  universal n (apArity n (apArity n (apArity n (apArity n (pureArity n (fun r : Prop => fun x1 : A => fun x2 : A => fun x : A => (r -> x = x1) /\ (~ r -> x = x2))) R) val1) val2) (Arity_ite n R (apArity n (pureArity n (fun r : Prop => ~ r)) R) R_dec val1 val2)).
Proof with eauto.
  induction n.
  - simpl. intros. destruct R_dec; firstorder.
  - simpl...
Qed.

Definition extensionality (A : Type) (n : nat) : Arity n A -> Arity n A -> Prop :=
  fun val1 : Arity n A => fun val2 : Arity n A => universal n (apArity n (apArity n (pureArity n (fun x1 : A => fun x2 : A => x1 = x2)) val1) val2)
.

Lemma extensionality_refl {A : Type} :
  forall n : nat,
  forall f : Arity n A,
  extensionality A n f f.
Proof with eauto.
  unfold extensionality. induction n.
  - reflexivity.
  - simpl...
Qed.

Lemma extensionality_symm {A : Type} :
  forall n : nat,
  forall f : Arity n A,
  forall g : Arity n A,
  extensionality A n f g ->
  extensionality A n g f.
Proof with eauto.
  unfold extensionality. induction n.
  - symmetry...
  - simpl...
Qed.

Lemma extensionality_trans {A : Type} :
  forall n : nat,
  forall f : Arity n A,
  forall g : Arity n A,
  forall h : Arity n A,
  extensionality A n f g ->
  extensionality A n g h ->
  extensionality A n f h.
Proof with eauto.
  unfold extensionality. induction n.
  - intros. transitivity g...
  - simpl...
Qed.

Fixpoint proj (m : nat) : forall n : nat, Arity (m + S n) w :=
  match m with
  | 0 => fun n : nat => pureArity n
  | S m' => fun n : nat => fun r : w => proj m' n
  end
.

Example proj_example1 :
  proj 2 1 = (fun x0 : w => fun x1 : w => fun x2 : w => fun x3 : w => x2).
Proof.
  reflexivity.
Qed.

Fixpoint call (m : nat) : forall n : nat, Arity n w -> Arity (m + n) w :=
  match m with
  | 0 => fun n : nat => fun f : Arity n w => f
  | S m' => fun n : nat => fun f : Arity n w => fun r : w => call m' n f
  end
.

Example call_example1 (f : w -> w -> w) :
  call 1 2 f = (fun x0 : w => fun x1 : w => fun x2 : w => f x1 x2).
Proof.
  reflexivity.
Qed.

Fixpoint load (m : nat) : forall n : nat, Arity (m + S n) w -> Arity m w -> Arity (m + n) w :=
  match m with
  | 0 => fun n : nat => fun f : Arity (S n) w => fun g : w => f g
  | S m' => fun n : nat => fun f : w -> Arity (m' + S n) w => fun g : w -> Arity m' w => fun r : w => load m' n (f r) (g r)
  end
.

Example load_example1 (f : w -> w -> w -> w -> w -> w -> w) (g : w -> w -> w -> w) :
  load 3 2 f g = (fun x0 : w => fun x1 : w => fun x2 : w => fun x3 : w => f x0 x1 x2 (g x0 x1 x2) x3).
Proof.
  reflexivity.
Qed.

Example composition_example1 (f : w -> w -> w -> w -> w) (g1 : w -> w -> w) (g2 : w -> w -> w) (g3 : w -> w -> w) (g4 : w -> w -> w) :
  (fun x0 : w => fun x1 : w => f (g1 x0 x1) (g2 x0 x1) (g3 x0 x1) (g4 x0 x1)) = load 2 0 (load 2 1 (load 2 2 (load 2 3 (call 2 4 f) g1) g2) g3) g4.
Proof.
  reflexivity.
Qed.

Example composition_example2 (f : w -> w -> w) (g1 : w -> w -> w -> w) (g2 : w -> w -> w -> w) :
  (fun x0 : w => fun x1 : w => fun x2 : w => f (g1 x0 x1 x2) (g2 x0 x1 x2)) = load 3 0 (load 3 1 (call 3 2 f) g1) g2.
Proof.
  reflexivity.
Qed.

Fixpoint shiftZeroRight (n : nat) : Arity n w -> Arity (n + 0) w :=
  match n with
  | 0 => fun f : w => f
  | S n' => fun f : w -> Arity n' w => fun r : w => shiftZeroRight n' (f r)
  end
.

Lemma composition_arity_1 (n : nat) :
  forall f : w -> w,
  forall g1 : Arity n w,
  extensionality w (n + 0) (shiftZeroRight n (apArity n (pureArity n f) g1)) (load n 0 (call n 1 f) g1).
Proof with eauto.
  unfold extensionality.
  induction n; [easy | simpl]...
Qed.

Lemma composition_arity_2 (n : nat) :
  forall f : w -> w -> w,
  forall g1 : Arity n w,
  forall g2 : Arity n w,
  extensionality w (n + 0) (shiftZeroRight n (apArity n (apArity n (pureArity n f) g1) g2)) (load n 0 (load n 1 (call n 2 f) g1) g2).
Proof with eauto.
  unfold extensionality.
  induction n; [easy | simpl]...
Qed.

End Arithmetic.

End Goedel's_Incompleteness_Theorem.
