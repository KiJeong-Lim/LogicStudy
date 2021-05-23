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

Definition liftArity1 {A : Type} {B : Type} (n : nat) : (A -> B) -> Arity n A -> Arity n B :=
  fun f : A -> B => fun val1 : Arity n A => apArity n (pureArity n f) val1
.

Definition liftArity2 {A : Type} {B : Type} {C : Type} (n : nat) : (A -> B -> C) -> Arity n A -> Arity n B -> Arity n C :=
  fun f : A -> B -> C => fun val1 : Arity n A => fun val2 : Arity n B => apArity n (apArity n (pureArity n f) val1) val2
.

Fixpoint assocArity (A : Type) (n : nat) : forall i : nat, Arity n (Arity i A) -> Arity (n + i) A :=
  match n with
  | 0 => fun i : nat => fun val : Arity i A => val
  | S n' => fun i : nat => fun val : w -> Arity n' (Arity i A) => fun m : w => assocArity A n' i (val m)
  end
.

Fixpoint shiftArity_left {A : Type} (n : nat) : Arity (S n) A -> Arity n (w -> A) :=
  match n with
  | 0 => fun val : w -> A => val
  | S n' => fun val : w -> Arity (S n') A => fun m : w => shiftArity_left n' (val m)
  end
.

Fixpoint shiftArity_right {A : Type} (n : nat) : Arity n (w -> A) -> Arity (S n) A :=
  match n with
  | 0 => fun val : w -> A => val
  | S n' => fun val : w -> Arity n' (w -> A) => fun m : w => shiftArity_right n' (val m)
  end
.

Lemma pure_assoc_pure {A : Type} :
  forall n : nat,
  forall x : A,
  pureArity (n + 0) x = assocArity A n 0 (pureArity n x).
Proof with eauto.
  induction n... simpl. intros x. rewrite IHn...
Qed.

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
  forall R_dec : Arity_dec n R (liftArity1 n (fun r : Prop => ~ r) R),
  forall val1 : Arity n A,
  forall val2 : Arity n A,
  universal n (apArity n (apArity n (apArity n (apArity n (pureArity n (fun r : Prop => fun x1 : A => fun x2 : A => fun x : A => (r -> x = x1) /\ (~ r -> x = x2))) R) val1) val2) (Arity_ite n R (liftArity1 n (fun r : Prop => ~ r) R) R_dec val1 val2)).
Proof with eauto.
  unfold liftArity1. induction n.
  - simpl. intros. destruct R_dec; firstorder.
  - simpl...
Qed.

Definition extensionality (A : Type) (n : nat) : Arity n A -> Arity n A -> Prop :=
  fun val1 : Arity n A => fun val2 : Arity n A => universal n (liftArity2 n (fun x1 : A => fun x2 : A => x1 = x2) val1 val2)
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

Lemma extensionality_lift1 {A : Type} {B : Type} :
  forall n : nat,
  forall f : A -> B,
  forall val1 : Arity n A,
  forall val2 : Arity n A,
  extensionality A n val1 val2 ->
  extensionality B n (liftArity1 n f val1) (liftArity1 n f val2).
Proof with eauto.
  unfold extensionality. induction n.
  - intros. apply f_equal...
  - simpl...
Qed.

Lemma extensionality_lift2 {A : Type} {B : Type} {C : Type} :
  forall n : nat,
  forall f : A -> B -> C,
  forall val1 : Arity n A,
  forall val2 : Arity n A,
  forall val3 : Arity n B,
  forall val4 : Arity n B,
  extensionality A n val1 val2 ->
  extensionality B n val3 val4 ->
  extensionality C n (liftArity2 n f val1 val3) (liftArity2 n f val2 val4).
Proof with eauto.
  unfold extensionality. induction n.
  - intros. apply f_equal2...
  - simpl...
Qed.

Inductive arith : Set :=
| projA : nat -> arith
| plusA : arith
| multA : arith
| lessA : arith
| liftA : nat -> arith -> arith
| callA : arith -> arith -> arith
| miniA : arith -> arith
.

Definition proj (n : nat) : Arity (S n) w :=
  pureArity n
.

Definition less (x : w) (y : w) : w :=
  if Compare_dec.lt_dec x y then 0 else 1
.

Definition lift (m : nat) (n : nat) (val1 : Arity n w) : Arity (m + n) w :=
  assocArity w m n (pureArity m val1)
.

Lemma extensionality_lift {A : Type} (m : nat) :
  forall n : nat,
  forall f : Arity n A,
  forall g : Arity n A,
  extensionality A n f g ->
  extensionality A (m + n) (assocArity A m n (pureArity m f)) (assocArity A m n (pureArity m g)).
Proof with eauto.
  unfold extensionality. unfold liftArity2. induction m; simpl...
Qed.

Definition call (n : nat) (val1 : Arity (S n) w) (val2 : Arity n w) : Arity n w :=
  apArity n (shiftArity_left n val1) val2
.

Lemma extensionality_call {A : Type} :
  forall n : nat,
  forall f1 : Arity (S n) A,
  forall f2 : Arity (S n) A,
  forall g1 : Arity n w,
  forall g2 : Arity n w,
  extensionality A (S n) f1 f2 ->
  extensionality w n g1 g2 ->
  extensionality A n (apArity n (shiftArity_left n f1) g1) (apArity n (shiftArity_left n f2) g2).
Proof with eauto.
  unfold extensionality. unfold liftArity2. induction n.
  - simpl. intros. rewrite H0. rewrite H...
  - simpl. intros. apply (IHn (f1 m) (f2 m) (g1 m) (g2 m))... simpl...
Qed.

Definition mini (n : nat) (val1 : Arity (S n) w) (witness : Arity n w) : Arity n w :=
  liftArity2 n first_nat (liftArity1 n (fun f : w -> w => fun x : w => Nat.eqb (f x) 0) (shiftArity_left n val1)) witness
.

Lemma extensionality_mini :
  forall n : nat,
  forall val1 : Arity (S n) w,
  forall val2 : Arity (S n) w,
  extensionality w (S n) val1 val2 ->
  forall witness1 : Arity n w,
  forall witness2 : Arity n w,
  universal n (liftArity1 n (fun x : w => x = 0) (call n val1 witness1)) ->
  universal n (liftArity1 n (fun x : w => x = 0) (call n val2 witness2)) ->
  extensionality w n (mini n val1 witness1) (mini n val2 witness2).
Proof with eauto.
  unfold extensionality. unfold liftArity2. induction n.
  - unfold call. unfold mini. unfold liftArity2. unfold liftArity1. simpl. intros val1 val2 H.
    assert (forall x : w, first_nat (fun y : w => val1 y =? 0) x = first_nat (fun y : w => val2 y =? 0) x). { induction x... simpl. rewrite H. rewrite IHx... }
    intros. rewrite H0. set (p := fun x : w => val2 x =? 0).
    assert (first_nat p witness1 <= first_nat p witness2). { apply well_ordering_principle. unfold p. rewrite <- H... apply well_ordering_principle. unfold p... }
    assert (first_nat p witness2 <= first_nat p witness1). { apply well_ordering_principle. unfold p... apply well_ordering_principle. unfold p. rewrite <- H. rewrite H1. reflexivity. }
    lia.
  - unfold mini. simpl. intros. apply (IHn (val1 m) (val2 m) (H m) (witness1 m) (witness2 m))...
Qed.

Inductive evalArith : forall n : nat, arith -> Arity n w -> Prop :=
| projE :
  forall n : nat,
  evalArith (S n) (projA n) (proj n)
| plusE :
  evalArith 2 plusA plus
| multE :
  evalArith 2 multA mult
| lessE :
  evalArith 2 lessA less
| liftE :
  forall m : nat,
  forall n : nat,
  forall e1 : arith,
  forall val1 : Arity n w,
  evalArith n e1 val1 ->
  evalArith (m + n) (liftA m e1) (lift m n val1)
| callE :
  forall n : nat,
  forall e1 : arith,
  forall e2 : arith,
  forall val1 : Arity (S n) w,
  forall val2 : Arity n w,
  evalArith (S n) e1 val1 ->
  evalArith n e2 val2 ->
  evalArith n (callA e1 e2) (call n val1 val2)
| miniE :
  forall n : nat,
  forall e1 : arith,
  forall val1 : Arity (S n) w,
  forall witness : Arity n w,
  evalArith (S n) e1 val1 ->
  universal n (liftArity1 n (fun x : w => x = 0) (call n val1 witness)) ->
  evalArith n (miniA e1) (mini n val1 witness) 
.

Lemma evalArith_unique :
  forall e : arith,
  forall ary : nat,
  forall f : Arity ary w,
  forall g : Arity ary w,
  evalArith ary e f ->
  evalArith ary e g ->
  extensionality w ary f g.
Proof with eauto.
  induction e.
  - intros. dependent destruction H. dependent destruction H0. apply extensionality_refl.
  - intros. dependent destruction H. dependent destruction H0. apply extensionality_refl.
  - intros. dependent destruction H. dependent destruction H0. apply extensionality_refl.
  - intros. dependent destruction H. dependent destruction H0. apply extensionality_refl.
  - intros. dependent destruction H. dependent destruction H0. assert (n1 = n0) by lia. subst. rewrite <- x. apply extensionality_lift...
  - intros. dependent destruction H. dependent destruction H1. apply extensionality_call...
  - intros. dependent destruction H. dependent destruction H1. apply extensionality_mini...
Qed.

Definition is_char_on (n : nat) : Arity n w -> Arity n Prop -> Prop :=
  fun val1 : Arity n w => fun P1 : Arity n Prop => universal n (liftArity2 n (fun x1 : w => fun p1 : Prop => if Nat.eq_dec x1 0 then p1 else ~ p1) val1 P1)
.

Lemma less_is_char_on_lt :
  is_char_on 2 less (fun x : w => fun y : w => x < y).
Proof with eauto.
  unfold is_char_on. unfold liftArity2. simpl. unfold less. intros. destruct (Compare_dec.lt_dec m m0)...
Qed.

Definition isBoolean (n : nat) : Arity n w -> Prop :=
  fun val1 : Arity n w => universal n (liftArity1 n (fun x1 : w => x1 = 0 \/ x1 = 1) val1)
.

Lemma less_isBoolean :
  isBoolean 2 less.
Proof with eauto.
  unfold isBoolean. unfold liftArity1. simpl. unfold less. intros. destruct (Compare_dec.lt_dec m m0)...
Qed.

Fixpoint num (n : nat) : Arity 0 w :=
  match n with
  | 0 => mini 0 (proj 0) 0
  | S n' => mini 0 (call 1 (lift 1 1 (call 1 less (lift 1 0 (num n')))) (proj 0)) (S n')
  end
.

Fixpoint numA (n : nat) : Arith :=
  match 

End Arithmetic.

End Goedel's_Incompleteness_Theorem.
