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
  split...
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
    destruct (p (first_nat p x)) eqn: H0...
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
Proof with (lia || eauto).
  cut (forall z : nat, forall y : nat, forall x : nat, z = x + y -> (x, y) = cantor_pairing (sum_from_0_to z + y))...
  induction z.
  - intros y x H.
    assert (H0 : x = 0)...
    assert (H1 : y = 0)...
    subst...
  - induction y.
    + intros x H.
      assert (H0 : x = S z)... subst. simpl.
      destruct (cantor_pairing (z + sum_from_0_to z + 0)) eqn: H0.
      assert (H1 : (0, z) = cantor_pairing (sum_from_0_to z + z))...
      rewrite Nat.add_0_r in H0. rewrite Nat.add_comm in H0. rewrite H0 in H1.
      inversion H1. subst...
    + intros x H.
      assert (H0 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)). { apply (IHy (S x))... }
      assert (H1 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y). { simpl... }
      simpl. rewrite H1. rewrite <- H0...
Qed.

Lemma cantor_pairing_is_injective :
  forall n : nat,
  forall x : nat,
  forall y : nat,
  cantor_pairing n = (x, y) ->
  n = sum_from_0_to (x + y) + y.
Proof with (lia || eauto).
  induction n; simpl.
  - intros x y H.
    inversion H. subst...
  - intros x y H.
    destruct (cantor_pairing n) as [x' y'] eqn: H0.
    destruct x'; (inversion H; subst).
    + repeat (rewrite Nat.add_0_r).
      simpl.
      rewrite (IHn 0 y' eq_refl).
      rewrite Nat.add_0_l...
    + rewrite (IHn (S x) y' eq_refl).
      assert (H1 : forall x' : nat, S x' + y' = x' + S y')...
      repeat (rewrite H1)...
Qed.

Lemma cantor_pairing_is :
  forall n : nat,
  forall x : nat,
  forall y : nat,
  cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
Proof.
  intros n x y; split; [apply (cantor_pairing_is_injective n x y) | intros; subst; eauto using (cantor_pairing_is_surjective x y)].
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
  unfold extensionality. induction n; [reflexivity | simpl]...
Qed.

Lemma extensionality_symm {A : Type} :
  forall n : nat,
  forall f : Arity n A,
  forall g : Arity n A,
  extensionality A n f g ->
  extensionality A n g f.
Proof with eauto.
  unfold extensionality. induction n; [symmetry | simpl]...
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
  unfold extensionality. induction n; [intros; transitivity g | simpl]...
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

Fixpoint unassocArity (m : nat) : forall n : nat, Arity (m + n) w -> Arity m (Arity n w) :=
  match m with
  | 0 => fun n : nat => fun f : Arity n w => f
  | S m' => fun n : nat => fun f : w -> Arity (m' + n) w => fun r : w => unassocArity m' n (f r)
  end
.

Fixpoint assocArity (m : nat) : forall n : nat, Arity m (Arity n w) -> Arity (m + n) w :=
  match m with
  | 0 => fun n : nat => fun f : Arity n w => f
  | S m' => fun n : nat => fun f : w -> Arity m' (Arity n w) => fun r : w => assocArity m' n (f r)
  end
.

Lemma composition_arity_1 (n : nat) :
  forall f : w -> w,
  forall g1 : Arity n w,
  extensionality w (n + 0) (assocArity n 0 (apArity n (pureArity n f) g1)) (load n 0 (call n 1 f) g1).
Proof.
  unfold extensionality. induction n; now simpl.
Qed.

Lemma composition_arity_2 (n : nat) :
  forall f : w -> w -> w,
  forall g1 : Arity n w,
  forall g2 : Arity n w,
  extensionality w (n + 0) (assocArity n 0 (apArity n (apArity n (pureArity n f) g1) g2)) (load n 0 (load n 1 (call n 2 f) g1) g2).
Proof.
  unfold extensionality. induction n; now simpl.
Qed.

Definition less : Arity 2 w :=
  fun x : w => fun y : w => if Compare_dec.lt_dec x y then 0 else 1
.

Definition mini (n : nat) : Arity (n + 1) w -> Arity n w -> Arity n w :=
  fun val : Arity (n + 1) w => fun witness : Arity n w => apArity n (apArity n (pureArity n (fun f : w -> w => fun x : w => first_nat (fun r : w => Nat.eqb (f r) 0) x)) (unassocArity n 1 val)) witness
.

Inductive IsArith : forall n : nat, Arity n w -> Prop :=
| plusA :
  forall f : Arity 2 w,
  extensionality w 2 f plus ->
  IsArith 2 f
| multA :
  forall f : Arity 2 w,
  extensionality w 2 f mult ->
  IsArith 2 f
| lessA :
  forall f : Arity 2 w,
  extensionality w 2 f less ->
  IsArith 2 f
| projA :
  forall m : nat,
  forall n : nat,
  forall f : Arity (m + S n) w,
  extensionality w (m + S n) f (proj m n) ->
  IsArith (m + S n) f
| loadA :
  forall m : nat,
  forall n : nat,
  forall val1 : Arity (m + S n) w,
  forall val2 : Arity m w,
  forall f : Arity (m + n) w,
  IsArith (m + S n) val1 ->
  IsArith m val2 ->
  extensionality w (m + n) f (load m n val1 val2) ->
  IsArith (m + n) f
| callA :
  forall m : nat,
  forall n : nat,
  forall val1 : Arity n w,
  forall f : Arity (m + n) w,
  IsArith n val1 ->
  extensionality w (m + n) f (call m n val1) ->
  IsArith (m + n) f
| miniA :
  forall m : nat,
  forall val1 : Arity (m + 1) w,
  forall witness : Arity m w,
  forall f : Arity m w,
  IsArith (m + 1) val1 ->
  universal m (apArity m (apArity m (pureArity m (fun f : w -> w => fun x : w => f x = 0)) (unassocArity m 1 val1)) witness) ->
  extensionality w m f (mini m val1 witness) ->
  IsArith m f
.

Ltac heehee := 
  tryif (apply extensionality_refl) then eauto else unfold extensionality; (simpl; reflexivity || eauto)
.

Ltac auto_show_IsArith :=
  match goal with
  | |- IsArith _ plus => apply plusA; heehee
  | |- IsArith _ mult => apply multA; heehee
  | |- IsArith _ less => apply lessA; heehee
  | |- IsArith _ (proj ?m ?n) => apply (projA m n); heehee
  | |- IsArith _ (load ?m ?n ?val1 ?val2) => apply (loadA m n val1 val2); [auto_show_IsArith | auto_show_IsArith | heehee]
  | |- IsArith _ (call ?m ?n ?val1) => apply (callA m n val1); [auto_show_IsArith | heehee]
  | |- IsArith _ (mini ?m ?val1 ?witness) => apply (miniA m val1 witness); [auto_show_IsArith | heehee | heehee]
  | _ => eauto
  end
.

Definition isBoolean (n : nat) : Arity n w -> Prop :=
  fun val1 : Arity n w => universal n (apArity n (pureArity n (fun x1 : w => x1 = 0 \/ x1 = 1)) val1)
.

Fixpoint isCharOn (n : nat) : Arity (n + 0) w -> Arity n Prop -> Prop :=
  match n with
  | 0 => fun f : w => fun p : Prop => if Nat.eq_dec f 0 then p else ~ p
  | S n' => fun f : w -> Arity (n' + 0) w => fun p : w -> Arity n' Prop => forall r : w, isCharOn n' (f r) (p r)
  end
.

Inductive IsRecursive : forall n : nat, Arity n Prop -> Prop :=
| Recursiveness :
  forall m : nat,
  forall val1 : Arity (m + 0) w,
  forall P1 : Arity m Prop,
  IsArith (m + 0) val1 ->
  isBoolean (m + 0) val1 -> 
  isCharOn m val1 P1 ->
  IsRecursive m P1
.

Lemma less_isBoolean :
  isBoolean 2 less.
Proof with eauto.
  unfold isBoolean. unfold less. simpl.
  intros. destruct (Compare_dec.lt_dec m m0); tauto.
Qed.

Fixpoint num (i : nat) : Arity 0 w :=
  match i with
  | 0 => mini 0 (proj 0 0) 0
  | S i' => mini 0 (load 1 0 (call 1 1 (load 0 1 (call 0 2 less) (num i'))) (proj 0 0)) (S i')
  end
.

Lemma num_is (m : nat) :
  forall i : nat,
  extensionality w (m + 0) (call m 0 (num i)) (pureArity (m + 0) i).
Proof with eauto.
  assert ( claim1 :
    forall n : nat,
    S n = first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n)
  ).
  { assert (forall n : nat, forall p : nat -> bool, first_nat p n <= n).
    { induction n...
      simpl. intros p. destruct (p (first_nat p n)) eqn: H0...
    }
    intros n.
    assert (first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n) <= S n) by apply H.
    set (p := (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0)).
    assert (p (first_nat p (S n)) = true).
    { apply well_ordering_principle...
      unfold p. destruct (Compare_dec.lt_dec n (S n))...
    }
    unfold p in H1. destruct (Compare_dec.lt_dec n (first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n))); [unfold p; lia | inversion H1].
  }
  unfold extensionality.
  induction m; simpl...
  induction i; simpl; unfold mini; simpl...
  rewrite IHi. cut (first_nat (fun r : w => (if Compare_dec.lt_dec i r then 0 else 1) =? 0) (S i) = S i); unfold less...
Qed.

Lemma numIsArith (i : nat) :
  IsArith 0 (num i).
Proof with heehee.
  induction i; simpl; auto_show_IsArith.
  - apply (projA 0 0)...
  - apply (loadA 0 1 less (num i))...
    apply lessA...
  - simpl. unfold less.
    assert (H : num i = i) by apply (num_is 0 i). rewrite H.
    destruct (Compare_dec.lt_dec i (S i)); [tauto | lia].
Qed.

Definition not : Arity 1 w :=
  load 1 0 (load 1 1 (call 1 2 less) (call 1 0 (num 0))) (proj 0 0)
.

Lemma not_is (m : nat) :
  forall val1 : Arity m w,
  forall P1 : Arity m Prop,
  isCharOn m (assocArity m 0 val1) P1 ->
  isCharOn m (load m 0 (call m 1 not) val1) (apArity m (pureArity m (fun p1 : Prop => ~ p1)) P1).
Proof with eauto.
  induction m; simpl...
  unfold not. intros.
  assert (H0 : num 0 = 0) by apply (num_is 0 0). rewrite H0.
  unfold less. simpl.
  destruct (Nat.eq_dec val1 0); simpl.
  - subst. simpl. tauto.
  - destruct (Compare_dec.lt_dec 0 val1); simpl; [tauto | lia].
Qed.

Lemma not_isBoolean :
  isBoolean 1 not.
Proof with eauto.
  unfold isBoolean. unfold not. unfold less. simpl.
  apply less_isBoolean.
Qed.

Lemma notIsArith :
  IsArith 1 not.
Proof with heehee.
  unfold not. auto_show_IsArith.
  apply numIsArith.
Qed.

Definition or : Arity 2 w :=
  load 2 0 (call 2 1 not) (load 2 0 (call 2 1 not) (load 2 0 (load 2 1 (call 2 2 mult) (proj 0 1)) (proj 1 0)))
.

Lemma or_is (m : nat) :
  forall val1 : Arity m w,
  forall val2 : Arity m w,
  forall P1 : Arity m Prop,
  forall P2 : Arity m Prop,
  isCharOn m (assocArity m 0 val1) P1 ->
  isCharOn m (assocArity m 0 val2) P2 ->
  isCharOn m (load m 0 (load m 1 (call m 2 or) val1) val2) (apArity m (apArity m (pureArity m (fun p1 : Prop => fun p2 : Prop => p1 \/ p2)) P1) P2).
Proof with eauto.
  induction m; simpl...
  unfold or. unfold not. simpl.
  unfold less. unfold mini. simpl.
  intros. destruct (Nat.eq_dec val1 0); destruct (Nat.eq_dec val2 0).
  - subst.
    simpl; tauto.
  - subst.
    simpl; tauto.
  - assert (H1 : val1 * val2 = 0) by lia. rewrite H1.
    simpl; tauto.
  - assert (H1 : val1 * val2 <> 0) by lia.
    destruct (Compare_dec.lt_dec 0 (val1 * val2)); simpl; [tauto | lia].
Qed.

Lemma or_isBoolean :
  isBoolean 2 or.
Proof with eauto.
  unfold isBoolean. simpl. intros. apply not_isBoolean.
Qed.

Lemma orIsArith :
  IsArith 2 or.
Proof with heehee.
  unfold or. auto_show_IsArith; apply notIsArith.
Qed.

End Arithmetic.

End Goedel's_Incompleteness_Theorem.
