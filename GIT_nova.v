From Coq.Bool Require Export Bool.
From Coq.micromega Require Export Lia.
From Coq.Lists Require Export List.
From Coq.Arith Require Export PeanoNat.
From Coq.Strings Require Export String.

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
Proof.
  assert (forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
  { intros x y; constructor.
    - intros H; induction H.
      + exists 0; lia.
      + destruct IHle as [z H0]; exists (S z); lia.
    - intros H; destruct H as [z H]; lia.
  }
  intros a b q r H1 H2.
  assert (H0 : a = b * (a / b) + (a mod b)) by (apply (Nat.div_mod a b); lia).
  assert (H3 : 0 <= a mod b < b).
  { apply (Nat.mod_bound_pos a b).
    - lia.
    - lia.
  }
  assert (H4 : ~ q > a / b).
  { intros H4.
    assert (H5 : exists z : nat, q = S (a / b + z)) by (apply (H q (a / b)); lia).
    destruct H5 as [z H5].
    cut (b * q + r >= b * S (a / b) + r); lia.
  }
  assert (H5 : ~ q < a / b).
  { intros H5.
    assert (H6 : exists z : nat, a / b = S (q + z)) by (apply (H (a / b) q); lia).
    destruct H6 as [z H6].
    cut (b * q + a mod b >= b * S (a / b) + a mod b); lia.
  }
  assert (H6 : q = a / b) by lia; assert (H7 : r = a mod b) by lia; lia.
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

Definition arity : Set :=
  nat
.

Inductive Arith : Set :=
| varArith : arity -> Arith
| plusArith : Arith -> Arith -> Arith
| multArith : Arith -> Arith -> Arith
| ltArith : Arith -> Arith -> Arith
| muArith : Arith -> Arith
.

Definition w : Set :=
  nat
.

Fixpoint Lift (ary : arity) (A : Type) : Type :=
  match ary with
  | 0 => A
  | S ary' => w -> Lift ary' A
  end
.

Fixpoint unLiftProp (ary : arity) : Lift ary Prop -> Prop :=
  match ary with
  | 0 =>
    fun P : Prop =>
    P
  | S ary' =>
    fun A : w -> Lift ary' Prop =>
    forall n : w, unLiftProp ary' (A n)
  end
.

Fixpoint returnLift {A : Type} (ary : arity) : A -> Lift ary A :=
  match ary with
  | 0 =>
    fun x : A =>
    x
  | S ary' =>
    fun x : A =>
    fun _ : w =>
    returnLift ary' x
  end
.

Fixpoint bindLift {A : Type} {B : Type} (ary : arity) : Lift ary A -> (A -> Lift ary B) -> Lift ary B :=
  match ary with
  | 0 =>
    fun x : A =>
    fun f : A -> B =>
    f x
  | S ary' =>
    fun x : w -> Lift ary' A =>
    fun f : A -> w -> Lift ary' B =>
    fun w : nat =>
    bindLift ary' (x w) (fun a : A => f a w)
  end
.

Fixpoint upgradeLift {A : Type} (n : arity) : forall ary : arity, Lift ary A -> Lift (n + ary) A :=
  match n with
  | 0 =>
    fun ary : arity =>
    fun x : Lift ary A =>
    x
  | S n' =>
    fun ary : arity =>
    fun x : Lift ary A =>
    fun _ : w =>
    upgradeLift n' ary x
  end
.

Fixpoint shiftLift_left {A : Type} (ary : arity) : Lift (S ary) A -> Lift ary (w -> A) :=
  match ary with
  | 0 =>
    fun f : w -> A =>
    f
  | S ary' =>
    fun f : w -> Lift (S ary') A =>
    fun x : w =>
    shiftLift_left ary' (f x)
  end
.

Fixpoint shiftLift_right {A : Type} (ary : arity) : Lift ary (w -> A) -> Lift (S ary) A :=
  match ary with
  | 0 =>
    fun f : w -> A =>
    f
  | S ary' =>
    fun f : w -> Lift ary' (w -> A) =>
    fun x : w =>
    shiftLift_right ary' (f x)
  end
.

Definition apLift {A : Type} {B : Type} (ary : arity) (f : Lift ary (A -> B)) (x : Lift ary A) : Lift ary B :=
  bindLift ary f (fun f' : A -> B => bindLift ary x (fun x' : A => returnLift ary (f' x')))
.

Fixpoint assocLift {A : Type} (n : arity) : forall ary, Lift n (Lift ary A) -> Lift (n + ary) A :=
  match n with
  | 0 =>
    fun ary : arity =>
    fun f : Lift ary A =>
    f
  | S n' =>
    fun ary : arity =>
    fun f : w -> Lift n' (Lift ary A) =>
    fun x : w =>
    assocLift n' ary (f x)
  end
.

Definition projection (n : arity) (m : arity) : Lift (m + (n + 1)) w :=
  assocLift m (n + 1) (returnLift m (upgradeLift n 1 (fun x : w => x)))
.

Definition chi_lt (x : w) (y : w) : w :=
  if Compare_dec.lt_dec x y then 0 else 1
.

Definition check (ary : arity) (val : Lift (S ary) w) : Lift ary (w -> bool) :=
  apLift ary (returnLift ary (fun f : w -> w => fun x : w => Nat.eqb (f x) 0)) (shiftLift_left ary val)
.

Inductive evalArith : forall ary : arity, Arith -> Lift ary w -> Prop :=
| varEval :
  forall m : arity,
  forall n : arity,
  evalArith (m + (n + 1)) (varArith n) (projection n m)
| plusEval :
  forall ary : arity,
  forall val1 : Lift ary w,
  forall val2 : Lift ary w,
  forall e1 : Arith,
  forall e2 : Arith,
  evalArith ary e1 val1 ->
  evalArith ary e2 val2 ->
  evalArith ary (plusArith e1 e2) (apLift ary (apLift ary (returnLift ary plus) val1) val2)
| multEval :
  forall ary : arity,
  forall val1 : Lift ary w,
  forall val2 : Lift ary w,
  forall e1 : Arith,
  forall e2 : Arith,
  evalArith ary e1 val1 ->
  evalArith ary e2 val2 ->
  evalArith ary (multArith e1 e2) (apLift ary (apLift ary (returnLift ary mult) val1) val2)
| ltEval :
  forall ary : arity,
  forall val1 : Lift ary w,
  forall val2 : Lift ary w,
  forall e1 : Arith,
  forall e2 : Arith,
  evalArith ary e1 val1 ->
  evalArith ary e2 val2 ->
  evalArith ary (ltArith e1 e2) (apLift ary (apLift ary (returnLift ary chi_lt) val1) val2)
| muEval :
  forall ary : arity,
  forall val1 : Lift (S ary) w,
  forall val' : Lift ary w,
  forall e1 : Arith,
  evalArith (S ary) e1 val1 ->
  unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun f : w -> bool => fun x : w => f x = true)) (check ary val1)) val') ->
  evalArith ary (muArith e1) (apLift ary (apLift ary (returnLift ary first_nat) (check ary val1)) val')
.

Lemma upgradeEval_once :
  forall ary : arity,
  forall e : Arith,
  forall val : Lift ary w,
  evalArith ary e val ->
  evalArith (S ary) e (upgradeLift 1 ary val).
Proof.
  intros ary e val H; induction H.
  - apply (varEval (S m) n).
  - apply (plusEval (S ary)); eauto.
  - apply (multEval (S ary)); eauto.
  - apply (ltEval (S ary)); eauto.
  - apply (muEval (S ary)); eauto.
    simpl; intros n; apply H0.
Qed.

Definition IsArithmetic (ary : arity) (func : Lift ary w) : Prop :=
  exists e : Arith, evalArith ary e func
.

Definition funcIsRecursive (ary : arity) (func : Lift ary w) : Prop :=
  exists func1 : Lift ary w, IsArithmetic ary func1 /\ unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun x : w => fun y : w => x = y)) func) func1)
.

Definition relIsRecursive (ary : arity) (rel : Lift ary Prop) : Prop :=
  exists func : Lift ary w, funcIsRecursive ary func /\ unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun P : Prop => fun n : w => (P -> n = 0) /\ (~ P -> n = 1))) rel) func)
.

Definition IsRecursivelyEnumerable (ary : arity) (rel : Lift ary Prop) : Prop :=
  exists rel1 : Lift (S ary) Prop, unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun P : Prop => fun Q : w -> Prop => P <-> exists x : w, Q x)) rel) (shiftLift_left ary rel1)) /\ relIsRecursive (S ary) rel1
.

Lemma constantsIsRecursive :
  forall n : nat,
  funcIsRecursive 0 n.
Proof.
  assert ( claim1 :
    forall n : nat,
    S n = first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n)
  ).
  { assert (forall n : nat, forall p : nat -> bool, first_nat p n <= n).
    { induction n.
      - reflexivity.
      - simpl.
        intros p.
        destruct (p (first_nat p n)) eqn: H0.
        + assert (first_nat p n <= n) by apply IHn.
          lia. 
        + reflexivity.
    }
    intros n.
    assert (first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n) <= S n) by apply H.
    set (p := (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0)).
    assert (p (first_nat p (S n)) = true).
    { apply well_ordering_principle.
      unfold p.
      destruct (Compare_dec.lt_dec n (S n)).
      - reflexivity.
      - lia.
    }
    unfold p in H1.
    destruct (Compare_dec.lt_dec n (first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n))).
    - unfold p.
      lia.
    - inversion H1.
  }
  induction n.
  - assert (evalArith 0 (muArith (varArith 0)) 0).
    { cut (evalArith 0 (muArith (varArith 0)) (apLift 0 (apLift 0 (returnLift 0 first_nat) (check 0 (fun x : w => x))) 0)); eauto.
      apply muEval.
      - apply (varEval 0 0).
      - reflexivity.
    }
    exists 0.
    constructor.
    + exists (muArith (varArith 0)).
      apply H.
    + reflexivity.
  - destruct IHn as [func1].
    destruct H.
    simpl in H0.
    destruct H as [e].
    assert (evalArith 0 (muArith (ltArith e (varArith 0))) (apLift 0 (apLift 0 (returnLift 0 first_nat)) (check 0 (shiftLift_left 0 (fun x : w => chi_lt n x))) (S n))).
    { apply (muEval 0 (fun x : w => chi_lt n x) (S n)).
      - apply (ltEval 1).
        + apply upgradeEval_once.
          unfold apLift in H0.
          simpl in H0.
          rewrite H0.
          apply H.
        + apply (varEval 0 0).
      - unfold apLift.
        simpl.
        unfold check.
        simpl.
        unfold apLift.
        simpl.
        unfold chi_lt.
        destruct (Compare_dec.lt_dec n (S n)).
        + reflexivity.
        + contradiction n0; lia.
    }
    exists ((apLift 0 (apLift 0 (returnLift 0 first_nat)) (check 0 (shiftLift_left 0 (fun x : w => chi_lt n x))) (S n))).
    constructor.
    + exists (muArith (ltArith e (varArith 0))).
      apply H1.
    + unfold apLift.
      simpl.
      unfold check.
      unfold apLift.
      unfold chi_lt.
      simpl.
      cut (S n = first_nat (fun x : w => Nat.eqb (if Compare_dec.lt_dec n x then 0 else 1) 0) (S n)); eauto.
Qed.

End Arithmetic.

End Goedel's_Incompleteness_Theorem.
