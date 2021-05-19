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

Lemma assoc_return :
  forall ary : arity,
  returnLift (ary + 0) 0 = assocLift ary 0 (returnLift ary 0).
Proof with eauto.
  induction ary... simpl. rewrite IHary...
Qed.

Definition projection (n : arity) (m : arity) : Lift (m + S n) w :=
  assocLift m (S n) (returnLift m (returnLift n))
.

Example projection_ex1 : projection 0 4 = (fun x4 : w => fun x3 : w => fun x2 : w => fun x1 : w => fun x0 : w => x0) := eq_refl.

Example projection_ex2 : projection 1 3 = (fun x4 : w => fun x3 : w => fun x2 : w => fun x1 : w => fun x0 : w => x1) := eq_refl.

Example projection_ex3 : projection 2 2 = (fun x4 : w => fun x3 : w => fun x2 : w => fun x1 : w => fun x0 : w => x2) := eq_refl.

Example projection_ex4 : projection 3 1 = (fun x4 : w => fun x3 : w => fun x2 : w => fun x1 : w => fun x0 : w => x3) := eq_refl.

Example projection_ex5 : projection 4 0 = (fun x4 : w => fun x3 : w => fun x2 : w => fun x1 : w => fun x0 : w => x4) := eq_refl.

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
  evalArith (m + S n) (varArith n) (projection n m)
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

Lemma liftEval_once :
  forall ary : arity,
  forall e : Arith,
  forall val : Lift ary w,
  evalArith ary e val ->
  evalArith (S ary) e (returnLift 1 val).
Proof with eauto.
  intros ary e val H; induction H.
  - apply (varEval (S m) n)...
  - apply (plusEval (S ary))...
  - apply (multEval (S ary))...
  - apply (ltEval (S ary))...
  - apply (muEval (S ary))... simpl...
Qed.

Lemma liftEval (n : arity) :
  forall ary : arity,
  forall e : Arith,
  forall val : Lift ary w,
  evalArith ary e val ->
  evalArith (n + ary) e (assocLift n ary (returnLift n val)).
Proof.
  induction n; eauto. simpl; eauto using liftEval_once.
Qed.

Definition correspondsToFunc (ary : arity) (func1 : Lift ary w) (func : Lift ary w) : Prop :=
  unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun x : w => fun y : w => x = y)) func) func1)
.

Example correspondsToFunc_ex1 (f : Lift 2 w) :
  correspondsToFunc 2 (fun x1 : w => fun x0 : w => f x1 x0) (apLift 2 (apLift 2 (returnLift 2 f) (projection 1 0)) (projection 0 1)).
Proof.
  unfold correspondsToFunc.
  unfold apLift.
  simpl.
  reflexivity.
Qed.

Definition correspondsToRel (ary : arity) (func1 : Lift ary w) (rel : Lift ary Prop) : Prop :=
  unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun p : Prop => fun x : w => (~ ~ p -> x = 0) /\ (~ p -> x = 1))) rel) func1)
.

Example correspondsToRel_ex1 :
  correspondsToRel 2 (fun x1 : w => fun x0 : w => chi_lt x1 x0) (apLift 2 (apLift 2 (returnLift 2 lt) (projection 1 0)) (projection 0 1)).
Proof.
  unfold correspondsToRel.
  unfold chi_lt.
  unfold projection.
  unfold apLift.
  simpl.
  intros n1 n2.
  destruct (Compare_dec.lt_dec n1 n2); lia.
Qed.

Inductive IsRecursivelyEnumerable : forall ary : arity, Lift ary Prop -> Prop :=
| IsRE :
  forall e : Arith,
  forall ary : arity,
  forall func1 : Lift (S ary) w,
  forall rel1 : Lift (S ary) Prop,
  forall rel : Lift ary Prop,
  evalArith (S ary) e func1 ->
  correspondsToRel (S ary) func1 rel1 ->
  unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun P : Prop => fun Q : w -> Prop => P <-> exists x : w, Q x)) rel) (shiftLift_left ary rel1)) -> 
  IsRecursivelyEnumerable ary rel
.

Fixpoint numEval (n : nat) : Lift 0 w :=
  match n with
  | 0 => apLift 0 (apLift 0 (returnLift 0 first_nat) (check 0 (fun x : w => x))) 0
  | S n' => apLift 0 (apLift 0 (returnLift 0 first_nat)) (check 0 (shiftLift_left 0 (fun x : w => chi_lt (numEval n') x))) (S (numEval n'))
  end
.

Lemma numEval_correpondsTo_numeral :
  forall n : nat,
  correspondsToFunc 0 (numEval n) n.
Proof with eauto.
  assert ( claim1 :
    forall n : nat,
    S n = first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n)
  ).
  { assert (forall n : nat, forall p : nat -> bool, first_nat p n <= n).
    { induction n...
      simpl.
      intros p.
      destruct (p (first_nat p n)) eqn: H0...
    }
    intros n.
    assert (first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n) <= S n) by apply H.
    set (p := (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0)).
    assert (p (first_nat p (S n)) = true).
    { apply well_ordering_principle...
      unfold p.
      destruct (Compare_dec.lt_dec n (S n))...
    }
    unfold p in H1.
    destruct (Compare_dec.lt_dec n (first_nat (fun x : w => (if Compare_dec.lt_dec n x then 0 else 1) =? 0) (S n))).
    - unfold p.
      lia.
    - inversion H1.
  }
  induction n.
  - reflexivity.
  - unfold correspondsToFunc in *.
    unfold check in *.
    unfold apLift in *.
    unfold chi_lt in *.
    simpl in *.
    rewrite <- IHn...
Qed.

Fixpoint numArith (n : nat) : Arith :=
  match n with
  | 0 => muArith (varArith 0)
  | S n' => muArith (ltArith (numArith n') (varArith 0))
  end
.

Lemma eval_numArith_numEval :
  forall n : nat,
  evalArith 0 (numArith n) (numEval n).
Proof with eauto.
  induction n.
  - apply muEval.
    + apply (varEval 0 0).
    + reflexivity.
  - simpl.
    assert (n = numEval n) by apply numEval_correpondsTo_numeral.
    cut (evalArith 0 (muArith (ltArith (numArith n) (varArith 0))) (apLift 0 (apLift 0 (returnLift 0 first_nat)) (check 0 (shiftLift_left 0 (fun x : w => chi_lt n x))) (S n))).
    { unfold apLift.
      simpl.
      rewrite <- H...
    }
    apply (muEval 0 (fun x : w => chi_lt n x) (S n)).
    + apply (ltEval 1).
      * apply liftEval_once...
        rewrite <- H in IHn...
      * apply (varEval 0 0).
    + unfold apLift.
      simpl.
      unfold check.
      simpl.
      unfold apLift.
      simpl.
      unfold chi_lt.
      destruct (Compare_dec.lt_dec n (S n))...
Qed.

Definition notEval (ary : arity) (func1 : Lift ary w) : Lift ary w :=
  apLift ary (apLift ary (returnLift ary chi_lt) (returnLift ary 0)) func1
.

Lemma notEval_correpondsTo_negation :
  forall ary : arity,
  forall P1 : Lift ary Prop,
  forall func1 : Lift ary w,
  correspondsToRel ary func1 P1 ->
  correspondsToRel ary (notEval ary func1) (apLift ary (returnLift ary (fun p1 : Prop => ~ p1)) P1).
Proof with eauto.
  assert ( claim1 :
    forall ary : arity,
    forall P : Lift ary Prop,
    forall func1 : Lift ary w,
    unLiftProp ary (bindLift ary (bindLift ary (returnLift ary (fun (p : Prop) (x : w) => (~ ~ p -> x = 0) /\ (~ p -> x = 1))) (fun f' : Prop -> w -> Prop => bindLift ary P (fun x' : Prop => returnLift ary (f' x')))) (fun f' : w -> Prop => bindLift ary func1 (fun x' : w => returnLift ary (f' x')))) ->
    unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun (p : Prop) (x : w) => (~ ~ p -> x = 0) /\ (~ p -> x = 1))) (bindLift ary (returnLift ary (fun p : Prop => ~ p)) (fun f' : Prop -> Prop => bindLift ary P (fun x' : Prop => returnLift ary (f' x'))))) (apLift ary (apLift ary (returnLift ary chi_lt) (returnLift ary 0)) func1))
  ).
  { induction ary.
    - unfold apLift.
      simpl.
      intros.
      unfold chi_lt.
      destruct (Compare_dec.lt_dec 0 func1 ).
      * constructor...
        intros.
        assert (func1 = 0) by tauto.
        lia.
      * assert (func1 = 0) by lia.
        constructor...
        intros.
        assert (func1 = 1) by tauto.
        lia.
    - unfold apLift.
      simpl...
  }
  unfold correspondsToRel...
Qed.

Definition notArith (e1 : Arith) : Arith :=
  ltArith (numArith 0) e1
.

Lemma eval_notArith_notEval :
  forall e1 : Arith,
  forall ary : arity,
  forall func1 : Lift ary w,
  evalArith ary e1 func1 ->
  evalArith ary (notArith e1) (notEval ary func1).
Proof with eauto.
  unfold notEval.
  unfold notArith.
  intros.
  apply ltEval...
  assert (ary = ary + 0)...
  rewrite H0.
  rewrite (assoc_return ary).
  apply liftEval.
  apply eval_numArith_numEval.
Qed.

Definition orEval (ary : arity) (func1 : Lift ary w) (func2 : Lift ary w) : Lift ary w :=
  apLift ary (apLift ary (returnLift ary mult) func1) func2
.

Lemma orEval_correspondsTo_disjunction :
  forall ary : arity,
  forall P1 : Lift ary Prop,
  forall P2 : Lift ary Prop,
  forall func1 : Lift ary w,
  forall func2 : Lift ary w,
  correspondsToRel ary func1 P1 ->
  correspondsToRel ary func2 P2 ->
  correspondsToRel ary (orEval ary func1 func2) (apLift ary (apLift ary (returnLift ary (fun p1 : Prop => fun p2 : Prop => p1 \/ p2)) P1) P2).
Proof with eauto. 
  assert ( claim1 :
    forall ary : arity,
    forall P1 : Lift ary Prop,
    forall P2 : Lift ary Prop,
    forall func1 : Lift ary w,
    forall func2 : Lift ary w,
    unLiftProp ary (bindLift ary (bindLift ary (returnLift ary (fun (p : Prop) (x : w) => (~ ~ p -> x = 0) /\ (~ p -> x = 1))) (fun f' : Prop -> w -> Prop => bindLift ary P1 (fun x' : Prop => returnLift ary (f' x')))) (fun f' : w -> Prop => bindLift ary func1 (fun x' : w => returnLift ary (f' x')))) ->
    unLiftProp ary (bindLift ary (bindLift ary (returnLift ary (fun (p : Prop) (x : w) => (~ ~ p -> x = 0) /\ (~ p -> x = 1))) (fun f' : Prop -> w -> Prop => bindLift ary P2 (fun x' : Prop => returnLift ary (f' x')))) (fun f' : w -> Prop => bindLift ary func2 (fun x' : w => returnLift ary (f' x')))) ->
    unLiftProp ary (apLift ary (apLift ary (returnLift ary (fun (p : Prop) (x : w) => (~ ~ p -> x = 0) /\ (~ p -> x = 1))) (bindLift ary (bindLift ary (returnLift ary (fun p1 p2 : Prop => p1 \/ p2)) (fun f' : Prop -> Prop -> Prop => bindLift ary P1 (fun x' : Prop => returnLift ary (f' x')))) (fun f' : Prop -> Prop => bindLift ary P2 (fun x' : Prop => returnLift ary (f' x'))))) (apLift ary (apLift ary (returnLift ary Init.Nat.mul) func1) func2))
  ).
  { induction ary.
    - unfold apLift.
      simpl.
      intros.
      constructor.
      + intros.
        assert (~ (func1 <> 0 /\ func2 <> 0)) by tauto.
        lia.
      + intros.
        assert (func1 = 1) by tauto.
        assert (func2 = 1) by tauto.
        lia.
    - unfold apLift.
      simpl...
  }
  unfold orEval.
  unfold correspondsToRel...
Qed.

Definition orArith (e1 : Arith) (e2 : Arith) : Arith :=
  multArith e1 e2
.

Lemma eval_orArith_orEval :
  forall e1 : Arith,
  forall e2 : Arith,
  forall ary : arity,
  forall func1 : Lift ary w,
  forall func2 : Lift ary w,
  evalArith ary e1 func1 ->
  evalArith ary e2 func2 ->
  evalArith ary (orArith e1 e2) (orEval ary func1 func2).
Proof with eauto.
  intros.
  unfold orArith.
  unfold orEval.
  apply multEval...
Qed.

Definition andEval (ary : arity) (func1 : Lift ary w) (func2 : Lift ary w) : Lift ary w :=
  notEval ary (orEval ary (notEval ary func1) (notEval ary func2))
.

Lemma andEval_correpondsTo_conjunction :
  forall ary : arity,
  forall P1 : Lift ary Prop,
  forall P2 : Lift ary Prop,
  forall func1 : Lift ary w,
  forall func2 : Lift ary w,
  correspondsToRel ary func1 P1 ->
  correspondsToRel ary func2 P2 ->
  correspondsToRel ary (andEval ary func1 func2) (apLift ary (apLift ary (returnLift ary (fun p1 : Prop => fun p2 : Prop => p1 /\ p2)) P1) P2).
Proof with eauto.
  unfold correspondsToRel.
  unfold andEval.
  intros.
  unfold apLift in H.
  unfold apLift in H0.
  generalize dependent ary.
  induction ary.
  - intros.
    assert (correspondsToRel 0 (notEval 0 (orEval 0 (notEval 0 func1) (notEval 0 func2))) (apLift 0 (apLift 0 (returnLift 0 (fun p1 p2 : Prop => ~ (~ p1 \/ ~ p2))) P1) P2)).
    { apply (notEval_correpondsTo_negation 0).
      apply (orEval_correspondsTo_disjunction 0).
      - apply (notEval_correpondsTo_negation 0)...
      - apply (notEval_correpondsTo_negation 0)...
    }
    unfold correspondsToRel in H1.
    unfold correspondsToRel.
    unfold apLift in *.
    simpl in *.
    tauto.
  - unfold orEval.
    unfold notEval.
    unfold apLift.
    simpl...
Qed.

Definition andArith (e1 : Arith) (e2 : Arith) : Arith :=
  notArith (orArith (notArith e1) (notArith e2))
.

Lemma eval_andArith_andEval :
  forall e1 : Arith,
  forall e2 : Arith,
  forall ary : arity,
  forall func1 : Lift ary w,
  forall func2 : Lift ary w,
  evalArith ary e1 func1 ->
  evalArith ary e2 func2 ->
  evalArith ary (andArith e1 e2) (andEval ary func1 func2).
Proof with eauto.
  intros.
  apply eval_notArith_notEval.
  apply eval_orArith_orEval.
  apply eval_notArith_notEval...
  apply eval_notArith_notEval...
Qed.

Definition eqEval (ary : arity) (func1 : Lift ary w) (func2 : Lift ary w) : Lift ary w :=
  andEval ary (notEval ary (apLift ary (apLift ary (returnLift ary chi_lt) func1) func2)) (notEval ary ((apLift ary (apLift ary (returnLift ary chi_lt) func2) func1)))
.

Lemma eqEval_correspondsTo_equality :
  forall ary : arity,
  forall val1 : Lift ary w,
  forall val2 : Lift ary w,
  forall func1 : Lift ary w,
  forall func2 : Lift ary w,
  correspondsToFunc ary func1 val1 ->
  correspondsToFunc ary func2 val2 ->
  correspondsToRel ary (eqEval ary func1 func2) (apLift ary (apLift ary (returnLift ary (fun x : w => fun y : w => x = y)) val1) val2).
Proof with eauto.
  unfold correspondsToFunc.
  unfold correspondsToRel.
  unfold eqEval.
  intros.
  unfold apLift in H.
  unfold apLift in H0.
  generalize dependent ary.
  induction ary.
  - intros.
    simpl.
    assert (correspondsToRel 0 (eqEval 0 func1 func2) (apLift 0 (apLift 0 (returnLift 0 (fun x1 : w => fun x2 : w => (~ (x1 < x2) /\ ~ (x2 < x1)))) val1) val2)).
    { unfold eqEval.
      apply (andEval_correpondsTo_conjunction 0).
      - apply (notEval_correpondsTo_negation 0)...
        unfold apLift.
        simpl.
        unfold chi_lt.
        unfold correspondsToFunc in *.
        unfold correspondsToRel.
        unfold apLift in *.
        simpl in *.
        destruct (Compare_dec.lt_dec func1 func2); lia.
      - apply (notEval_correpondsTo_negation 0)...
        unfold apLift.
        simpl.
        unfold chi_lt.
        unfold correspondsToFunc in *.
        unfold correspondsToRel.
        unfold apLift in *.
        simpl in *.
        destruct (Compare_dec.lt_dec func2 func1); lia.
    }
    unfold correspondsToRel in H1.
    unfold apLift in *.
    simpl in *...
    destruct H1.
    constructor.
    + intros.
      apply H1.
      lia.
    + intros.
      apply H2.
      lia.
  - unfold andEval.
    unfold notEval.
    unfold orEval.
    unfold apLift.
    simpl...
Qed.

End Arithmetic.

End Goedel's_Incompleteness_Theorem.
