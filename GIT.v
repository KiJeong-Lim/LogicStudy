From Coq.Bool Require Export Bool.
From Coq.micromega Require Export Lia.
From Coq.Lists Require Export List.
From Coq.Arith Require Export PeanoNat.

Module Smullyan's_Goedel's_Incompleteness_Theorems.

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

Lemma forallb_true_iff {A : Type} (f : A -> bool) :
  forall xs : list A,
  forallb f xs = true <-> (forall x : A, In x xs -> f x = true).
Proof.
  intros xs; induction xs as [| x' xs].
  - simpl; constructor.
    + intros H x H0; contradiction.
    + tauto.
  - simpl; rewrite andb_true_iff; constructor.
    + intros H; destruct H as [H H0]; intros x H1; destruct H1.
      * subst; apply H.
      * apply IHxs.
        apply H0.
        apply H1.
    + intros H; constructor.
      * apply H; left; reflexivity.
      * apply IHxs.
        intros x H0; apply H; right; apply H0.
Qed.

Definition fold_right_max_0 : list nat -> nat :=
  fold_right max 0
.

Lemma fold_right_max_0_in :
  forall ns : list nat,
  forall n : nat,
  In n ns ->
  fold_right_max_0 ns >= n.
Proof.
  unfold fold_right_max_0; intros ns; induction ns as [| n' ns].
  - simpl; lia.
  - simpl; intros n H; destruct H.
    + lia.
    + assert (fold_right max 0 ns >= n) by (apply IHns; apply H); lia.
Qed.

Lemma fold_right_max_0_app :
  forall ns1 : list nat,
  forall ns2 : list nat,
  fold_right_max_0 (ns1 ++ ns2) = max (fold_right_max_0 ns1) (fold_right_max_0 ns2).
Proof.
  unfold fold_right_max_0; intros ns1; induction ns1 as [|n1 ns1].
  - simpl; intros n; lia.
  - simpl; intros n; rewrite IHns1; lia.
Qed.

Definition ensemble (A : Type) : Type :=
  A -> Prop
.

Definition member {A : Type} (x : A) (xs : ensemble A) : Prop :=
  xs x
.

Inductive empty {A : Type} : ensemble A :=
.

Inductive singletone {A : Type} : A -> ensemble A :=
| In_singletone :
  forall x : A,
  forall xs : ensemble A,
  member x (singletone x)
.

Inductive union {A : Type} : ensemble A -> ensemble A -> ensemble A :=
| In_union_left :
  forall x : A,
  forall xs1 : ensemble A,
  forall xs2 : ensemble A,
  member x xs1 ->
  member x (union xs1 xs2)
| In_union_right :
  forall x : A,
  forall xs1 : ensemble A,
  forall xs2 : ensemble A,
  member x xs2 ->
  member x (union xs1 xs2)
.

Definition insert {A : Type} (x1 : A) (xs2 : ensemble A) : ensemble A :=
  union xs2 (singletone x1)
.

Definition intersection {A : Type} (xs1 : ensemble A) (xs2 : ensemble A) : ensemble A :=
  fun x : A => member x xs1 /\ member x xs2
.

Definition completement {A : Type} (xs1 : ensemble A) : ensemble A :=
  fun x : A => ~ member x  xs1
.

Definition difference {A : Type} (xs1 : ensemble A) (xs2 : ensemble A) : ensemble A :=
  intersection xs1 (completement xs2)
.

Definition delete {A : Type} (x1 : A) (xs2 : ensemble A) : ensemble A :=
  difference xs2 (singletone x1)
.

Definition isSubsetOf {A : Type} (xs1 : ensemble A) (xs2 : ensemble A) : Prop :=
  forall x : A, member x xs1 -> member x xs2
.

Lemma isSubsetOf_refl {A : Type} :
  forall xs1 : ensemble A,
  isSubsetOf xs1 xs1.
Proof.
  unfold isSubsetOf; intros xs1 x H; apply H.
Qed.

Lemma isSubsetOf_trans {A : Type} :
  forall xs1 : ensemble A,
  forall xs2 : ensemble A,
  forall xs3 : ensemble A,
  isSubsetOf xs1 xs2 ->
  isSubsetOf xs2 xs3 ->
  isSubsetOf xs1 xs3.
Proof.
  unfold isSubsetOf; intros xs1 xs2 xs3 H1 H2; apply (fun x : A => fun H0 : member x xs1 => H2 x (H1 x H0)).
Qed.

End Preliminaries.

Section Chapter1.

Class GoedelianLanguage (mathcalE : Type) : Type :=
  { enum_mathcalE : nat -> mathcalE
  ; mathcalE_is_denumerable : forall E : mathcalE, {n : nat | enum_mathcalE n = E}
  ; isSentence : ensemble mathcalE
  ; isProvable : ensemble mathcalE
  ; isRefutable : ensemble mathcalE
  ; isPredicate : ensemble mathcalE
  ; apply_nat : mathcalE -> nat -> mathcalE
  ; isTrue : ensemble mathcalE
  ; onlyProvableIsSentence : isSubsetOf isProvable isSentence
  ; onlyRefutableIsSentence : isSubsetOf isRefutable isSentence
  ; apply_natForPredicate : forall h : mathcalE, isPredicate h -> forall n : nat, isSentence (apply_nat h n)
  ; onlyTrueIsSentence : isSubsetOf isTrue isSentence
  }
.

Definition diagonalizer (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : nat -> nat :=
  fun n : nat => proj1_sig (mathcalE_is_denumerable (apply_nat (enum_mathcalE n) n))
.

Lemma diagonalizer_diagonalizes (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} :
  forall n : nat,
  forall E : mathcalE,
  enum_mathcalE n = E ->
  enum_mathcalE (diagonalizer mathcalE n) = apply_nat E n.
Proof.
  intros n E H; unfold diagonalizer; subst; destruct (mathcalE_is_denumerable (apply_nat (enum_mathcalE n) n)) as [d_n]; simpl; tauto.
Qed.

Definition expressPredicate (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : mathcalE -> ensemble nat -> Prop :=
  fun H : mathcalE => fun A : ensemble nat => forall n : nat, isTrue (apply_nat H n) <-> member n A
.

Definition is_expressible (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : ensemble nat -> Prop :=
  fun A : ensemble nat => exists H : mathcalE, expressPredicate mathcalE H A
.

Inductive StarOf (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : ensemble nat -> ensemble nat :=
| InStarOf :
  forall ns : ensemble nat,
  forall n : nat,
  member (diagonalizer mathcalE n) ns ->
  member n (StarOf mathcalE ns)
.

Definition isCorrect (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : Prop :=
  isSubsetOf isProvable isTrue /\ isSubsetOf (intersection isRefutable isTrue) empty
.

Inductive P (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : ensemble nat :=
| InP :
  forall n : nat,
  isProvable (enum_mathcalE n) ->
  member n (P mathcalE)
.

Theorem After_Goedel_with_shades_of_Tarski (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} :
  isCorrect mathcalE ->
  is_expressible mathcalE (StarOf mathcalE (completement (P mathcalE))) ->
  exists E : mathcalE, isTrue E /\ ~ isProvable E.
Proof.
  intros mathcalE_is_correct StarOf_complement_P_is_expressible.
  destruct StarOf_complement_P_is_expressible as [H H_express_StarOf_complement_P].
  destruct (mathcalE_is_denumerable H) as [n n_is_the_goedel_number_of_H].
  assert (diagonalization_of_n_is_true_iff_n_is_in_StarOf_complement_of_P : isTrue (enum_mathcalE (diagonalizer mathcalE n)) <-> member n (StarOf mathcalE (completement (P mathcalE)))).
  { unfold expressPredicate in H_express_StarOf_complement_P.
    rewrite (diagonalizer_diagonalizes mathcalE n H n_is_the_goedel_number_of_H).
    apply H_express_StarOf_complement_P.
  }
  assert (n_in_StarOf_complement_of_P_iff_diagonalization_of_n_is_not_Provable : member n (StarOf mathcalE (completement (P mathcalE))) <-> ~ isProvable (enum_mathcalE (diagonalizer mathcalE n))).
  { constructor.
    - intros n_in_StarOf_complement_of_P diagonalization_of_n_is_not_Provable.
      inversion n_in_StarOf_complement_of_P as [A n' diagonalization_of_n_is_in_A A_is_complement_of_P n_is_n']; subst n'; contradiction diagonalization_of_n_is_in_A.
      apply InP; apply diagonalization_of_n_is_not_Provable.
    - intros diagonalization_of_n_is_not_Provable; apply InStarOf.
      intros diagonalization_of_n_is_in_P; contradiction diagonalization_of_n_is_not_Provable.
      inversion diagonalization_of_n_is_in_P as [n' diagonalization_of_n_is_Provable n_is_n']; subst n'; apply diagonalization_of_n_is_Provable.
  }
  assert (diagonalization_of_n_is_not_Provable : ~ isProvable (enum_mathcalE (diagonalizer mathcalE n))).
  { intros diagonalization_of_n_is_Provable.
    destruct mathcalE_is_correct as [Provable_implies_true Refutable_implies_false].
    assert (diagonalization_of_n_is_True : isTrue (enum_mathcalE (diagonalizer mathcalE n))) by (apply Provable_implies_true; apply diagonalization_of_n_is_Provable).
    tauto.
  }
  exists (enum_mathcalE (diagonalizer mathcalE n)).
  tauto.
Qed.

Definition the_first_goal (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : Prop :=
  forall A : ensemble nat, is_expressible mathcalE A -> is_expressible mathcalE (StarOf mathcalE A)
.

Definition the_second_goal (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : Prop :=
  forall A : ensemble nat, is_expressible mathcalE A -> is_expressible mathcalE (completement A)
.

Definition the_third_goal (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : Prop :=
  is_expressible mathcalE (P mathcalE)
.

Definition isGoedelSentence (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : mathcalE -> ensemble nat -> Prop :=
  fun E : mathcalE => fun A : ensemble nat => exists n : nat, enum_mathcalE n = E /\ (isTrue E <-> member n A)
.

Lemma A_Diagonal_Lemma_a (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} :
  forall A : ensemble nat,
  is_expressible mathcalE (StarOf mathcalE A) ->
  exists E : mathcalE, isGoedelSentence mathcalE E A.
Proof.
  intros A StarOf_A_is_expressible; destruct StarOf_A_is_expressible as [H H_express_StarOf_A]; destruct (mathcalE_is_denumerable H) as [n g_H_is_n]; exists (apply_nat H n).
  assert (isTrue (apply_nat H n) <-> member (diagonalizer mathcalE n) A).
  { constructor.
    - intros H_n_is_true; assert (n_is_in_StarOfA : member n (StarOf mathcalE A)) by (apply H_express_StarOf_A; apply H_n_is_true).
      inversion n_is_in_StarOfA as [A' n' d_n_is_in_A A_is_A' n_is_n']; subst; apply d_n_is_in_A.
    - intros d_n_is_in_A; apply H_express_StarOf_A; constructor; apply d_n_is_in_A.
  }
  assert (enum_mathcalE (diagonalizer mathcalE n) = apply_nat H n).
  { unfold diagonalizer; rewrite (proj2_sig (mathcalE_is_denumerable (apply_nat (enum_mathcalE n) n))).
    rewrite g_H_is_n; reflexivity.
  }
  exists (diagonalizer mathcalE n); tauto.
Qed.

Lemma A_Diagonal_Lemma_b (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} :
  the_first_goal mathcalE ->
  forall A : ensemble nat,
  is_expressible mathcalE A ->
  exists E : mathcalE, isGoedelSentence mathcalE E A.
Proof.
  intros the_first_goal_holds A A_is_expressible; apply A_Diagonal_Lemma_a; apply the_first_goal_holds; apply A_is_expressible.
Qed.

Inductive T (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} : ensemble nat :=
| InT :
  forall n : nat,
  isTrue (enum_mathcalE n) ->
  member n (T mathcalE)
.

Theorem there_is_no_GoedelSentence_of_complement_of_T (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} :
  ~ exists E : mathcalE, isGoedelSentence mathcalE E (completement (T mathcalE)).
Proof.
  intros there_is_GoedelSentence_of_complement_of_T.
  destruct there_is_GoedelSentence_of_complement_of_T as [E E_is_GoedelSentence_of_complement_of_T].
  destruct E_is_GoedelSentence_of_complement_of_T as [n n_is_g_E_and_E_is_true_iff_n_is_in_complement_T].
  destruct n_is_g_E_and_E_is_true_iff_n_is_in_complement_T as [n_is_g_E E_is_true_iff_n_is_in_complement_T].
  assert (E_is_true_iff_n_is_not_in_T : isTrue E <-> ~ member n (T mathcalE)) by (rewrite E_is_true_iff_n_is_in_complement_T; unfold completement; unfold member; reflexivity).
  assert (E_is_true_iff_n_is_in_T : isTrue E <-> member n (T mathcalE)).
  { constructor.
    - intros E_is_true; constructor; rewrite n_is_g_E; apply E_is_true.
    - intros n_is_inT; inversion n_is_inT as [n' E_is_true n_is_n']; subst n'; rewrite <- n_is_g_E; apply E_is_true.
  }
  tauto.
Qed.

Theorem After_Tarski_1 (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} :
  ~ is_expressible mathcalE (StarOf mathcalE (completement (T mathcalE))).
Proof.
  intros StarOf_T_is_expressible.
  destruct (A_Diagonal_Lemma_a mathcalE (completement (T mathcalE)) StarOf_T_is_expressible) as [H H_is_GoedelSentence_for_complement_of_T].
  contradiction (there_is_no_GoedelSentence_of_complement_of_T mathcalE).
  exists H; apply H_is_GoedelSentence_for_complement_of_T.
Qed.

Theorem After_Tarski_2 (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} :
  the_first_goal mathcalE ->
  ~ is_expressible mathcalE (completement (T mathcalE)).
Proof.
  intros the_first_goal_holds completement_of_T_is_expressible.
  apply (After_Tarski_1 mathcalE); apply the_first_goal_holds; apply completement_of_T_is_expressible.
Qed.

Theorem After_Tarski_3 (mathcalE : Type) `{mathcalE_is_goedelian : GoedelianLanguage mathcalE} :
  the_first_goal mathcalE ->
  the_second_goal mathcalE ->
  ~ is_expressible mathcalE (T mathcalE).
Proof.
  intros the_first_goal_holds the_second_goal_holds T_is_expressible.
  apply (After_Tarski_2 mathcalE the_first_goal_holds); apply the_second_goal_holds; apply T_is_expressible.
Qed.

End Chapter1.

Section Chapter2.

End Chapter2.

End Smullyan's_Goedel's_Incompleteness_Theorems.
