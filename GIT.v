From Coq.Bool Require Export Bool.
From Coq.micromega Require Export Lia.
From Coq.Lists Require Export List.
From Coq.Arith Require Export PeanoNat.

Import ListNotations.

Section Chapter2.

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
      { subst; apply H.
      }
      { apply IHxs.
        - apply H0.
        - apply H1.
      }
    + intros H; constructor.
      { apply H; left; reflexivity.
      }
      { apply IHxs.
        intros x H0; apply H; right; apply H0.
      }
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
    + assert (fold_right max 0 ns >= n).
      { apply IHns.
        apply H.
      }
      lia.
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

Definition vr : Set :=
  nat
.
Inductive tm : Set :=
| ivar_tm : vr -> tm
| zero_tm : tm
| succ_tm : tm -> tm
| plus_tm : tm -> tm -> tm
| mult_tm : tm -> tm -> tm
| expo_tm : tm -> tm -> tm
.
Inductive form : Set :=
| eqn_form : tm -> tm -> form
| leq_form : tm -> tm -> form
| neg_form : form -> form
| imp_form : form -> form -> form
| all_form : vr -> form -> form
.

Lemma vr_eq_dec :
  forall x1 : vr,
  forall x2 : vr,
  {x1 = x2} + {x1 <> x2}.
Proof.
  apply Nat.eq_dec.
Qed.
Fixpoint occursFreeIn_tm (z : vr) (t : tm) : bool :=
  match t with
  | ivar_tm x => if vr_eq_dec z x then true else false
  | zero_tm => false
  | succ_tm t1 => occursFreeIn_tm z t1
  | plus_tm t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
  | mult_tm t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
  | expo_tm t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
  end
.
Fixpoint occursFreeIn_form (z : vr) (f : form) : bool :=
  match f with
  | eqn_form t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
  | leq_form t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
  | neg_form f1 => occursFreeIn_form z f1
  | imp_form f1 f2 => occursFreeIn_form z f1 || occursFreeIn_form z f2
  | all_form x f1 => if vr_eq_dec z x then false else occursFreeIn_form z f1
  end
.
Fixpoint getFreeVars_tm (t : tm) : list vr :=
  match t with
  | ivar_tm x => [x]
  | zero_tm => []
  | succ_tm t1 => getFreeVars_tm t1
  | plus_tm t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
  | mult_tm t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
  | expo_tm t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
  end
.
Theorem the_rule_of_getFreeVars_tm :
  forall t : tm,
  forall x : vr,
  In x (getFreeVars_tm t) <-> occursFreeIn_tm x t = true.
Proof.
  intros t; induction t.
  - intros vr; simpl; constructor.
    + intros H; destruct H.
      { subst.
        destruct (vr_eq_dec vr vr).
        - reflexivity.
        - contradiction.
      }
      { contradiction.
      }
    + intros H; destruct (vr_eq_dec vr v).
      { rewrite e; left; reflexivity.
      }
      { inversion H.
      }
  - intros vr; simpl; constructor.
    + tauto.
    + intros H; inversion H.
  - intros vr; simpl; apply IHt.
  - intros vr; simpl; rewrite orb_true_iff; rewrite in_app_iff; rewrite IHt1; rewrite IHt2; reflexivity.
  - intros vr; simpl; rewrite orb_true_iff; rewrite in_app_iff; rewrite IHt1; rewrite IHt2; reflexivity.
  - intros vr; simpl; rewrite orb_true_iff; rewrite in_app_iff; rewrite IHt1; rewrite IHt2; reflexivity.
Qed.
Fixpoint getFreeVars_form (f : form) : list vr :=
  match f with
  | eqn_form t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
  | leq_form t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
  | neg_form f1 => getFreeVars_form f1
  | imp_form f1 f2 => getFreeVars_form f1 ++ getFreeVars_form f2
  | all_form x f1 => remove vr_eq_dec x (getFreeVars_form f1)
  end
.
Theorem the_rule_of_getFreeVars_form :
  forall f : form,
  forall x : vr,
  In x (getFreeVars_form f) <-> occursFreeIn_form x f = true.
Proof.
  intros f; induction f.
  - intros vr; simpl; rewrite orb_true_iff; rewrite in_app_iff; rewrite the_rule_of_getFreeVars_tm; rewrite the_rule_of_getFreeVars_tm; reflexivity.
  - intros vr; simpl; rewrite orb_true_iff; rewrite in_app_iff; rewrite the_rule_of_getFreeVars_tm; rewrite the_rule_of_getFreeVars_tm; reflexivity.
  - intros vr; simpl; apply IHf.
  - intros vr; simpl; rewrite orb_true_iff; rewrite in_app_iff; rewrite IHf1; rewrite IHf2; reflexivity.
  - intros vr; simpl; constructor.
    + intros H.
      assert (In vr (getFreeVars_form f) /\ vr <> v).
      { apply (in_remove vr_eq_dec (getFreeVars_form f) vr v); apply H.
      }
      destruct H0 as [H0 H1]; destruct (vr_eq_dec vr v).
      { contradiction H1.
      }
      { apply IHf; apply H0.
      }
    + intros H; destruct (vr_eq_dec vr v).
      { inversion H.
      }
      { apply in_in_remove.
        - apply n.
        - apply IHf; apply H.
      }
Qed.

Definition value_assignment : Set :=
  vr -> nat
.
Fixpoint eval_tm (va : value_assignment) (t : tm) : nat :=
  match t with
  | ivar_tm x => va x
  | zero_tm => 0
  | succ_tm t1 => S (eval_tm va t1)
  | plus_tm t1 t2 => eval_tm va t1 + eval_tm va t2
  | mult_tm t1 t2 => eval_tm va t1 * eval_tm va t2
  | expo_tm t1 t2 => (eval_tm va t1)^(eval_tm va t2)
  end
.
Lemma eval_tm_extensionality :
  forall t : tm,
  forall va1 : value_assignment,
  forall va2 : value_assignment,
  (forall x : vr, occursFreeIn_tm x t = true -> va1 x = va2 x) ->
  eval_tm va1 t = eval_tm va2 t.
Proof.
  intros t; induction t.
  - simpl; intros va1 va2 H; apply H; destruct (vr_eq_dec v v).
    { reflexivity.
    }
    { contradiction.
    }
  - simpl; intros va1 va2 H.
    reflexivity.
  - simpl; intros va1 va2 H.
    rewrite (IHt va1 va2).
    reflexivity.
    apply H.
  - simpl; intros va1 va2 H.
    rewrite (IHt1 va1 va2).
    rewrite (IHt2 va1 va2).
    reflexivity.
    intros x H0; apply H; apply orb_true_iff; tauto.
    intros x H0; apply H; apply orb_true_iff; tauto.
  - simpl; intros va1 va2 H.
    rewrite (IHt1 va1 va2).
    rewrite (IHt2 va1 va2).
    reflexivity.
    intros x H0; apply H; apply orb_true_iff; tauto.
    intros x H0; apply H; apply orb_true_iff; tauto.
  - simpl; intros va1 va2 H.
    rewrite (IHt1 va1 va2).
    rewrite (IHt2 va1 va2).
    reflexivity.
    intros x H0; apply H; apply orb_true_iff; tauto.
    intros x H0; apply H; apply orb_true_iff; tauto.
Qed.
Fixpoint eval_form (va : value_assignment) (f : form) : Prop :=
  match f with
  | eqn_form t1 t2 => eval_tm va t1 = eval_tm va t2
  | leq_form t1 t2 => eval_tm va t1 <= eval_tm va t2
  | neg_form f1 => ~ eval_form va f1
  | imp_form f1 f2 => eval_form va f1 -> eval_form va f2
  | all_form x f1 => forall n : nat, eval_form (fun z : vr => if vr_eq_dec x z then n else va z) f1
  end
.
Lemma eval_form_extensionality :
  forall f : form,
  forall va1 : value_assignment,
  forall va2 : value_assignment,
  (forall x : vr, occursFreeIn_form x f = true -> va1 x = va2 x) ->
  eval_form va1 f <-> eval_form va2 f.
Proof.
  intros f; induction f.
  - simpl; intros va1 va2 H.
    rewrite (eval_tm_extensionality t va1 va2).
    rewrite (eval_tm_extensionality t0 va1 va2).
    reflexivity.
    intros x H0; apply H; apply orb_true_iff; tauto.
    intros x H0; apply H; apply orb_true_iff; tauto.
  - simpl; intros va1 va2 H.
    rewrite (eval_tm_extensionality t va1 va2).
    rewrite (eval_tm_extensionality t0 va1 va2).
    reflexivity.
    intros x H0; apply H; apply orb_true_iff; tauto.
    intros x H0; apply H; apply orb_true_iff; tauto.
  - simpl; intros va1 va2 H.
    rewrite (IHf va1 va2).
    reflexivity.
    intros x H0; apply H; tauto.
  - simpl; intros va1 va2 H.
    rewrite (IHf1 va1 va2).
    rewrite (IHf2 va1 va2).
    reflexivity.
    intros x H0; apply H; apply orb_true_iff; tauto.
    intros x H0; apply H; apply orb_true_iff; tauto.
  - simpl; intros va1 va2 H.
    cut (
      forall n : nat,
      eval_form (fun z : vr => if vr_eq_dec v z then n else va1 z) f <->  eval_form (fun z : vr => if vr_eq_dec v z then n else va2 z) f
    ).
    { constructor.
      - intros H1 n; apply H0; apply H1.
      - intros H1 n; apply H0; apply H1.
    }
    intros n.
    rewrite (IHf (fun z : vr => if vr_eq_dec v z then n else va1 z) (fun z : vr => if vr_eq_dec v z then n else va2 z)).
    reflexivity.
    intros x H0; destruct (vr_eq_dec v x).
    { reflexivity.
    }
    { apply H.
      destruct (vr_eq_dec x v).
      - contradiction n0; rewrite e; reflexivity.
      - apply H0.
    }
Qed.
Fixpoint make_numeral (n : nat) : tm :=
  match n with
  | 0 => zero_tm
  | S n => succ_tm (make_numeral n)
  end
.
Lemma eval_tm_make_numeral :
  forall n : nat,
  forall va : value_assignment,
  eval_tm va (make_numeral n) = n.
Proof.
  intros n; induction n.
  - simpl; intros va; reflexivity.
  - simpl; intros va; rewrite IHn; reflexivity.
Qed.

Definition substitution : Set :=
  list (vr * tm)
.
Fixpoint substitute_vr (sigma : substitution) (x : vr) : tm :=
  match sigma with
  | [] => ivar_tm x
  | (x1, tm1) :: sigma' =>
    if vr_eq_dec x x1
    then tm1
    else substitute_vr sigma' x
  end
.
Fixpoint substitute_tm (sigma : substitution) (t : tm) : tm :=
  match t with
  | ivar_tm x => substitute_vr sigma x
  | zero_tm => zero_tm
  | succ_tm t1 => succ_tm (substitute_tm sigma t1)
  | plus_tm t1 t2 => plus_tm (substitute_tm sigma t1) (substitute_tm sigma t2)
  | mult_tm t1 t2 => mult_tm (substitute_tm sigma t1) (substitute_tm sigma t2)
  | expo_tm t1 t2 => expo_tm (substitute_tm sigma t1) (substitute_tm sigma t2)
  end
.
Theorem substitute_tm_preserves_eval_tm :
  forall t : tm,
  forall sigma : substitution,
  forall va : value_assignment,
  eval_tm (fun z : vr => eval_tm va (substitute_vr sigma z)) t = eval_tm va (substitute_tm sigma t).
Proof.
  intros t; induction t.
  - intros sigma va; simpl; reflexivity.
  - intros sigma va; simpl; reflexivity.
  - intros sigma va; simpl; rewrite IHt; reflexivity.
  - intros sigma va; simpl; rewrite IHt1; rewrite IHt2; reflexivity.
  - intros sigma va; simpl; rewrite IHt1; rewrite IHt2; reflexivity.
  - intros sigma va; simpl; rewrite IHt1; rewrite IHt2; reflexivity.
Qed.
Definition getMaxNumOfFreeVars_tm (t : tm) : vr :=
  fold_right_max_0 (getFreeVars_tm t)
.
Lemma getMaxNumOfFreeVars_tm_lt :
  forall t : tm,
  forall x : vr,
  getMaxNumOfFreeVars_tm t < x ->
  occursFreeIn_tm x t = false.
Proof.
  unfold getMaxNumOfFreeVars_tm; intros t; induction t.
  - simpl; intros x H; destruct (vr_eq_dec x v).
    + lia.
    + reflexivity.
  - simpl; intros x H; tauto.
  - simpl; intros x H; apply IHt; apply H.
  - simpl; intros x H; apply orb_false_iff; rewrite fold_right_max_0_app in H; constructor.
    + apply IHt1; lia.
    + apply IHt2; lia.
  - simpl; intros x H; apply orb_false_iff; rewrite fold_right_max_0_app in H; constructor.
    + apply IHt1; lia.
    + apply IHt2; lia.
  - simpl; intros x H; apply orb_false_iff; rewrite fold_right_max_0_app in H; constructor.
    + apply IHt1; lia.
    + apply IHt2; lia.
Qed.
Definition isFreshVarIn_substitute_tm (sigma : substitution) (z : vr) (t : tm) : Prop :=
  forallb (fun x : vr => negb (occursFreeIn_tm z (substitute_vr sigma x))) (getFreeVars_tm t) = true
.
Definition isFreshVarIn_substitute_form (sigma : substitution) (z : vr) (f : form) : Prop :=
  forallb (fun x : vr => negb (occursFreeIn_tm z (substitute_vr sigma x))) (getFreeVars_form f) = true
.
Definition chi (sigma : substitution) (f : form) : vr :=
  S (fold_right_max_0 (map (fun x : vr => getMaxNumOfFreeVars_tm (substitute_vr sigma x)) (getFreeVars_form f)))
.
Theorem the_rule_of_chi :
  forall f : form,
  forall sigma : substitution,
  isFreshVarIn_substitute_form sigma (chi sigma f) f.
Proof.
  assert ( claim1 :
    forall sigma : substitution,
    forall f : form,
    forall x : vr,
    occursFreeIn_form x f = true ->
    occursFreeIn_tm (chi sigma f) (substitute_vr sigma x) = false
  ).
  { intros sigma f x H.
    assert (getMaxNumOfFreeVars_tm (substitute_vr sigma x) < chi sigma f).
    { unfold chi; unfold fold_right_max_0.
      cut (fold_right max 0 (map (fun z : vr => getMaxNumOfFreeVars_tm (substitute_vr sigma z)) (getFreeVars_form f)) >= getMaxNumOfFreeVars_tm (substitute_vr sigma x)).
      { lia.
      }
      rewrite <- the_rule_of_getFreeVars_form in H.
      apply fold_right_max_0_in; apply in_map_iff.
      exists x; constructor.
      - reflexivity.
      - apply H.
    }
    apply getMaxNumOfFreeVars_tm_lt; apply H0.
  }
  unfold isFreshVarIn_substitute_form; intros f sigma; apply forallb_true_iff.
  intros x H; apply negb_true_iff; apply claim1; apply the_rule_of_getFreeVars_form; apply H.
Qed.
Fixpoint substitute_form (sigma : substitution) (f : form) : form :=
  match f with
  | eqn_form t1 t2 => eqn_form (substitute_tm sigma t1) (substitute_tm sigma t2)
  | leq_form t1 t2 => leq_form (substitute_tm sigma t1) (substitute_tm sigma t2)
  | neg_form f1 => neg_form (substitute_form sigma f1)
  | imp_form f1 f2 => imp_form (substitute_form sigma f1) (substitute_form sigma f2)
  | all_form x f1 =>
    let z : vr := chi sigma f in
    all_form z (substitute_form ((x, ivar_tm z) :: sigma) f1)
  end
.
Theorem substitute_form_preserves_eval_form :
  forall f : form,
  forall sigma : substitution,
  forall va : value_assignment,
  eval_form (fun z : vr => eval_tm va (substitute_vr sigma z)) f <-> eval_form va (substitute_form sigma f).
Proof.
  intros f; induction f.
  - intros sigma va; simpl.
    rewrite substitute_tm_preserves_eval_tm; rewrite substitute_tm_preserves_eval_tm; reflexivity.
  - intros sigma va; simpl.
    rewrite substitute_tm_preserves_eval_tm; rewrite substitute_tm_preserves_eval_tm; reflexivity.
  - intros sigma va; simpl.
    rewrite IHf; reflexivity.
  - intros sigma va; simpl.
    rewrite IHf1; rewrite IHf2; reflexivity.
  - intros sigma va. simpl.
    cut (
      forall n : nat,
      eval_form (fun z : vr => if vr_eq_dec v z then n else eval_tm va (substitute_vr sigma z)) f <-> eval_form (fun z : vr => if vr_eq_dec (chi sigma (all_form v f)) z then n else va z) (substitute_form ((v, ivar_tm (chi sigma (all_form v f))) :: sigma) f)
    ).
    { intros H; constructor.
      - intros H0 n; apply H; apply H0.
      - intros H0 n; apply H; apply H0.
    }
    intros n; rewrite <- (IHf ((v, ivar_tm (chi sigma (all_form v f))) :: sigma) (fun z : vr => if vr_eq_dec (chi sigma (all_form v f)) z then n else va z)); apply eval_form_extensionality.
    intros x H; simpl; destruct (vr_eq_dec v x).
    { destruct (vr_eq_dec x v).
      - simpl; destruct (vr_eq_dec (chi sigma (all_form v f)) (chi sigma (all_form v f))).
        + reflexivity.
        + contradiction.
      - contradiction n0; rewrite e; reflexivity.
    }
    { destruct (vr_eq_dec x v).
      - contradiction n0; rewrite e; reflexivity.
      - apply eval_tm_extensionality.
        intros x' H0; destruct (vr_eq_dec (chi sigma (all_form v f)) x').
        { subst.
          assert (isFreshVarIn_substitute_form sigma (chi sigma (all_form v f)) (all_form v f)).
            apply the_rule_of_chi.
          unfold isFreshVarIn_substitute_form in H1; rewrite forallb_true_iff in H1.
          assert (negb (occursFreeIn_tm (chi sigma (all_form v f)) (substitute_vr sigma x)) = true).
          { apply H1; apply the_rule_of_getFreeVars_form; simpl; destruct (vr_eq_dec x v).
            - contradiction.
            - tauto. 
          }
          rewrite H0 in H2; inversion H2.
        }
        { reflexivity.
        }
    }
Qed.

End Chapter2.
