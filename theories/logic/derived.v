From iris.bi Require Export bi updates.
From iris_ora.logic Require Export oupred.
Import bi.bi logic.oupred.ouPred.
From iris.prelude Require Import options.

(** Derived laws for Iris-specific primitive connectives (own, valid).
    This file does NOT unseal! *)

Infix "~~>" := (cmra_update(A := ora_cmraR _)) (at level 70).

Module ouPred.
Section derived.
Context {M : uora}.
Implicit Types φ : Prop.
Implicit Types P Q : ouPred M.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=ouPredI M) P Q).
Notation "P ⊣⊢ Q" := (equiv (A:=ouPredI M) P%I Q%I).

(** Propers *)
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@ouPred_ownM M) := ne_proper _.

(** Own and valid derived *)
Global Instance ownM_mono : Proper (flip (≼ₒ) ==> (⊢)) (@ouPred_ownM M).
Proof. by intros ???; apply ownM_order. Qed.
Global Instance ownM_unit_affine : Affine(PROP:=ouPredI M) (ouPred_ownM ε).
Proof. apply ownM_unit_discard. Qed.
Global Instance ownM_increasing_affine a {H : Increasing a} : Affine (PROP:=ouPredI M) (ouPred_ownM a).
Proof. apply uora_unit_order_increasing in H. rewrite /Affine ownM_mono //. apply ownM_unit_discard. Qed.
Global Instance ownM_core_affine a : Affine (PROP:=ouPredI M) (ouPred_ownM (core a)).
Proof. apply ownM_core_discard. Qed.
Lemma intuitionistically_ownM (a : M) : OraCoreId a → ouPred_ownM a ⊢ □ ouPred_ownM a.
Proof. intros; rewrite /bi_intuitionistically -{1}(oracore_id_core a) -{1}(affine_affinely (ouPred_ownM (core a))).
  rewrite oracore_id_core -{2}(oracore_id_core a).
  apply affinely_mono, persistently_ownM_core.
Qed.
Lemma ownM_invalid (a : M) : ¬ ✓{0} a → ouPred_ownM a ⊢ False.
Proof.
  intros. rewrite ownM_valid internal_cmra_valid_elim. by apply pure_elim'.
Qed.

Lemma ownM_unit' : ouPred_ownM ε ⊣⊢ emp.
Proof. apply (anti_symm _); [apply ownM_unit_discard | apply ownM_unit]. Qed.
Instance absorbing_valid {A : ora} (a : A) : Absorbing(PROP:=ouPredI M) (✓ a).
Proof.
  rewrite /Absorbing /bi_absorbingly /internal_cmra_valid.
  unseal; siProp_primitive.unseal.
  constructor.
  intros ??? (? & ? & ? & ? & ?); auto.
Qed.

Lemma bupd_ownM_update (x y : M) : x ~~> y → ouPred_ownM x ⊢ |==> ouPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (y =.)); last by apply @cmra_update_updateP.
  by apply ouPred.bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.

(** Timeless instances *)
Global Instance ownM_timeless (a : M) : Discrete a → Timeless (ouPred_ownM a).
Proof.
  intros ?. rewrite /Timeless later_ownM. apply exist_elim=> b.
  rewrite (timeless (a≡b)) (except_0_intro (ouPred_ownM b)) -except_0_and.
  apply except_0_mono. rewrite internal_eq_sym.
  apply (internal_eq_rewrite' b a (ouPred_ownM) _);
    [solve_proper|auto using and_elim_l, and_elim_r..].
Qed.
Global Instance emp_timeless : Timeless (emp : ouPred M)%I.
Proof.
  rewrite /Timeless later_mono; last apply ownM_unit.
  rewrite ownM_timeless ownM_unit_discard //.
Qed.

(** Persistence *)
Global Instance ownM_persistent a : OraCoreId a → Persistent (@ouPred_ownM M a).
Proof.
  intros. rewrite /Persistent -{2}(oracore_id_core a). apply persistently_ownM_core.
Qed.

(** For big ops *)
Global Instance ouPred_ownM_sep_homomorphism :
  MonoidHomomorphism op ouPred_sep (≡) (@ouPred_ownM M).
Proof. split; [split|]; try apply _; [apply ownM_op | apply ownM_unit']. Qed.

(** Consistency/soundness statement *)
Lemma uora_unit_refl (A : uora) n : (ε : A) ≼ₒ{n} ε.
Proof.
  rewrite -{2}(oracore_id_core ε); apply ora_order_orderN, uora_unit_order_core.
Qed.

(** Soundness statement for our modalities: facts derived under modalities in
  the empty context also without the modalities.
  For basic updates, soundness only holds for plain propositions. *)
  Lemma bupd_soundness P `{!Plain P} `{!Absorbing P} : (⊢ |==> P) → ⊢ P.
  Proof. rewrite bupd_elim. done. Qed.

  (** As pure demonstration, we also show that this holds for an arbitrary nesting
  of modalities. We have to do a bit of work to be able to state this theorem
  though. *)
  Inductive modality := MBUpd | MLater | MPersistently | MPlainly.
  Definition denote_modality (m : modality) : ouPred M → ouPred M :=
    match m with
    | MBUpd => bupd
    | MLater => bi_later
    | MPersistently => bi_persistently
    | MPlainly => plainly
    end.
  Definition denote_modalities (ms : list modality) : ouPred M → ouPred M :=
    λ P, foldr denote_modality P ms.

  (** Now we can state and prove 'soundness under arbitrary modalities' for plain
  propositions. This is probably not a lemma you want to actually use. *)
  Corollary modal_soundness P `{!Plain P} `{!Absorbing P} (ms : list modality) :
    (⊢ denote_modalities ms P) → ⊢ P.
  Proof.
    intros H. apply (laterN_soundness _ (length ms)).
    move: H. apply bi_emp_valid_mono.
    induction ms as [|m ms IH]; first done; simpl.
    destruct m; simpl; rewrite IH.
    - rewrite -later_intro. apply: bupd_elim.
    - done.
    - rewrite -later_intro persistently_elim. done.
    - rewrite -later_intro plainly_elim. done.
  Qed.

  (** Consistency: one cannot deive [False] in the logic, not even under
  modalities. Again this is just for demonstration and probably not practically
  useful. *)
  Corollary consistency : ¬ ⊢@{ouPredI M} False.
  Proof. apply: pure_soundness. Qed.
End derived.
End ouPred.
