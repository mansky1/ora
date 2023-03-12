From iris.bi Require Export bi.
From iris_ora.logic Require Export oupred.
From iris.prelude Require Import options.
Import bi.bi logic.oupred.ouPred.

(** Derived laws for Iris-specific primitive connectives (own, valid).
    This file does NOT unseal! *)

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
Global Instance ora_valid_proper {A : ora} :
  Proper ((≡) ==> (⊣⊢)) (@ouPred_ora_valid M A) := ne_proper _.

(** Own and valid derived *)
Lemma persistently_ora_valid_1 {A : ora} (a : A) : ✓ a ⊢@{ouPredI M} <pers> (✓ a).
Proof. by rewrite {1}plainly_ora_valid_1 plainly_elim_persistently. Qed.
(*Lemma intuitionistically_ownM (a : M) : OraCoreId a → □ ouPred_ownM a ⊣⊢ ouPred_ownM a.
Proof.
  rewrite /bi_intuitionistically affine_affinely=>?; apply (anti_symm _);
    [by rewrite persistently_elim|].
  by rewrite {1}persistently_ownM_core core_id_core.
Qed.*)
Lemma ownM_invalid (a : M) : ¬ ✓{0} a → ouPred_ownM a ⊢ False.
Proof. by intros; rewrite ownM_valid ora_valid_elim. Qed.
Global Instance ownM_mono : Proper (flip (≼ₒ) ==> (⊢)) (@ouPred_ownM M).
Proof. by intros ???; apply ownM_order. Qed.
Lemma ownM_unit' : ouPred_ownM ε ⊣⊢ emp.
Proof. apply (anti_symm _); [apply ownM_unit_discard | apply ownM_unit]. Qed.
Global Instance ownM_unit_affine : Affine(PROP:=ouPredI M) (ouPred_ownM ε).
Proof. apply ownM_unit_discard. Qed.
Instance absorbing_valid {A : ora} (a : A) : Absorbing(PROP:=ouPredI M) (✓ a).
Proof.
  rewrite /Absorbing /bi_absorbingly.
  unseal.
  constructor.
  intros ??? (? & ? & ? & ? & ?); auto.
Qed.
Lemma plainly_ora_valid {A : ora} (a : A) : ■ ✓ a ⊣⊢ ✓ a.
Proof. apply (anti_symm _), plainly_ora_valid_1. apply plainly_elim, _. Qed.
(*Lemma intuitionistically_ora_valid {A : ora} (a : A) : □ ✓ a ⊣⊢ ✓ a.
Proof.
  rewrite /bi_intuitionistically affine_affinely. intros; apply (anti_symm _);
    first by rewrite persistently_elim.
  apply:persistently_ora_valid_1.
Qed.*)
(*Lemma bupd_ownM_update x y : x ~~> y → ouPred_ownM x ⊢ |==> ouPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (y =.)); last by apply ora_update_updateP.
  by apply bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.*)

(** Timeless instances *)
Global Instance valid_timeless {A : ora} `{!OraDiscrete A} (a : A) :
  Timeless (✓ a : ouPred M)%I.
Proof. rewrite /Timeless !discrete_valid. apply (timeless _). Qed.
Global Instance ownM_timeless (a : M) : Discrete a → Timeless (ouPred_ownM a).
Proof.
  intros ?. rewrite /Timeless later_ownM. apply exist_elim=> b.
  rewrite (timeless (a≡b)) (except_0_intro (ouPred_ownM b)) -except_0_and.
  apply except_0_mono. rewrite internal_eq_sym.
  apply (internal_eq_rewrite' b a (ouPred_ownM) _);
    auto using and_elim_l, and_elim_r.
Qed.

(** Plainness *)
Global Instance ora_valid_plain {A : ora} (a : A) :
  Plain (✓ a : ouPred M)%I.
Proof. rewrite /Persistent. apply plainly_ora_valid_1. Qed.

(** Persistence *)
Global Instance ora_valid_persistent {A : ora} (a : A) :
  Persistent (✓ a : ouPred M)%I.
Proof. rewrite /Persistent. apply persistently_ora_valid_1. Qed.
Global Instance ownM_persistent a : OraCoreId a → Persistent (@ouPred_ownM M a).
Proof.
  intros. rewrite /Persistent -{2}(core_id_core a). apply persistently_ownM_core.
Qed.

(** For big ops *)
Global Instance ouPred_ownM_sep_homomorphism :
  MonoidHomomorphism op ouPred_sep (≡) (@ouPred_ownM M).
Proof. split; [split|]; try apply _; [apply ownM_op | apply ownM_unit']. Qed.

(** Consistency/soundness statement *)
(*Lemma bupd_plain_soundness P `{!Plain P} : (⊢ |==> P) → ⊢ P.
Proof.
  eapply bi_emp_valid_mono. etrans; last exact: bupd_plainly. apply bupd_mono'.
  apply: plain.
Qed.

Corollary soundness φ n : (⊢@{ouPredI M} ▷^n ⌜ φ ⌝) → φ.
Proof.
  induction n as [|n IH]=> /=.
  - apply pure_soundness.
  - intros H. by apply IH, later_soundness.
Qed.

Corollary consistency_modal n : ¬ ⊢@{ouPredI M} ▷^n False.
Proof. exact (soundness False n). Qed.

Corollary consistency : ¬ ⊢@{ouPredI M} False.
Proof. exact (consistency_modal 0). Qed.
End derived.*)

End derived.
End ouPred.
