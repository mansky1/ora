From iris.algebra Require Export updates.
From iris.algebra Require Export stepindex_finite.
From iris.bi Require Export derived_connectives plainly internal_eq bi.
From iris_ora.algebra Require Export ora.
From iris.si_logic Require Import siprop.
From stdpp Require Import finite.
Set Default Proof Using "Type".
Local Hint Extern 1 (_ ≼ₒ _) => etrans; [eassumption|] : core.
Local Hint Extern 1 (_ ≼ₒ _) => etrans; [|eassumption] : core.
Local Hint Extern 10 (_ ≤ _) => lia : core.


(* TODO: change following text. *)

(** The basic definition of the ouPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

(* A good way of understanding this definition of the uPred OFE is to
   consider the OFE uPred0 of monotonous SProp predicates. That is,
   uPred0 is the OFE of non-expansive functions from M to SProp that
   are monotonous with respect to CMRA inclusion. This notion of
   monotonicity has to be stated in the SProp logic. Together with the
   usual closedness property of SProp, this gives exactly uPred_mono.

   Then, we quotient uPred0 *in the sProp logic* with respect to
   equivalence on valid elements of M. That is, we quotient with
   respect to the following *sProp* equivalence relation:
     P1 ≡ P2 := ∀ x, ✓ x → (P1(x) ↔ P2(x))       (1)
   When seen from the ambiant logic, obtaining this quotient requires
   definig both a custom Equiv and Dist.


   It is worth noting that this equivalence relation admits canonical
   representatives. More precisely, one can show that every
   equivalence class contains exactly one element P0 such that:
     ∀ x, (✓ x → P0(x)) → P0(x)                 (2)
   (Again, this assertion has to be understood in sProp). Intuitively,
   this says that P0 trivially holds whenever the resource is invalid.
   Starting from any element P, one can find this canonical
   representative by choosing:
     P0(x) := ✓ x → P(x)                        (3)

   Hence, as an alternative definition of uPred, we could use the set
   of canonical representatives (i.e., the subtype of monotonous
   sProp predicates that verify (2)). This alternative definition would
   save us from using a quotient. However, the definitions of the various
   connectives would get more complicated, because we have to make sure
   they all verify (2), which sometimes requires some adjustments. We
   would moreover need to prove one more property for every logical
   connective.
 *)

Record ouPred (M : uora) : Type := IProp {
  ouPred_holds :> nat → M → Prop;

  ouPred_mono n1 n2 x1 x2 :
    ouPred_holds n1 x1 → x1 ≼ₒ{n1} x2 → n2 ≤ n1 → ouPred_holds n2 x2
}.

Bind Scope bi_scope with ouPred.
Arguments ouPred_holds {_} _ _ _ : simpl never.
Add Printing Constructor ouPred.
#[export] Instance: Params (@ouPred_holds) 3 := {}.


Section cofe.
  Context {M : uora}.

  Inductive ouPred_equiv' (P Q : ouPred M) : Prop :=
    { ouPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Instance ouPred_equiv : Equiv (ouPred M) := ouPred_equiv'.
  Inductive ouPred_dist' (n : nat) (P Q : ouPred M) : Prop :=
    { ouPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Instance ouPred_dist : Dist (ouPred M) := ouPred_dist'.
  Definition ouPred_ofe_mixin : OfeMixin (ouPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros n m P Q HPQ; split=> i x ??; apply HPQ; auto.
      by trans m.
  Qed.
  Canonical Structure ouPredO : ofe := Ofe (ouPred M) ouPred_ofe_mixin.

  Program Definition ouPred_compl : Compl ouPredO := λ c,
    {| ouPred_holds n x := ∀ n', n' ≤ n → ✓{n'}x → c n' n' x |}.
  Next Obligation.
    move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply ouPred_mono.
    eapply HP, ora_validN_orderN, ora_orderN_le=>//; try auto.
    trans n2; try done.
    eapply ora_orderN_le=>//. trans n2; done. done.
  Qed.
  Global Program Instance ouPred_cofe : Cofe ouPredO := cofe_finite ouPred_compl _.
  Next Obligation.
    intros n c.
    split=>i x Hin Hv.
    etrans; [|by symmetry; apply (chain_cauchy c i n)]. split=>H; [by apply H|].
    repeat intro. apply (chain_cauchy c n' i)=>//. by eapply ouPred_mono.
  Qed.
End cofe.
Arguments ouPredO : clear implicits.

#[export] Instance ouPred_ne {M} (P : ouPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply ouPred_mono; eauto; by rewrite Hx.
Qed.
#[export] Instance ouPred_proper {M} (P : ouPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply ouPred_ne, equiv_dist. Qed.

Lemma ouPred_holds_ne {M} (P Q : ouPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done. eauto using ouPred_mono, cmra_validN_le.
Qed.

(* TODO: remove!? *)
(* Equivalence to the definition of uPred in the appendix. *)
Lemma ouPred_alt {M : uora} (P: nat → M → Prop) :
  (∀ n1 n2 x1 x2, P n1 x1 → x1 ≼ₒ{n1} x2 → n2 ≤ n1 → P n2 x2) ↔
  ( (∀ x n1 n2, n2 ≤ n1 → P n1 x → P n2 x) (* Pointwise down-closed *)
  ∧ (∀ n x1 x2, x1 ≡{n}≡ x2 → ∀ m, m ≤ n → P m x1 ↔ P m x2) (* Non-expansive *)
  ∧ (∀ n x1 x2, x1 ≼ₒ{n} x2 → ∀ m, m ≤ n → P m x1 → P m x2) (* Monotonicity *)
  ).
Proof.
  (* Provide this lemma to eauto. *)
  assert (∀ n1 n2 (x1 x2 : M), n2 ≤ n1 → x1 ≡{n1}≡ x2 → x1 ≼ₒ{n2} x2).
  { intros ????? H. eapply ora_orderN_le; last done. by rewrite H. }
  (* Now go ahead. *)
  split.
  - intros Hupred. repeat split; eauto using ora_orderN_le.
  - intros (Hdown & _ & Hmono) **. eapply Hmono; [done..|]. eapply Hdown; done.
Qed.

(** functor *)
Program Definition ouPred_map {M1 M2 : uora} (f : M2 -n> M1)
  `{!OraMorphism f} (P : ouPred M1) :
  ouPred M2 := {| ouPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using ouPred_mono, ora_morphism_monotoneN. Qed.

Global Instance ouPred_map_ne {M1 M2 : uora} (f : M2 -n> M1)
  `{!OraMorphism f} n : Proper (dist n ==> dist n) (ouPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using ora_morphism_validN.
Qed.
Lemma ouPred_map_id {M : uora} (P : ouPred M): ouPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma ouPred_map_compose {M1 M2 M3 : uora} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!OraMorphism f, !OraMorphism g} (P : ouPred M3):
  ouPred_map (g ◎ f) P ≡ ouPred_map f (ouPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma ouPred_map_ext {M1 M2 : uora} (f g : M1 -n> M2)
      `{!OraMorphism f} `{!OraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, ouPred_map f x ≡ ouPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /ouPred_holds /= Hf. Qed.
Definition ouPredO_map {M1 M2 : uora} (f : M2 -n> M1) `{!OraMorphism f} :
  ouPredO M1 -n> ouPredO M2 := OfeMor (ouPred_map f : ouPredO M1 → ouPredO M2).
Lemma ouPredO_map_ne {M1 M2 : uora} (f g : M2 -n> M1)
    `{!OraMorphism f, !OraMorphism g} n :
  f ≡{n}≡ g → ouPredO_map f ≡{n}≡ ouPredO_map g.
Proof.
  intros Hfg P; split=> n' y ??.
    rewrite /ouPred_holds /= (dist_le _ _ _ _(Hfg y)); done.
Qed.

Program Definition ouPredOF (F : uorarFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := ouPredO (uorarFunctor_car F B A);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := ouPredO_map (uorarFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply ouPredO_map_ne, uorarFunctor_map_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros F A ? B ? P; simpl. rewrite -{2}(ouPred_map_id P).
  apply ouPred_map_ext=>y. by rewrite uorarFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' P; simpl. rewrite -ouPred_map_compose.
  apply ouPred_map_ext=>y; apply uorarFunctor_map_compose.
Qed.

#[export] Instance ouPredOF_contractive F :
  uorarFunctorContractive F → oFunctorContractive (ouPredOF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n P Q HPQ. apply ouPredO_map_ne, uorarFunctor_map_contractive.
  destruct HPQ as [HPQ]. constructor. intros ??.
  split; by eapply HPQ.
Qed.

(** logical entailment *)
Inductive ouPred_entails {M} (P Q : ouPred M) : Prop :=
  { ouPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
#[export] Hint Resolve ouPred_mono : ouPred_def.

(** logical connectives *)
Local Program Definition ouPred_si_pure_def {M} (Pi : siProp) : ouPred M :=
  {| ouPred_holds n x := siProp_holds Pi n |}.
Solve Obligations with naive_solver eauto using siProp_closed.
Local Definition ouPred_si_pure_aux : seal (@ouPred_si_pure_def).
Proof. by eexists. Qed.
Definition ouPred_si_pure := ouPred_si_pure_aux.(unseal).
Global Arguments ouPred_si_pure {M}.
Local Definition ouPred_si_pure_unseal :
  @ouPred_si_pure = @ouPred_si_pure_def := ouPred_si_pure_aux.(seal_eq).

Local Program Definition ouPred_si_emp_valid_def {M} (P : ouPred M) : siProp :=
  {| siProp_holds n := P n ε |}.
Solve Obligations with naive_solver eauto with ouPred_def.
Local Definition ouPred_si_emp_valid_aux : seal (@ouPred_si_emp_valid_def).
Proof. by eexists. Qed.
Definition ouPred_si_emp_valid := ouPred_si_emp_valid_aux.(unseal).
Global Arguments ouPred_si_emp_valid {M}.
Local Definition ouPred_si_emp_valid_unseal :
  @ouPred_si_emp_valid = @ouPred_si_emp_valid_def := ouPred_si_emp_valid_aux.(seal_eq).

Program Definition ouPred_and_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_and_aux : seal (@ouPred_and_def). by eexists. Qed.
Definition ouPred_and {M} := unseal ouPred_and_aux M.
Definition ouPred_and_eq: @ouPred_and = @ouPred_and_def := seal_eq ouPred_and_aux.

Program Definition ouPred_or_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_or_aux : seal (@ouPred_or_def). by eexists. Qed.
Definition ouPred_or {M} := unseal ouPred_or_aux M.
Definition ouPred_or_eq: @ouPred_or = @ouPred_or_def := seal_eq ouPred_or_aux.

Program Definition ouPred_impl_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ n' x',
       x ≼ₒ{n'} x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ Hle1 Hn1 n2 x3 Hle2 ?; simpl in *.
  apply HPQ; eauto.
  etrans; last apply Hle2.
  eapply ora_orderN_le; eauto.
  trans n1'; done.
Qed.
Definition ouPred_impl_aux : seal (@ouPred_impl_def). by eexists. Qed.
Definition ouPred_impl {M} := unseal ouPred_impl_aux M.
Definition ouPred_impl_eq :
  @ouPred_impl = @ouPred_impl_def := seal_eq ouPred_impl_aux.

Program Definition ouPred_forall_def {M A} (Ψ : A → ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_forall_aux : seal (@ouPred_forall_def). by eexists. Qed.
Definition ouPred_forall {M A} := unseal ouPred_forall_aux M A.
Definition ouPred_forall_eq :
  @ouPred_forall = @ouPred_forall_def := seal_eq ouPred_forall_aux.

Program Definition ouPred_exist_def {M A} (Ψ : A → ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_exist_aux : seal (@ouPred_exist_def). by eexists. Qed.
Definition ouPred_exist {M A} := unseal ouPred_exist_aux M A.
Definition ouPred_exist_eq: @ouPred_exist = @ouPred_exist_def := seal_eq ouPred_exist_aux.

Program Definition ouPred_sep_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∃ x1 x2, x1 ⋅ x2 ≼ₒ{n} x ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros M P Q n1 n2 x y (x1&x2&Hx&?&?) ? ?.
  eexists x1, x2; repeat split; eauto using ouPred_mono.
  etrans; eapply ora_orderN_le; eauto.
Qed.
Definition ouPred_sep_aux : seal (@ouPred_sep_def). by eexists. Qed.
Definition ouPred_sep {M} := unseal ouPred_sep_aux M.
Definition ouPred_sep_eq: @ouPred_sep = @ouPred_sep_def := seal_eq ouPred_sep_aux.

Program Definition ouPred_wand_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ ? Hn n3 x3 ???; simpl in *.
  eapply ouPred_mono with n3 (x1 ⋅ x3);
    eauto using HPQ, ora_validN_orderN, ora_monoN_r, ora_orderN_le.
  apply HPQ; eauto.
  eauto using ora_validN_orderN,  ora_monoN_r, ora_orderN_le.
Qed.
Definition ouPred_wand_aux : seal (@ouPred_wand_def). by eexists. Qed.
Definition ouPred_wand {M} := unseal ouPred_wand_aux M.
Definition ouPred_wand_eq :
  @ouPred_wand = @ouPred_wand_def := seal_eq ouPred_wand_aux.

Program Definition ouPred_persistently_def {M} (P : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n (core x) |}.
Next Obligation.
  intros M P n1 n2 x1 x2 HP Hx Hn; simpl in *.
  eapply ouPred_mono; eauto. by apply ora_core_monoN.
Qed.
Definition ouPred_persistently_aux : seal (@ouPred_persistently_def). by eexists. Qed.
Definition ouPred_persistently {M} := unseal ouPred_persistently_aux M.
Definition ouPred_persistently_eq :
  @ouPred_persistently = @ouPred_persistently_def := seal_eq ouPred_persistently_aux.

Program Definition ouPred_later_def {M} (P : ouPred M) : ouPred M :=
  {| ouPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation.
  intros M P [|n1] [|n2] x1 x2; eauto using ouPred_mono, ora_orderN_le, SIdx.le_succ_diag_r with lia.
Qed.
Definition ouPred_later_aux : seal (@ouPred_later_def). by eexists. Qed.
Definition ouPred_later {M} := unseal ouPred_later_aux M.
Definition ouPred_later_eq :
  @ouPred_later = @ouPred_later_def := seal_eq ouPred_later_aux.

Program Definition ouPred_ownM_def {M : uora} (a : M) : ouPred M :=
  {| ouPred_holds n x := a ≼ₒ{n} x |}.
Next Obligation.
  intros M a n1 n2 x1 x2; simpl => Hax1 Hx1x2 Hn.
  eapply ora_orderN_le; last eassumption.
  etrans; eauto.
Qed.
Definition ouPred_ownM_aux : seal (@ouPred_ownM_def). by eexists. Qed.
Definition ouPred_ownM {M} := unseal ouPred_ownM_aux M.
Definition ouPred_ownM_eq :
  @ouPred_ownM = @ouPred_ownM_def := seal_eq ouPred_ownM_aux.

Local Program Definition ouPred_bupd_def {M} (Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ k yf,
      k ≤ n → ✓{k} (x ⋅ yf) → ∃ x', ✓{k} (x' ⋅ yf) ∧ Q k x' |}.
Next Obligation.
  intros M Q n1 n2 x1 x2 HQ Hord Hn k yf Hk Hxy.
  eapply ora_validN_orderN in Hxy; last eapply ora_monoN_r, ora_orderN_le; [|done|simpl; lia].
  auto.
Qed.
Local Definition ouPred_bupd_aux : seal (@ouPred_bupd_def). Proof. by eexists. Qed.
Definition ouPred_bupd := ouPred_bupd_aux.(unseal).
Global Arguments ouPred_bupd {M}.
Local Definition ouPred_bupd_unseal :
  @ouPred_bupd = @ouPred_bupd_def := ouPred_bupd_aux.(seal_eq).

Module ouPred_unseal.
Local Definition unseal_eqs :=
  (ouPred_si_pure_unseal, ouPred_si_emp_valid_unseal,
  ouPred_and_eq, ouPred_or_eq, ouPred_impl_eq, ouPred_forall_eq,
  ouPred_exist_eq, ouPred_sep_eq, ouPred_wand_eq,
  ouPred_persistently_eq, ouPred_later_eq, ouPred_ownM_eq,
  @ouPred_bupd_unseal).
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_emp; simpl;
  unfold bupd, bi_bupd_bupd, bi_pure,
    bi_and, bi_or, bi_impl, bi_forall, bi_exist,
    bi_sep, bi_wand, bi_persistently, bi_later; simpl;
  rewrite !unseal_eqs /=.
End ouPred_unseal.

Local Arguments ouPred_holds {_} !_ _ _ /.

Local Instance entails_po {M} : PreOrder (@ouPred_entails M).
Proof.
  split.
  - by intros P; split=> x i.
  - by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
Qed.

Definition ouPred_pure {M} (φ : Prop) : ouPred M := ouPred_si_pure ⌜ φ ⌝.
Program Definition ouPred_emp {M} : ouPred M := {| ouPred_holds n x := ε ≼ₒ{n} x |}.
Next Obligation.
Proof.
  intros M n1 n2 x1 x2; simpl => Hx1 Hx2 Hn.
  eapply ora_orderN_le; last eassumption.
  etrans; eauto.
Qed.

Section primitive.
  Context {M : uora}.
  Implicit Types φ : Prop.
  Implicit Types P Q : ouPred M.
  Implicit Types A : Type.
  Local Arguments ouPred_holds {_} !_ _ _ /.
  Local Arguments siProp_holds !_ _ /.
  Local Hint Immediate ouPred_in_entails : core.
  Import ouPred_unseal.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (@ouPred_entails M P%I Q%I) : stdpp_scope.
  Notation "(⊢)" := (@ouPred_entails M) (only parsing) : stdpp_scope.
  Notation "P ⊣⊢ Q" := (@ouPred_equiv M P%I Q%I) : stdpp_scope.
  Notation "(⊣⊢)" := (@ouPred_equiv M) (only parsing) : stdpp_scope.

  Notation "<si_pure> Pi" := (ouPred_si_pure Pi) : bi_scope.
  Notation "<si_emp_valid> P" := (ouPred_si_emp_valid P).
  Notation "'⌜' φ '⌝'" := (<si_pure> siProp_pure φ%type%stdpp)%I : bi_scope.
  Notation "'True'" := ⌜ True ⌝%I : bi_scope.
  Notation "'False'" := ⌜ False ⌝%I : bi_scope.
  Infix "∧" := ouPred_and : bi_scope.
  Infix "∨" := ouPred_or : bi_scope.
  Infix "→" := ouPred_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (ouPred_forall (λ x, .. (ouPred_forall (λ y, P)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (ouPred_exist (λ x, .. (ouPred_exist (λ y, P)) ..)) : bi_scope.
  Infix "∗" := ouPred_sep : bi_scope.
  Infix "-∗" := ouPred_wand : bi_scope.
  Notation "□ P" := (ouPred_persistently P) : bi_scope.
  Notation "▷ P" := (ouPred_later P) : bi_scope.
  Notation "|==> P" := (ouPred_bupd P) : bi_scope.

  Lemma si_pure_ne : NonExpansive (@ouPred_si_pure M).
  Proof. intros n Pi Pi' HPi. unseal; split; intros; by apply HPi. Qed.

  Lemma si_emp_valid_ne : NonExpansive (@ouPred_si_emp_valid M).
  Proof.
    intros n P P' HP.
    unseal; split; intros; apply HP; auto using ucmra_unit_validN.
  Qed.

  (** Rules for the [siProp] embedding *)
  Lemma si_pure_mono Pi Qi : siProp_entails Pi Qi → <si_pure> Pi ⊢ <si_pure> Qi.
  Proof. intros HPQi. unseal; split=> n ??. apply HPQi. Qed.
  Lemma si_emp_valid_mono P Q :
    (P ⊢ Q) → siProp_entails (ouPred_si_emp_valid P) (ouPred_si_emp_valid Q).
  Proof. intros HPQ. unseal; split=> n. apply HPQ, ucmra_unit_validN. Qed.

  Lemma si_pure_impl_2 Pi Qi :
    (<si_pure> Pi → <si_pure> Qi) ⊢ <si_pure> siProp_impl Pi Qi.
  Proof.
    unseal; siProp_primitive.unseal. split; simpl.
    intros ??? H ???; eapply H; eauto.
    by eapply (@cmra_validN_le _ M).
  Qed.
  Lemma si_pure_forall_2 {A} (Φi : A → siProp) :
   (∀ x, <si_pure> Φi x) ⊢ <si_pure> siProp_forall Φi.
  Proof. by unseal; siProp_primitive.unseal. Qed.
  Lemma si_pure_later Pi : <si_pure> siProp_later Pi ⊣⊢ ▷ <si_pure> Pi.
  Proof. by unseal; siProp_primitive.unseal. Qed.

  Lemma si_emp_valid_later_1 P :
    siProp_entails (ouPred_si_emp_valid (▷ P)) (siProp_later (ouPred_si_emp_valid P)).
  Proof. by unseal; siProp_primitive.unseal. Qed.
  Lemma si_emp_valid_exist_1 {A} (Φ : A → ouPred M) :
    siProp_entails (ouPred_si_emp_valid (∃ x, Φ x))
                   (siProp_exist (λ x, <si_emp_valid> Φ x)).
  Proof. by unseal; siProp_primitive.unseal. Qed.

  Lemma si_emp_valid_si_pure Pi :
    <si_emp_valid> (<si_pure> Pi : ouPred M)%I ≡ Pi.
  Proof. by unseal. Qed.
  Lemma si_pure_si_emp_valid P :
    <si_pure> (ouPred_si_emp_valid P) ⊢ □ P.
  Proof.
    unseal. split=> /= n x _ ?.
    eapply ouPred_mono with n ε; eauto.
    apply ora_order_orderN, uora_unit_order_core.
  Qed.

  Lemma persistently_impl_si_pure Pi Q :
    (<si_pure> Pi → □ Q) ⊢ □ (<si_pure> Pi → Q).
  Proof.
    unseal; split=> /= n x ? HPQ n' x' ????.
    eapply ouPred_mono with n' (core x)=>//.
    apply (HPQ n' x); eauto.
    by eapply (@cmra_validN_le _ M).
  Qed.

  Lemma prop_ext_2 P Q :
    siProp_entails (ouPred_si_emp_valid ((P -∗ Q) ∧ (Q -∗ P)))
                   (siProp_internal_eq P Q).
  Proof.
    unseal; siProp_primitive.unseal.
    split=> n /=. setoid_rewrite (left_id ε op). split; naive_solver.
  Qed.

(** Introduction and elimination rules *)
  Lemma and_elim_l P Q : P ∧ Q ⊢ P.
  Proof. by unseal; split=> n x ? [??]. Qed.
  Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
  Proof. by unseal; split=> n x ? [??]. Qed.
  Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
  Proof. intros HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR]. Qed.

  Lemma forall_intro {A} P (Ψ : A → ouPred M): (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ. Qed.
  Lemma forall_elim {A} {Ψ : A → ouPred M} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof. unseal; split=> n x ? HP; apply HP. Qed.

  (** Persistently *)
  Lemma persistently_mono P Q : (P ⊢ Q) → □ P ⊢ □ Q.
  Proof. intros HP; unseal; split=> n x ? /=. by apply HP, ora_core_validN. Qed.
  Lemma persistently_idemp_2 P : □ P ⊢ □ □ P.
  Proof. unseal; split=> n x ?? /=. by rewrite ora_core_idemp. Qed.

  Lemma persistently_forall_2 {A} (Ψ : A → ouPred M) : (∀ a, □ Ψ a) ⊢ (□ ∀ a, Ψ a).
  Proof. by unseal. Qed.
  Lemma persistently_exist_1 {A} (Ψ : A → ouPred M) : (□ ∃ a, Ψ a) ⊢ (∃ a, □ Ψ a).
  Proof. by unseal. Qed.

End primitive.

Local Lemma pure_ne {M} n : Proper (iff ==> dist n) (@ouPred_pure M).
Proof. intros φ1 φ2 Hφ. apply si_pure_ne. by rewrite Hφ. Qed.

Local Lemma pure_intro {M} (φ : Prop) (P : ouPred M) :
  φ → ouPred_entails P (ouPred_pure φ).
Proof.
  intros. 
  trans (ouPred_si_pure (∀ x : False, True) : ouPred M).
  - etrans; last apply si_pure_forall_2. by apply forall_intro.
  - by apply si_pure_mono, bi.pure_intro.
Qed.

Local Lemma pure_elim' {M} (φ : Prop) (P : ouPred M) :
  (φ → ouPred_entails (ouPred_pure True) P) →
  ouPred_entails (ouPred_pure φ) P.
Proof.
  rewrite /ouPred_pure; ouPred_unseal.unseal; siProp_primitive.unseal.
  intros; split; intros.
  by eapply H; eauto.
Qed.

(** BI instances *)
Lemma ouPred_bi_mixin (M : uora) :
  BiMixin
    ouPred_entails ouPred_emp ouPred_pure ouPred_and ouPred_or ouPred_impl
    (@ouPred_forall M) (@ouPred_exist M) ouPred_sep ouPred_wand
    .
Proof.
  split.
  - (* PreOrder ouPred_entails *)
    split.
    + by intros P; split=> x i.
    + by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
  - (* (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P) *)
    intros P Q. split.
    + intros HPQ; split; split=> x i; apply HPQ.
    + intros [HPQ HQP]; split=> x n; by split; [apply HPQ|apply HQP].
  - exact: pure_ne.
  - (* NonExpansive2 ouPred_and *)
    intros n P P' HP Q Q' HQ; ouPred_unseal.unseal; split=> x n' ??.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  - (* NonExpansive2 ouPred_or *)
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    ouPred_unseal.unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  - (* NonExpansive2 ouPred_impl *)
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    ouPred_unseal.unseal; split; intros HPQ x' n'' ????; apply HQ, HPQ, HP; auto.
  - (* Proper (pointwise_relation A (dist n) ==> dist n) ouPred_forall *)
    by intros A n Ψ1 Ψ2 HΨ; ouPred_unseal.unseal; split=> n' x; split; intros HP a; apply HΨ.
  - (* Proper (pointwise_relation A (dist n) ==> dist n) ouPred_exist *)
    intros A n Ψ1 Ψ2 HΨ.
    ouPred_unseal.unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
  - (* NonExpansive2 ouPred_sep *)
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    ouPred_unseal.unseal; split; intros (x1&x2&?&?&?); ofe_subst;
      exists x1, x2; split_and!; try (apply HP || apply HQ); eauto.
    + eapply (@cmra_validN_op_l _ M), ora_validN_orderN; eauto.
    + eapply (@cmra_validN_op_r _ M), ora_validN_orderN; eauto.
    + eapply (@cmra_validN_op_l _ M), ora_validN_orderN; eauto.
    + eapply (@cmra_validN_op_r _ M), ora_validN_orderN; eauto.
  - (* NonExpansive2 ouPred_wand *)
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    ouPred_unseal.unseal; split; intros HPQ x' n'' ???;
      apply HQ, HPQ, HP; eauto.
    + eapply (@cmra_validN_op_r _ M); eauto.
    + eapply (@cmra_validN_op_r _ M); eauto.
  - exact: pure_intro.
  - exact: pure_elim'.
  - (* P ∧ Q ⊢ P *)
    intros P Q. ouPred_unseal.unseal; by split=> n x ? [??].
  - (* P ∧ Q ⊢ Q *)
    intros P Q. ouPred_unseal.unseal; by split=> n x ? [??].
  - (* (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R *)
    intros P Q R HQ HR; ouPred_unseal.unseal; split=> n x ??; by split; [apply HQ|apply HR].
  - (* P ⊢ P ∨ Q *)
    intros P Q. ouPred_unseal.unseal; split=> n x ??; left; auto.
  - (* Q ⊢ P ∨ Q *)
    intros P Q. ouPred_unseal.unseal; split=> n x ??; right; auto.
  - (* (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R *)
    intros P Q R HP HQ. ouPred_unseal.unseal; split=> n x ? [?|?]. by apply HP. by apply HQ.
  - (* (P ∧ Q ⊢ R) → P ⊢ Q → R. *)
    intros P Q R. ouPred_unseal.unseal => HQ; split=> n x ?? n' x' ????. apply HQ;
      naive_solver eauto using ouPred_mono, cmra_included_includedN.
  - (* (P ⊢ Q → R) → P ∧ Q ⊢ R *)
    intros P Q R. ouPred_unseal.unseal=> HP; split=> n x ? [??]. apply HP with n x; auto.
  - (* (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a *)
    intros A P Ψ. ouPred_unseal.unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ.
  - (* (∀ a, Ψ a) ⊢ Ψ a *)
    intros A Ψ a. ouPred_unseal.unseal; split=> n x ? HP; apply HP.
  - (* Ψ a ⊢ ∃ a, Ψ a *)
    intros A Ψ a. ouPred_unseal.unseal; split=> n x ??; by exists a.
  - (* (∀ a, Ψ a ⊢ Q) → (∃ a, Ψ a) ⊢ Q *)
    intros A Ψ Q. ouPred_unseal.unseal; intros HΨ; split=> n x ? [a ?]; by apply HΨ with a.
  - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *)
    intros P P' Q Q' HQ HQ'; ouPred_unseal.unseal.
    split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x; repeat split; eauto.
    + apply HQ; auto.
      eapply (@cmra_validN_op_l _ M), ora_validN_orderN; eauto.
    + apply HQ'; auto.
      eapply (@cmra_validN_op_r _ M), ora_validN_orderN; eauto.
  - (* P ⊢ emp ∗ P *)
    intros P. rewrite /ouPred_emp. ouPred_unseal.unseal; split=> n x ?? /=.
    exists (core x), x. rewrite ora_core_l; repeat split; auto.
    apply ora_order_orderN, uora_unit_order_core.
  - (* emp ∗ P ⊢ P *)
    intros P. ouPred_unseal.unseal; split; intros n x ? (x1&x2&?&?&?); ofe_subst.
    eapply ouPred_mono; eauto.
    rewrite -(left_id _ _ x2). etrans; last eauto.
    by eapply ora_orderN_op.
  - (* P ∗ Q ⊢ Q ∗ P *)
    intros P Q. ouPred_unseal.unseal; split; intros n x ? (x1&x2&?&?&?).
    exists x2, x1. by rewrite (comm op).
  - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *)
    intros P Q R. ouPred_unseal.unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
    exists y1, (y2 ⋅ x2); split_and?; auto.
    + by rewrite (assoc op); setoid_rewrite <-Hx; setoid_rewrite Hy.
    + by exists y2, x2.
  - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *)
    intros P Q R. ouPred_unseal.unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
    exists x, x'; split_and?; auto.
    eapply ouPred_mono; eauto using cmra_validN_op_l.
  - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *)
    intros P Q R. ouPred_unseal.unseal=> HPQR. split; intros n x ? (?&?&?&HP&HQ).
    apply HPQR in HP.
    apply HP in HQ; eauto using ora_validN_orderN.
    eauto using ouPred_mono.
    { eapply (@cmra_validN_op_l _ M), ora_validN_orderN; eauto. }
Qed.

Lemma ouPred_bi_persistently_mixin (M : uora) :
  BiPersistentlyMixin ouPred_entails ouPred_emp ouPred_and
  (@ouPred_exist M) ouPred_sep ouPred_persistently.
Proof.
split.
  - (* NonExpansive ouPred_persistently *)
    intros n P1 P2 HP.
    ouPred_unseal.unseal; split=> n' x; split; apply HP;
    try apply @ora_core_validN; auto; try apply _.
  - (* (P ⊢ Q) → bi_persistently P ⊢ bi_persistently Q *)
    intros P QR HP. ouPred_unseal.unseal; split=> n x ? /=. by apply HP, ora_core_validN.
  - (* bi_persistently P ⊢ bi_persistently (bi_persistently P) *)
    intros P. ouPred_unseal.unseal; split=> n x ?? /=. by rewrite ora_core_idemp.
  - (* emp ⊢ bi_persistently emp *)
    ouPred_unseal.unseal; split => n x Hx HP /=;
      apply ora_order_orderN; apply uora_unit_order_core.
  - (* (∀ a, bi_persistently (Ψ a)) ⊢ bi_persistently (∀ a, Ψ a) *)
    by ouPred_unseal.unseal.
  - (* bi_persistently (∃ a, Ψ a) ⊢ ∃ a, bi_persistently (Ψ a) *)
    by ouPred_unseal.unseal.
  - (* bi_persistently P ∗ Q ⊢ bi_persistently P (ADMISSIBLE) *)
    ouPred_unseal.unseal; split; intros n x ? (x1&x2&?&?&_); ofe_subst.
    eapply ouPred_mono; eauto.
    etrans; last by apply ora_core_monoN; eassumption.
    eapply ora_order_orderN, uora_core_order_op.
  - (* bi_persistently P ∧ Q ⊢ P ∗ Q *)
    intros P Q. ouPred_unseal.unseal; split=> n x ? [??]; simpl in *.
    exists (core x), x; rewrite ?ora_core_l; repeat split; auto.
Qed.

Lemma ouPred_bi_later_mixin (M : uora) : BiLaterMixin
  ouPred_entails ouPred_pure ouPred_or ouPred_impl
  (@ouPred_forall M) (@ouPred_exist M) ouPred_sep
  ouPred_persistently ouPred_later.
Proof.
  split.
  - (* NonExpansive bi_later *)
    ouPred_unseal.unseal; intros n P Q HPQ; split=> -[|n'] x ?? //=; try lia.
    apply HPQ, (cmra_validN_S(A:=M)); auto.
  - (* (P ⊢ Q) → ▷ P ⊢ ▷ Q *)
    intros P Q.
    ouPred_unseal.unseal=> HP; split=>-[|n] x ??; [done|by apply HP; [apply (cmra_validN_S(A:=M))|]].
  - (* P ⊢ ▷ P *)
    intros P. ouPred_unseal.unseal; split=> -[|n] /= x ? HP; first done.
    apply ouPred_mono with (S n) x; eauto.
  - (* (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a *)
    intros A Φ. ouPred_unseal.unseal; by split=> -[|n] x.
  - (* (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a) *)
    intros A Φ. ouPred_unseal.unseal; split=> -[|[|n]] x /=; eauto.
  - (* ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q *)
    intros P Q. ouPred_unseal.unseal; split=> -[|n] x ? /=.
    { by exists x, (core x); rewrite ora_core_r. }
    intros (x1&x2&Hx&?&?); destruct (ora_op_extend n x x1 x2)
      as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_S; simpl in *.
    exists y1, y2; split; auto; by rewrite Hy1 Hy2.
  - (* ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q) *)
    intros P Q. ouPred_unseal.unseal; split=> -[|n] x ? /=; [done|intros (x1&x2&Hx&?&?)].
    exists x1, x2. split; eauto. eapply ora_orderN_le; eauto. simpl; lia.
  - (* ▷ bi_persistently P ⊢ bi_persistently (▷ P) *)
    by ouPred_unseal.unseal.
  - (* bi_persistently (▷ P) ⊢ ▷ bi_persistently P *)
    by ouPred_unseal.unseal.
  - (* ▷ P ⊢ ▷ False ∨ (▷ False → P) *)
    intros P. rewrite /ouPred_pure; ouPred_unseal.unseal; siProp_primitive.unseal; split=> -[|n] x ? /= HP; [by left|right].
    intros [|n'] x' ????; [|done].
    eapply ouPred_mono; [| eassumption | trivial].
    eapply ouPred_mono; eauto.
Qed.

Canonical Structure ouPredI (M : uora) : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (ouPred M); bi_bi_mixin := ouPred_bi_mixin M;
     bi_bi_persistently_mixin := ouPred_bi_persistently_mixin M;
     bi_bi_later_mixin := ouPred_bi_later_mixin M |}.

Lemma ouPred_sbi_mixin M : SbiMixin (ouPredI M) ouPred_si_pure ouPred_si_emp_valid.
Proof.
  split.
  - exact: si_pure_ne.
  - exact: si_emp_valid_ne.
  - exact: si_pure_mono.
  - exact: si_emp_valid_mono.
  - exact: si_emp_valid_si_pure.
  - exact: si_pure_si_emp_valid.
  - exact: si_pure_impl_2.
  - exact: @si_pure_forall_2.
  - exact: persistently_impl_si_pure.
  - exact: si_pure_later.
  - (* Absorbing (<si_pure> Pi) (ADMISSIBLE) *)
    intros Pi. rewrite /Absorbing /bi_absorbingly /si_pure; ouPred_unseal.unseal.
    split; intros ??? (? & ? & ? & ? & ?); auto.
  - exact: @si_emp_valid_later_1.
  - (* <si_emp_valid> P -∗ <si_emp_valid> <affine> P (ADMISSIBLE) *)
    intros P. rewrite /bi_affinely /si_emp_valid; ouPred_unseal.unseal.
    split; intros; split; auto.
    apply ora_orderN_refl.
Qed.
Lemma ouPred_sbi_prop_ext_mixin M : SbiPropExtMixin (ouPredI M) ouPred_si_emp_valid.
Proof. apply sbi_prop_ext_mixin. apply prop_ext_2. Qed.
Global Instance ouPred_sbi M : Sbi (ouPredI M) :=
  {| sbi_sbi_mixin := ouPred_sbi_mixin M;
     sbi_sbi_prop_ext_mixin := ouPred_sbi_prop_ext_mixin M |}.

(* Latest notation *)
Global Instance later_contractive M : Contractive (bi_later (PROP:=ouPredI M)).
Proof.
  ouPred_unseal.unseal; intros [|n] P Q HPQ; split=> -[|n'] x ?? //=; try lia.
  eapply HPQ, (cmra_validN_S(A:=M)); auto. simpl; lia.
Qed.

Global Instance ouPred_later_contractive {M} : BiLaterContractive (ouPredI M).
Proof.
  exact: @later_contractive.
Qed.

Global Instance ouPred_sbi_emp_valid_exist {M} : SbiEmpValidExist (ouPredI M).
Proof. exact: @si_emp_valid_exist_1. Qed.

#[export] Instance ouPred_pure_forall {M} : BiPureForall (ouPredI M).
Proof.
  intros A φ. etrans; [apply si_pure_forall_2|].
  apply si_pure_mono, pure_forall_2.
Qed.

#[export] Instance ouPred_persistently_forall {M} : BiPersistentlyForall (ouPredI M).
Proof. rewrite /BiPersistentlyForall. ouPred_unseal.unseal. done. Qed.

Module ouPred.
Section ouPred.
Context {M : uora}.
Implicit Types φ : Prop.
Implicit Types P Q : ouPred M.
Implicit Types A : Type.
Arguments ouPred_holds {_} !_ _ _ /.
Hint Immediate ouPred_in_entails : core.

Global Instance ownM_ne : NonExpansive (@ouPred_ownM M).
Proof.
  intros n a b Ha.
  ouPred_unseal.unseal; split=> n' x ? /=. rewrite (dist_le _ _ _ _ Ha) //.
Qed.
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@ouPred_ownM M) := ne_proper _.

Lemma bupd_ne : NonExpansive (@ouPred_bupd M).
Proof.
  intros n P Q HPQ.
  ouPred_unseal.unseal; split=> n' x; split; intros HP k yf ??;
    destruct (HP k yf) as (x'&?&?); auto;
    exists x'; split; auto; apply HPQ; eauto; eapply (cmra_validN_op_l(A:=M)); eauto.
Qed.

(** BI instances *)

(** Limits *)
Lemma entails_lim (cP cQ : chain (ouPredO M)) :
  (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
Proof.
  intros Hlim; split=> n m ? HP.
    eapply ouPred_holds_ne, Hlim; [..|apply: HP]; rewrite ?conv_compl; eauto.
Qed.

(** Basic update modality *)
Notation "|==> P" := (ouPred_bupd P) : bi_scope.

Lemma bupd_intro P : P ⊢ |==> P.
Proof.
  ouPred_unseal.unseal. split=> n x ? HP k yf ?; exists x; split; first done.
  apply ouPred_mono with n x; eauto using cmra_validN.
Qed.
Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
Proof.
  ouPred_unseal.unseal. intros HPQ; split=> n x ? HP k yf ??.
  destruct (HP k yf) as (x'&?&?); eauto.
  exists x'; split; eauto.
  eapply ouPred_in_entails; eauto.
  eapply (cmra_validN_op_l(A:=M)); eauto.
Qed.
Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P.
Proof. ouPred_unseal.unseal; split; naive_solver. Qed.
Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R.
Proof.
  ouPred_unseal.unseal; split; intros n x ? (x1&x2&Hx&HP&?) k yf ??.
  eapply ora_validN_orderN in H2; last by eapply ora_monoN_r, ora_orderN_le; [done | simpl; lia].
  destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto.
  { by rewrite assoc. }
  exists (x' ⋅ x2); split; first by rewrite -assoc.
  exists x', x2. eauto using ouPred_mono, cmra_validN_op_l, cmra_validN_op_r.
Qed.

(* Own *)
Lemma ownM_op (a1 a2 : M) :
  ouPred_ownM (a1 ⋅ a2) ⊣⊢ ouPred_ownM a1 ∗ ouPred_ownM a2.
Proof.
  rewrite /bi_sep /=; ouPred_unseal.unseal. split=> n x ?; split; simpl; eauto.
  intros (x1&x2&Hx&Ha1&Ha2).
  setoid_rewrite <- Hx. etrans; first eapply ora_orderN_op; eauto.
  rewrite !(comm op x1); etrans; first eapply ora_orderN_op; eauto.
Qed.
Lemma persistently_ownM_core (a : M) :
  ouPred_ownM a ⊢ bi_persistently (ouPred_ownM (core a)).
Proof.
  rewrite /bi_persistently /=. ouPred_unseal.unseal.
  split=> n x Hx /=. by apply ora_core_monoN.
Qed.
Lemma ownM_unit : ⊢ ouPred_ownM (ε:M).
Proof. ouPred_unseal.unseal; split=> n x ? ?; done. Qed.

Lemma ownM_unit_discard : ouPred_ownM (ε:M) ⊢ emp.
Proof. ouPred_unseal.unseal; split=> n x ? ?; done. Qed.

Lemma ownM_core_discard (a : M) : ouPred_ownM (core a) ⊢ emp.
Proof. ouPred_unseal.unseal; split=> n x ? ?.
  unfold ouPred_ownM_def in *; simpl in *.
  etrans; last done.
  apply ora_order_orderN, uora_unit_order_core.
Qed.

Lemma later_ownM (a : M) : ▷ ouPred_ownM a ⊢ ∃ b, ouPred_ownM b ∧ ▷ (a ≡ b).
Proof.
  rewrite /internal_eq /si_pure /sbi_si_pure /ouPred_si_pure; ouPred_unseal.unseal; siProp_primitive.unseal.
  split=> -[|n] x /= ? Hax; first by eauto using ucmra_unit_leastN.
  destruct (ora_extend n x a) as (a'&Hx&?); auto using cmra_validN_S.
  exists a'. symmetry in H. auto.
Qed.

Lemma ownM_order (a b : M) :
  a ≼ₒ b -> ouPred_ownM b ⊢ ouPred_ownM a.
Proof.
  rewrite ora_order_orderN.
  split => ???; ouPred_unseal.unseal.
  etrans; eauto.
Qed.

Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  cmra_updateP(A := uora_oraR M) x Φ → ouPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ ouPred_ownM y.
Proof.
  ouPred_unseal.unseal=> Hup; split=> n x2 ? /= Hx k yf ? Hxy.
  eapply ora_validN_orderN in Hxy; last (eapply ora_monoN_r, ora_orderN_le; [done | simpl; lia]).
  destruct (Hup k (Some yf)) as (y&?&?); simpl in *; first done.
  rewrite /ouPred_pure; ouPred_unseal.unseal; siProp_primitive.unseal.
  eexists; split=>//.
  eexists; split=>//; auto.
Qed.

Lemma ownM_valid' (a : M) : ouPred_ownM a ⊢ <si_pure> siProp_cmra_valid(A := ora_cmraR _) a.
Proof.
  rewrite /si_pure /sbi_si_pure; ouPred_unseal.unseal; siProp_primitive.unseal.
  split=> n x Hv H; ofe_subst.
  by eapply ora_validN_orderN.
Qed.

Lemma bupd_si_pure Pi : (|==> <si_pure> Pi : ouPred M) ⊢ <si_pure> Pi.
Proof.
  rewrite /si_pure /sbi_si_pure /ouPred_si_pure; ouPred_unseal.unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
Qed.

(* Basic update modality *)
Lemma ouPred_bupd_mixin : BiBUpdMixin (ouPredI M) ouPred_bupd.
Proof.
  split.
  - exact: bupd_ne.
  - exact: bupd_intro.
  - exact: bupd_mono.
  - exact: bupd_trans.
  - exact: bupd_frame_r.
Qed.
Global Instance ouPred_bi_bupd : BiBUpd (ouPredI M) := {| bi_bupd_mixin := ouPred_bupd_mixin |}.

Global Instance ouPred_bi_bupd_sbi : BiBUpdSbi (ouPredI M).
Proof. exact: bupd_si_pure. Qed.

Section restate.
  
  (** Re-exporting primitive lemmas that are not in any interface *)
  Lemma ownM_valid (a : M) : ouPred_ownM a ⊢ ✓ (a : ora_cmraR _).
  Proof. exact: ownM_valid'. Qed.

  (** We restate the unsealing lemmas for the BI layer. The sealing lemmas
  are partially applied so that they also rewrite under binders. *)
  Local Lemma ouPred_emp_unseal :
    bi_emp = @ouPred_emp M.
  Proof. done. Qed.
  Local Lemma ouPred_pure_unseal :
    bi_pure = λ φ, @ouPred_si_pure_def M (siprop.siProp_pure_def φ).
  Proof. by rewrite -ouPred_si_pure_unseal -siprop.siProp_pure_unseal. Qed.
  Local Lemma ouPred_si_pure_unseal : si_pure = @ouPred_si_pure_def M.
  Proof. by rewrite -ouPred_si_pure_unseal. Qed.
  Local Lemma ouPred_si_emp_valid_unseal :
    si_emp_valid = @ouPred_si_emp_valid_def M.
  Proof. by rewrite -ouPred_si_emp_valid_unseal. Qed.
  Local Lemma ouPred_and_unseal : bi_and = @ouPred_and_def M.
  Proof. by rewrite -ouPred_and_eq. Qed.
  Local Lemma ouPred_or_unseal : bi_or = @ouPred_or_def M.
  Proof. by rewrite -ouPred_or_eq. Qed.
  Local Lemma ouPred_impl_unseal : bi_impl = @ouPred_impl_def M.
  Proof. by rewrite -ouPred_impl_eq. Qed.
  Local Lemma ouPred_forall_unseal : @bi_forall _ = @ouPred_forall_def M.
  Proof. by rewrite -ouPred_forall_eq. Qed.
  Local Lemma ouPred_exist_unseal : @bi_exist _ = @ouPred_exist_def M.
  Proof. by rewrite -ouPred_exist_eq. Qed.
  Local Lemma ouPred_sep_unseal : bi_sep = @ouPred_sep_def M.
  Proof. by rewrite -ouPred_sep_eq. Qed.
  Local Lemma ouPred_wand_unseal : bi_wand = @ouPred_wand_def M.
  Proof. by rewrite -ouPred_wand_eq. Qed.
  Local Lemma ouPred_persistently_unseal :
    bi_persistently = @ouPred_persistently_def M.
  Proof. by rewrite -ouPred_persistently_eq. Qed.
  Local Lemma ouPred_later_unseal : bi_later = @ouPred_later_def M.
  Proof. by rewrite -ouPred_later_eq. Qed.
  Local Lemma ouPred_bupd_unseal : bupd = @ouPred_bupd_def M.
  Proof. by rewrite -ouPred_bupd_unseal. Qed.

  Local Definition ouPred_unseal :=
    (ouPred_emp_unseal, ouPred_pure_unseal,
    ouPred_si_pure_unseal, ouPred_si_emp_valid_unseal,
    ouPred_and_unseal, ouPred_or_unseal,
    ouPred_impl_unseal, ouPred_forall_unseal, ouPred_exist_unseal,
    ouPred_sep_unseal, ouPred_wand_unseal,
    ouPred_persistently_unseal, ouPred_later_unseal,
    ouPred_ownM_eq, @ouPred_bupd_unseal).
End restate.
End ouPred.

(** A tactic for rewriting with the above lemmas. Unfolds [ouPred] goals that use
the BI layer. *)
Ltac unseal := rewrite !ouPred_unseal /=.
End ouPred.
