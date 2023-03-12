From stdpp Require Export list gmap.
From iris.algebra Require Export list cmra.
From iris.algebra Require Import gset gmap.
From iris.algebra Require Import updates local_updates proofmode_classes big_op.
From iris.prelude Require Import options.
From iris_ora.algebra Require Export ora.

Section ora.

Context `{Countable K} {A : ora}.
Implicit Types m : gmap K A.

Instance gmap_orderN : OraOrderN (gmap K A) := λ n, map_relation (ora_orderN A n) (λ _, False) Increasing.
Instance gmap_order : OraOrder (gmap K A) := map_relation (ora_order A) (λ _, False) Increasing.

Lemma lookup_increasing : forall m i, Increasing m -> Increasing (m !! i).
Proof.
  intros ?? Hincr [a|].
  - specialize (Hincr {[ i := a ]} i).
    by rewrite lookup_op lookup_singleton in Hincr.
  - specialize (Hincr ε i).
    by rewrite lookup_op lookup_empty in Hincr.
Qed.

Definition gmap_ora_mixin : OraMixin (gmapR K A).
Proof.
  apply ora_total_mixin; try apply _; try done.
  - intros ???; simpl.
    rewrite lookup_op lookup_core.
    eapply (@ora_core_increasing (optionR A)), _.
  - intros ??? Hincr Hord z i.
    rewrite lookup_op; eapply (@ora_increasing_closed (optionR A)), Hord.
    by apply lookup_increasing.
  - intros ??? Hord i.
    rewrite !lookup_core.
    specialize (Hord i).
    apply (ora_core_monoN n (x !! i)); auto.
  - intros ???? Hx Hord.
    hnf in Hord.
    setoid_rewrite lookup_op in Hord.
    assert (FUN := λ i, ora_op_extend n (x !! i) (y1 !! i) (y2 !! i) (Hx i) (Hord i)).
    exists (map_imap (λ x _, projT1 (FUN x)) x), (map_imap (λ x _, proj1_sig (projT2 (FUN x))) x).
    split; [|split]=>i; [rewrite lookup_op| |]; rewrite !map_lookup_imap;
      destruct (FUN i) as (z1&z2&?&?&?); destruct (x !! i) eqn: Hi; rewrite Hi; try done; simpl.
    + destruct (z1 ⋅ z2) eqn: Hop; try contradiction.
      apply op_None in Hop as []; subst; auto.
    + destruct (z1 ⋅ z2) eqn: Hop; try contradiction.
      apply op_None in Hop as []; subst; auto.
  - intros ??? Hx Hord.
    assert (FUN := λ i, ora_extend n (x !! i) (y !! i) (Hx i) (Hord i)).
    exists (map_imap (λ x _, proj1_sig (FUN x)) x).
    split=>i; rewrite !map_lookup_imap;
      destruct (FUN i) as (z&?&?); destruct (x !! i) eqn: Hi; rewrite Hi; try done; simpl.
    destruct z; done.
  - intros ?????.
    apply (@ora_dist_orderN (optionR A)); auto.
  - intros ??? Hord i.
    apply (@ora_orderN_S (optionR A)), Hord.
  - intros ???? Hxy Hyz i.
    eapply (@ora_orderN_trans (optionR A)); [apply Hxy | apply Hyz].
  - intros ???? Hord i.
    rewrite !lookup_op.
    eapply (@ora_orderN_op (optionR A)), Hord.
  - intros ???? Hord i.
    eapply (@ora_validN_orderN (optionR A)), Hord; auto.
  - split; intros; intros i; eapply (@ora_order_orderN (optionR A)).
    + apply H0.
    + intros; apply H0.
  - intros ??? Hcx.
    eexists; split; [constructor; reflexivity|].
    inversion Hcx as [?? Heq|]; subst.
    intros i.
    rewrite -Heq !lookup_omap lookup_op.
    edestruct (ora_pcore_order_op (x !! i)) as (? & Hcore & ?).
    { constructor; reflexivity. }
    inversion Hcore as [?? Hxy|]; subst.
    by rewrite Hxy.
Qed.
Canonical Structure gmapR : ora := Ora (gmap K A) gmap_ora_mixin.

Global Instance gmap_ora_total : OraTotal gmapR.
Proof. rewrite /OraTotal; eauto. Qed.

Canonical Structure gmapUR : uora := Uora (gmap K A) (gmap_ucmra_mixin(H := H)(A := A)).

End ora.

Global Arguments gmapR _ {_ _} _.
Global Arguments gmapUR _ {_ _} _.

Section properties.
Context `{Countable K} {A : ora}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Global Instance gmap_core_id m : (∀ x : A, OraCoreId x) → OraCoreId m.
Proof.
  intros; apply core_id_total=> i.
  rewrite lookup_core. apply (core_id_core _).
Qed.
Global Instance gmap_singleton_core_id i (x : A) :
  OraCoreId x → OraCoreId {[ i := x ]}.
Proof. intros. by apply core_id_total, (singleton_core'(A := A)). Qed.

End properties.

Global Instance gmap_fmap_ora_morphism `{Countable K} {A B : ora} (f : A → B)
  `{!OraMorphism f} : OraMorphism (fmap f : gmap K A → gmap K B).
Proof.
  split; try apply _.
  - by intros n m ? i; rewrite lookup_fmap; apply (ora_morphism_validN _).
  - intros ??? Hord ?.
    rewrite !lookup_fmap.
    apply option_fmap_ora_morphism, Hord; auto.
  - intros ? Hincr ??.
    rewrite lookup_op lookup_fmap.
    apply option_fmap_ora_morphism; auto.
    by apply lookup_increasing.
  - intros m. apply Some_proper=>i. rewrite lookup_fmap !lookup_omap lookup_fmap.
    case: (m!!i)=>//= ?. apply ora_morphism_pcore, _.
  - intros m1 m2 i. by rewrite lookup_op !lookup_fmap lookup_op ora_morphism_op.
Qed.

Program Definition gmapURF K `{Countable K} (F : OrarFunctor) : uorarFunctor := {|
  uorarFunctor_car A _ B _ := gmapUR K (orarFunctor_car F A B);
  uorarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (orarFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, orarFunctor_map_ne.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply orarFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply orarFunctor_map_compose.
Qed.

Global Instance gmapURF_contractive K `{Countable K} F :
  OrarFunctorContractive F → uorarFunctorContractive (gmapURF K F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, orarFunctor_map_contractive.
Qed.

Program Definition gmapRF K `{Countable K} (F : OrarFunctor) : OrarFunctor := {|
  orarFunctor_car A _ B _ := gmapR K (orarFunctor_car F A B);
  orarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (orarFunctor_map F fg)
|}.
Solve Obligations with apply gmapURF.

Global Instance gmapRF_contractive K `{Countable K} F :
  OrarFunctorContractive F → OrarFunctorContractive (gmapRF K F).
Proof. apply gmapURF_contractive. Qed.
