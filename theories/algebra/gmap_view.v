From iris.algebra Require Export gmap_view.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From iris_ora.algebra Require Export gmap view.
From iris.prelude Require Import options.

Section gmap_view.
  Context {SI : sidx} K `{Countable K} (V : ofe).
  (* This isn't fixed to agree in base Iris, but we do need to know that the ORA order implies
     inclusion, so for now keeping agree. *)
  Local Definition gmap_view_fragUR : uora := gmapUR K (prodR dfracR (agreeR V)).

  Local Lemma gmap_view_rel_order: ∀ n (a : gmapO K (agree V)) (x y : gmap_view_fragUR),
    x ≼ₒ{n} y → gmap_view.gmap_view_rel _ _ n a y → gmap_view.gmap_view_rel _ _ n a x.
  Proof.
    intros ???? Hord Hy i (?, ?) Hxi.
    specialize (Hord i); rewrite Hxi in Hord.
    destruct (y !! i) as [(?, ?)|] eqn: Hyi; rewrite Hyi in Hord; simpl in Hord; last done.
    destruct Hord as [Hd Hv]; simpl in *.
    specialize (Hy _ _ Hyi); destruct Hy as (? & ? & Ha & Hvalid & Ho).
    eexists _, _; split; [|split]; try done.
    etrans; last apply Ho.
    rewrite Some_includedN.
    eapply cmra_validN_Some_includedN in Hvalid as (? & ?); last done; simpl in *.
    apply agree_order_dist in Hv; last done.
    destruct Hd; subst.
    - left; split; auto.
    - right; apply (pair_includedN(A := dfracR)); split.
      + by eexists.
      + by rewrite Hv.
  Qed.
End gmap_view.

Canonical Structure gmap_viewR {SI : sidx} (K : Type) `{Countable K} (V : ofe) : ora :=
  view.viewR (gmap_view.gmap_view_rel K (iris.algebra.agree.agreeR V)) (gmap_view_rel_order K V).
Canonical Structure gmap_viewUR {SI : sidx} (K : Type) `{Countable K} (V : ofe) : uora :=
  viewUR (gmap_view.gmap_view_rel K (iris.algebra.agree.agreeR V)).

Section instances.
  Context {SI : sidx} K `{Countable K} (V : ofe).
  (** Typeclass instances *)
  Global Instance gmap_view_frag_core_id (k : K) dq (v : iris.algebra.agree.agreeR V) : OraCoreId dq → OraCoreId (gmap_view_frag k dq v).
  Proof. intros; apply (gmap_view_frag_core_id(V := iris.algebra.agree.agreeR V)); [done | apply _]. Qed.
  
  Global Instance gmap_view_ora_discrete : OfeDiscrete V → OraDiscrete (gmap_viewR K V).
  Proof.
    intros; apply view_ora_discrete; try apply _.
    apply gmap_view.gmap_view_rel_discrete, _.
  Qed.
End instances.

(** Functor *)
Program Definition gmap_viewURF {SI : sidx} (K : Type) `{Countable K} (F : oFunctor) : uorarFunctor := {|
  uorarFunctor_car A _ B _ := gmap_viewUR K (oFunctor_car F A B);
  uorarFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view.gmap_view_rel K (iris.algebra.agree.agreeR (oFunctor_car F A1 B1)))
              (rel':=gmap_view.gmap_view_rel K (iris.algebra.agree.agreeR (oFunctor_car F A2 B2)))
              (gmapO_map (K:=K) (agreeO_map (oFunctor_map F fg)))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Next Obligation.
  intros ? K ?? F A1 ? A2 ? B1 ? B2 ?? f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, agreeO_map_ne, oFunctor_map_ne. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_ne. done.
Qed.
Next Obligation.
  intros ? K ?? F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ??.
    rewrite agree_map_ext; first by setoid_rewrite agree_map_id.
    intros; apply oFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -{2}(agree_map_id va).
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_id.
Qed.
Next Obligation.
  intros ? K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k ??.
    rewrite agree_map_ext; last by apply oFunctor_map_compose.
    by rewrite agree_map_compose.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -agree_map_compose.
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_compose.
Qed.
Next Obligation.
  intros ? K ?? F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  apply: view_map_ora_morphism; [apply _..|]=> n m f.
  intros Hrel k [df va] Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.
  simpl=>[= <- <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel.
  destruct Hrel as (v & dq & Hlookup & Hval & Hincl).
  exists (agree_map (oFunctor_map F fg) v), dq.
  rewrite Hlookup. split; first done. split.
  - split; first by apply Hval. simpl. apply: cmra_morphism_validN. apply Hval.
  - destruct Hincl as [[[fdq fv]|] Hincl].
    + apply: Some_includedN_mono. rewrite -Some_op in Hincl.
      apply (inj _) in Hincl.
      exists (fdq, agree_map (oFunctor_map F fg) fv).
      split; first apply Hincl.
      simpl. rewrite -cmra_morphism_op. f_equiv. apply Hincl.
    + exists None. rewrite right_id in Hincl. apply (inj _) in Hincl.
      rewrite right_id. f_equiv. split; first apply Hincl.
      simpl. f_equiv. apply Hincl.
Qed.

Global Instance gmap_viewURF_contractive {SI : sidx} (K : Type) `{Countable K} F :
  oFunctorContractive F → uorarFunctorContractive (gmap_viewURF K F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply agreeO_map_ne, oFunctor_map_contractive. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_contractive. done.
Qed.

Program Definition gmap_viewRF {SI : sidx} (K : Type) `{Countable K} (F : oFunctor) : OrarFunctor := {|
  orarFunctor_car A _ B _ := gmap_viewR K (oFunctor_car F A B);
  orarFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view.gmap_view_rel K (iris.algebra.agree.agreeR (oFunctor_car F A1 B1)))
              (rel':=gmap_view.gmap_view_rel K (iris.algebra.agree.agreeR (oFunctor_car F A2 B2)))
              (gmapO_map (K:=K) (agreeO_map (oFunctor_map F fg)))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Solve Obligations with apply @gmap_viewURF.

Global Instance gmap_viewRF_contractive {SI : sidx} (K : Type) `{Countable K} F :
  oFunctorContractive F → OrarFunctorContractive (gmap_viewRF K F).
Proof. apply gmap_viewURF_contractive. Qed.
