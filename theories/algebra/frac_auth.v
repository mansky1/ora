From iris.algebra Require Export frac_auth.
From iris_ora.algebra Require Export auth.
From iris_ora.algebra Require Import ext_order.
From iris.prelude Require Import options.

Lemma frac_positive : forall (a : Qp), ~a ≡ a ⋅ a.
Proof.
  intros; rewrite frac_op.
  by intros H; symmetry in H; apply Qp.add_id_free in H.
Qed.

Canonical Structure fracR := ext_order.positiveR frac_positive.

Section frac_auth.

Context {A : ora} (Ha : forall n (x y : A), ✓{n} y → x ≼ₒ{n} y → x ≡{n}≡ y).

Lemma auth_frac_rel_order : forall n (x y : optionUR (prodR fracR A)), ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
Proof using Ha.
  intros ??? Hv [(-> & ?) | (xa & xb & -> & -> & H)]%option_orderN'.
  - rewrite option_includedN; auto.
  - rewrite option_includedN; right.
    destruct xa, xb, H as [Heq H], Hv; simpl in *; hnf in Heq; subst.
    apply Ha in H; last done.
    eexists _, _; split; first done; split; first done.
    left; split; auto.
Qed.

Definition frac_authR := authR _ auth_frac_rel_order.
Definition frac_authUR := authUR _ auth_frac_rel_order.

End frac_auth.

Notation "●F a" := (@frac_auth_auth (ora_cmraR _) a) (at level 10).
Notation "◯F{ q } a" := (@frac_auth_frag (ora_cmraR _) q a) (at level 10, format "◯F{ q }  a").
Notation "◯F a" := (@frac_auth_frag (ora_cmraR _) 1 a) (at level 10).

Lemma frac_auth_frag_op : forall {A : ora} (q1 q2 : Qp) (a1 a2 : A),
  ◯F{q1 + q2} (a1 ⋅ a2) ≡ ◯F{q1} a1 ⋅ ◯F{q2} a2.
Proof.
  intros; apply frac_auth_frag_op.
Qed.
