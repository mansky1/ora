From iris.algebra.lib Require Export excl_auth.
From iris_ora.algebra Require Export excl auth.
From iris.prelude Require Import options.

Lemma excl_rel_order : ∀ {SI : sidx} {A : ofe} n (x y : optionUR (exclR A)), ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
Proof.
  intros ?????? [(-> & ?) | (? & ? & -> & -> & H)]%option_orderN'.
  - rewrite option_includedN; auto.
  - rewrite option_includedN; eauto 7.
Qed.

Definition excl_authR {SI : sidx} (A : ofe) := authR _ (@excl_rel_order _ A).
Definition excl_authUR {SI : sidx} (A : ofe) := authUR _ (@excl_rel_order _ A).
