Require Import Reals.
Require Import ArithProp.
Require Import Lra.

Open Scope R_scope.

Fixpoint N2R (n : nat) :=
  match n with 
  | O => 0
  | S n' => 1 + (N2R n')
  end.

Section N2R_lemma.

  Lemma N2R_ge_0 : forall n, N2R n >= 0.
  Proof.
    induction n.
    - simpl ; apply Rge_refl.
    - simpl. 
      assert (1 + (-1) = 0) as H1. ring. rewrite <- H1.
      apply Rplus_ge_compat_l.
      eapply Rge_trans.
      + apply IHn.
      + lra.
  Qed.
  Hint Resolve N2R_ge_0: real.

End N2R_lemma.
