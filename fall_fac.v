Add LoadPath "C:\Users\ljt12138\Desktop\2019秋\Coq\Discrete-Calculus-for-Coq".
Require Import Reals.
Require Import omega.Omega.
Require Export fcal.
Open Scope R_scope.

Fixpoint N2R (n : nat) :=
  match n with 
  | O => 0
  | S n' => 1 + (N2R n')
  end.

Fixpoint Ffac (n : nat) (x : nat) :=
  match n with
  | O => 1
  | S n' => N2R(x) * (Ffac n' (x - 1))
  end.

Fixpoint Npow (n : nat) (x : R) :=
  match n with 
  | O => 1
  | S n' => x * (Npow n' x)
  end.

Notation "[ x ] ^n" := (pow x) (at level 19).
Notation "x^ [ n ]" := (fun (x : nat) => Npow x n) (at level 19).
Notation "x↓ [ n ]" := (Ffac n) (at level 19).
Notation "[ x ] ↓n" := (fun n => Ffac n x) (at level 19).

Ltac open_delta := 
    unfold Delta;
    unfold E;
    unfold Id.

Section Ffac_lemma.

  (*x (x - 1) (x - 2) ... (x - n + 1)
   (x + 1) x (x - 1) ... (x - n + 2) *)

  Lemma Unfold_Ffac : forall n n0,
    x↓[S n][n0] = N2R(n0) * x↓[n][(n0 - 1)%nat].
  Proof.
    induction n.
    - intros ; simpl ; ring.
    - intros ; rewrite IHn.
      simpl ; reflexivity.
  Qed.

  Lemma Unfold_Ffac_n0 : forall n n0, 
    x↓[S n][S n0] = (1 + N2R[n0]) * x↓[n][n0].
  Proof.
    destruct n.
    - intros n0 ; simpl ; ring.
    - intros n0. 
      rewrite Unfold_Ffac.
      simpl.
      rewrite Nat.sub_0_r.
      reflexivity.
  Qed.

  Lemma Ffac_0 : forall n,
    x↓[S n] 0%nat = 0.
  Proof.
    intros ; simpl ; field.
  Qed.

  Lemma Delta_lemma_1 : forall (n n1 : nat),
    (x↓[n]) (S [n1]) - (x↓[n]) n1 = Δ[x↓[n]] n1.
  Proof. trivial_op. Qed.

  Theorem Delta_Ffac : forall n, 
    Δ[x↓[n]] = N2R(n) \* (x↓[n - 1]).
  Proof.
    intros n.
    induction n.
    - open_delta ; unfold Ffac ; trivial_op.
      simpl ; ring.
    - (* simplify carefully *)
      unfold Delta; rewrite Sub_app_distr.
      unfold E; unfold Id; trivial_seq.
      assert (forall n, (S [n] - 1 = n)%nat) as H1. 
      { intuition. }
      rewrite H1.
      repeat (rewrite Unfold_Ffac).
      repeat (rewrite H1) ; simpl.
      repeat (rewrite (Rmult_plus_distr_r)).
      assert (forall a b c, a + b - c = a + (b - c)) as H2.
      { intros ; field. }
      rewrite H2.
      apply Rplus_eq_compat_l.
      rewrite <- Rmult_minus_distr_l.
      (* case on n0 is necessary *)
      case n0.
      + simpl ; case n ; simpl ; try (intros) ; ring.
      + intros n1 ; simpl.
        (* do some rewrite, in order to use IHn *)
        assert ((x↓[n]) (S [n1]) - (x↓[n]) (n1 - 0)%nat = Δ[x↓[n]] n1) as H3.
        { rewrite Nat.sub_0_r. trivial_op. }
        rewrite H3 ; rewrite IHn ; trivial_op.
        rewrite <- Rmult_assoc.
        rewrite (Rmult_comm _ (N2R[n])).
        rewrite Rmult_assoc.
        (* when n = 0, we can not simply remove N2R[n] in both sides*)
        case n.
        * simpl ; ring.
        * intros n2.
          rewrite Unfold_Ffac_n0 ; simpl.
          rewrite Nat.sub_0_r.
          reflexivity.
  Qed.

End Ffac_lemma.

Section Npow_lemma.

End Npow_lemma.

Section Nexp_lemma.

Lemma Delta_fixpoint : Δ[[2]^n] = [2]^n.
Proof.
  unfold Delta.
  rewrite Sub_app_distr.
  unfold Id.
  trivial_seq ; unfold E ; simpl.
  field.
Qed.

End Nexp_lemma.