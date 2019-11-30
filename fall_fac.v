Add LoadPath "C:\Users\ljt12138\Desktop\2019秋\Coq\Discrete-Calculus-for-Coq".
Require Import Reals.
Require Export fcal.
Open Scope R_scope.

Fixpoint Ffac (n : nat) (x : R) :=
  match n with
  | O => 1
  | S n' => x * (Ffac n' (x - 1))
  end.

Notation "[ x ] ^n" := (pow x) (at level 19).
Notation "(x)^ [ n ]" := (fun x => pow x n) (at level 19).
Notation "x↓ [ n ]" := (Ffac n) (at level 19).
Notation "[ x ] ↓n" := (fun n => Ffac n x) (at level 19).

Lemma Delta_fixpoint : Δ[[2]^n] = [2]^n.
Proof.
  unfold Delta.
  rewrite Sub_app_distr.
  unfold Id.
  trivial_seq ; unfold E ; simpl.
  field.
Qed.
