Add LoadPath "C:\Users\ljt12138\Desktop\2019秋\Coq\Discrete-Calculus-for-Coq".
Require Import Reals.
Require Import omega.Omega.
Require Import ArithProp.
Require Import Program.Basics.
Require Export Coq.Reals.RIneq.
Require Export fcal.
Open Scope R_scope.

Lemma seq_div_mult_l : forall s r,
  r <> 0 -> s = (1 / r) \* r \* s.
Proof.
  intros s r H.
  trivial_seq.
  assumption.
Qed.

Lemma seq_mult_div_l : forall s r,
  r <> 0 -> s = r \* (1 / r) \* s.
Proof.
  intros s r H.
  trivial_seq.
  assumption.
Qed.

  