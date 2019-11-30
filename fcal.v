Require Import Reals.
Require Import omega.Omega.
Require Import ArithProp.
Require Import Program.Basics.
Require Export Coq.Reals.RIneq.
Open Scope R_scope.

Notation "a [ b ]" := (a b) (at level 30).

Definition Sequence := nat -> R.
Definition Add (L L' : Sequence) :=
  fun n => L[n] + L'[n].
Definition Scale (a : R) (L : Sequence) :=
  fun n => a * L[n].
Definition Sub (L L' : Sequence) :=
  fun n => L[n] - L'[n].
Definition Dot (L L' : Sequence) :=
  fun n => L[n] * L'[n].

Definition Zs : Sequence := fun n => 0.
Definition Os : Sequence := fun n => 1.
Definition Is : Sequence := fun n => INR n.
Definition δ : Sequence := fun n => 
    match n with 
    | O => 1
    | S n' => 0
    end.

Notation "a \+ b" := (Add a b) (at level 29, left associativity).
Notation "a \- b" := (Sub a b) (at level 29, left associativity).
Notation "a \* b" := (Scale a b) (at level 19, right associativity).
Notation "a \o b" := (Dot a b) (at level 19, right associativity).

Axiom eq_extension_seq : forall L L' : Sequence,
    (forall n, L[n] = L'[n]) -> L = L'.

Ltac equality := apply eq_extension_seq ; intros.
Ltac trivial_seq := try (intros ) ;
                    try (equality) ;
                    try (unfold Add) ;
                    try (unfold Sub) ;
                    try (unfold Scale) ;
                    try (unfold Dot) ; 
                    try (intuition) ;
                    try (field).

Section Sequence_lemma.
  
  Lemma Add_comm : forall L L', L \+ L' = L' \+ L.
  Proof. trivial_seq. Qed.

  Lemma Add_assoc : forall L L' L'',
      L \+ L' \+ L'' = L \+ (L' \+ L'').
  Proof. trivial_seq. Qed.

  Lemma Dot_comm : forall L L', L \o L' = L' \o L.
  Proof. trivial_seq. Qed.

  Lemma Dot_assoc : forall L L' L'',
      L \o L' \o L'' = L \o (L' \o L'').
  Proof. trivial_seq. Qed.

  Lemma Scale_assoc : forall c c' L ,
      c \* c' \* L = (c * c') \* L.
  Proof. trivial_seq. Qed.

  Lemma Scale_1 : forall L,
      1 \* L = L.
  Proof. trivial_seq. Qed.

  Lemma Scale_Zs : forall c,
      c \* Zs = Zs.
  Proof. trivial_seq. Qed.
  
  Lemma Dot_Add_distr_l : forall L L' L'',
      L \o (L' \+ L'') = L \o L' \+ L \o L''.
  Proof. trivial_seq. Qed.
  
  Lemma Scale_Add_distr : forall c L L',
      c \* (L \+ L') = c \* L \+ c \* L'.
  Proof. trivial_seq. Qed.         
    
  Lemma Zs_id : forall L, Zs \+ L = L.
  Proof. trivial_seq. Qed.

  Lemma Os_id : forall L, Os \o L = L.
  Proof. trivial_seq. Qed.
  
End Sequence_lemma.

Definition Operator := Sequence -> Sequence.

Definition E (L : Sequence) :=
  fun n => L (S n).
Definition Id (L : Sequence) := L.
Definition Zp (L : Sequence) :=
  fun (n : nat) => 0.

Definition Add_op (O O' : Operator) :=
  fun L => (O L) \+ (O' L).
Definition Sub_op (O O' : Operator) :=
  fun L => (O L) \- (O' L).
Definition Scale_op (r : R) (O : Operator) :=
  fun L => r \* (O L).

Notation "a \\+ b" := (Add_op a b) (at level 29, left associativity).
Notation "a \\- b" := (Sub_op a b) (at level 29, left associativity).
Notation "a \\* b" := (Scale_op a b) (at level 15, right associativity).

Definition Delta := E \\- Id.

Axiom eq_extension_op : forall O O' : Operator,
    (forall L, O L = O' L) -> O = O'.

Definition Linear O : Prop :=
  forall r L L', O (r \* L \+ L') = r \* (O L) \+ (O L').

Ltac simpl_linear := intros ; unfold Linear.
Ltac trivial_op := try (intros) ;
                   try (unfold Linear in *) ;
                   try (simpl_linear) ;
                   try (apply eq_extension_op) ;
                   try (unfold Add_op) ;
                   try (unfold Sub_op) ;
                   try (unfold Scale_op) ;
                   try (trivial_seq) ; 
                   try (field).

Section Operator_lemma.

  Lemma Add_comm_op : forall O O', O \\+ O' = O' \\+ O.
  Proof. trivial_op. Qed.

  Lemma Add_assoc_op : forall O O' O'',
      O \\+ O' \\+ O'' = O \\+ (O' \\+ O'').
  Proof. trivial_op. Qed.

  Lemma Scale_assoc_op : forall c c' O ,
      c \\* c' \\* O = (c * c') \\* O.
  Proof. trivial_op. Qed.

  Lemma Scale_Add_distr_op : forall c O O',
      c \\* (O \\+ O') = c \\* O \\+ c \\* O'.
  Proof. trivial_op. Qed.         

  Lemma Scale_app_op : forall c O L,
      c \* (O L) = (c \\* O) L.
  Proof. reflexivity. Qed.
  
  Lemma Zp_id_op : forall L, Zp \\+ L = L.
  Proof. trivial_op. Qed.
  
  Lemma E_linear : Linear E.
  Proof. trivial_op. Qed.

  Lemma Id_linear : Linear Id.
  Proof. trivial_op. Qed.

  Lemma Sub_app_distr : forall O O' L,
    (O \\- O') L = O[L] \- (O'[L]).
  Proof. trivial_op. Qed.

  Lemma Id_identical : forall L,
    Id [L] = L.
  Proof. trivial_op. Qed.

  Lemma Dot_sub_distr : forall U V W,
    U \o (V \- W) = U \o V \- U \o W.
  Proof. trivial_op. Qed.

  Lemma E_Dot : forall U V,
    E[U \o V] = E[U] \o (E[V]).
  Proof. trivial_op. Qed.
  
  Lemma linear_plus_linear : forall O O',
      Linear O -> Linear O' ->
      Linear (O \\+ O').
  Proof.
    intros O O' H H'.
    unfold Linear in *.
    simpl_linear.
    unfold Add_op.
    rewrite H ; rewrite H'.
    trivial_seq.
  Qed.

  Lemma linear_scale : forall O c,
      Linear O ->
      Linear (c \\* O).
  Proof.
    intros O c H.
    unfold Linear in *.
    simpl_linear.
    repeat (rewrite <- Scale_app_op).
    rewrite H.
    trivial_seq.
  Qed.
  
  Lemma Sub_by_Add : forall O O',
      O \\- O' = O \\+ (-1) \\* O'.
  Proof. trivial_op. Qed.
  
  Lemma Delta_linear : Linear Delta.
  Proof.
    unfold Delta.
    rewrite Sub_by_Add.
    apply linear_plus_linear.
    - apply E_linear.
    - apply linear_scale.
      apply Id_linear.
  Qed.

  Lemma linear_compose : forall O O',
      Linear O -> Linear O' ->
      Linear (compose O O').
  Proof.
    intros O O' H H'.
    unfold Linear in *.
    simpl_linear.
    unfold compose.
    rewrite H' ; rewrite H.
    reflexivity.
  Qed.

  Lemma linear_Zs : forall O,
      Linear O -> O [Zs] = Zs.
  Proof.
    intros O H.
    rewrite <- (Scale_Zs (-1)).
    rewrite <- (Zs_id ((-1) \* Zs)).
    rewrite Add_comm.
    rewrite H.
    trivial_seq.
  Qed.

  Lemma linear_scale_weaken : forall O,
      Linear O -> forall c L, O [c \* L] = c \\* O [L].
  Proof.
    intros O H c L.
    rewrite <- (Zs_id ((c \\* O) L)).
    rewrite <- (Zs_id L).    
    rewrite Scale_Add_distr.
    rewrite Scale_Zs.
    rewrite (Add_comm Zs).
    rewrite (Add_comm Zs).
    rewrite (Zs_id L).
    unfold Linear in H.
    unfold Scale_op.
    rewrite H.
    rewrite (linear_Zs O).
    - reflexivity.
    - assumption.
  Qed.

  Lemma linear_add_weaken : forall O,
    Linear O -> forall L L', 
      O [L \+ L'] = O [L] \+ (O [L']).
  Proof.
    intros O H L L'. 
    rewrite <- (Scale_1 L).
    rewrite linear_scale_weaken.
    - rewrite H ; reflexivity.
    - assumption.
  Qed.

  Lemma seq_plus_minus : forall P Q,
    P \- Q = P \+ (-1) \* Q.
  Proof. trivial_seq. Qed.

  Lemma linear_minus_weaken : forall O,
    Linear O -> forall L L',
      O [L \- L'] = O[L] \- (O [L']).
  Proof.
    intros O H L L'. 
    repeat (rewrite seq_plus_minus).
    rewrite (Add_comm L _).
    rewrite (Add_comm (O [L]) _).
    apply H.
  Qed.
End Operator_lemma.

Notation "Δ[ L ]" := (Delta L) (at level 5, no associativity).

Section Delta_lemma.

  Lemma Delta_add : forall L L',
    Δ[L \+ L'] = Δ[L] \+ Δ[L'].
  Proof.
    apply linear_add_weaken.
    apply Delta_linear.
  Qed.
  
  Lemma Delta_scale : forall c L,
    Δ[c \* L] = c \* Δ[L].
  Proof.
    apply linear_scale_weaken.
    apply Delta_linear.
  Qed.

  Lemma Delta_dot : forall (U V : Sequence),
    Δ[U \o V] = U \o Δ[V] \+ (E[V]) \o Δ[U].
  Proof.
    intros U V.
    unfold Delta.
    repeat (rewrite Sub_app_distr).
    repeat (rewrite Dot_sub_distr).
    repeat (rewrite Id_identical).
    repeat (rewrite E_Dot).
    rewrite (Dot_comm (E U) (E V)).
    rewrite (Dot_comm U (E V)).
    trivial_seq.
  Qed.
 
End Delta_lemma.

Notation "f , g" := (compose f g) (at level 50, no associativity).

Fixpoint PartialSum (L : Sequence) (n : nat) :=
  match n with
  | O => 0
  | S n => (PartialSum L n) + (L n)
  end.

Notation "Σ[ L ]" := (PartialSum L) (at level 5, no associativity).

Section PartialSum_Delta.

  Lemma E_compose_app : forall (O : Operator) U n,
    E[O[U]][n] = O[U] (S n).
  Proof. trivial_seq. Qed.

  Lemma E_app : forall U n,
    E[U][n] = U[S n].
  Proof. trivial_seq. Qed.

  Lemma PartialSum_minus : forall L n,
    Σ[L][S n] - Σ[L][n] = L n.
  Proof.
    intros L n.
    induction n ; simpl ; field. 
  Qed.

  Lemma Delta_inv : forall L, 
    Δ[Σ[L]] = L.
  Proof.    
    intros L.
    unfold Delta.
    rewrite Sub_app_distr.
    rewrite Id_identical.
    trivial_seq.
    rewrite E_compose_app.
    apply PartialSum_minus.
  Qed.

  Corollary Delta_both_side : forall L L',
    Σ[L] = L' -> L = Δ[L'].
  Proof.
    intros L L' H.
    rewrite <- H.
    rewrite Delta_inv.
    reflexivity.
  Qed.

  Lemma PartialSum_linear : Linear PartialSum.
  Proof.
    simpl_linear ; intros. 
    equality.
    induction n.
    - trivial_seq ; simpl ; field.
    - simpl ; rewrite IHn.
      trivial_seq ; simpl ; field.
  Qed.    

  Lemma PartialSum_split_minus : forall L U,
    Σ[L \- U] = Σ[L] \- Σ[U].
  Proof.
    intros L U.
    apply linear_minus_weaken.
    apply PartialSum_linear.
  Qed.

  Lemma sig_inv_le1 : forall a b c d,
    a + b - (c + d) = a - c + b - d.
  Proof. intros ; field. Qed.

  Lemma Sigma_inv : forall L, 
    Σ[Δ[L]] = L \- (L[0%nat] \* Os).
  Proof.    
    intros L.
    unfold Os.
    unfold Delta.
    rewrite Sub_app_distr.
    rewrite Id_identical.
    equality.
    rewrite PartialSum_split_minus.
    trivial_seq.
    induction n.
    - simpl ; field.
    - simpl. rewrite sig_inv_le1.
      rewrite IHn.
      unfold E.
      field.
  Qed.

  Lemma PSum_delta_Os : Σ[δ] = Os \- δ.
  Proof.
    trivial_seq.
    induction n.
    - unfold Os ; simpl ; field.
    - simpl ; rewrite IHn ; unfold Os.
      field.
  Qed.
  
  Lemma Delta_Is_Os : Δ[Is] = Os.
  Proof. 
    unfold Os ; unfold Is ; unfold Delta.
    trivial_op.
    unfold E ; unfold Id.
    rewrite S_O_plus_INR.
    simpl ; ring.
  Qed.

  Lemma PSum_Os_Is : Σ[Os] = Is.
  Proof.
    rewrite <- Delta_Is_Os.
    rewrite Sigma_inv.
    simpl ; trivial_seq.
  Qed. 

End PartialSum_Delta.

Fixpoint Ffac (n : nat) (x : R) :=
  match n with
  | O => 1
  | S n' => x * (Ffac n' (x - 1))
  end.

Notation "[ x ] ^n" := (pow x) (at level 19).
Notation "x^ [ n ]" := (fun x => pow x n) (at level 19).
Notation "x^^ [ n ]" := (Ffac n) (at level 19).
Notation "[ x ] ^^n" := (fun n => Ffac n x) (at level 19).

Lemma Delta_fixpoint : Δ[[2]^n] = [2]^n.
Proof.
  unfold Delta.
  rewrite Sub_app_distr.
  unfold Id.
  trivial_seq ; unfold E ; simpl.
  field.
Qed.

Lemma Delta_ffac : forall x,
  Δ[x^^[n]] = (S n) \* x^^[n].



