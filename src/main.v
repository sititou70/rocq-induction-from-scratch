(* Set Printing All. *)

Inductive myeq {A: Type}: A -> A -> Prop :=
  | myeq_refl: forall (x: A), myeq x x.
Notation "x = y" := (myeq x y): type_scope.
Hint Constructors myeq.

Theorem myeq_spec:
  forall (A: Type) (x: A) (y: A),
  myeq x y <-> eq x y.
Proof.
  intros A x y.
  split;
  intros H;
  inversion H;
  subst;
  constructor.
Qed.

Print eq_ind_r.

Lemma myeq_ind_r:
  forall [A: Type] (P: A -> Prop) (x: A) (y: A),
  P x ->
  y = x ->
  P y.
Proof.
  intros A P x y HPx Heq.
  inversion Heq.
  subst.
  apply HPx.
Qed.

Inductive mynat: Type :=
  | MO: mynat
  | MS: forall (_: mynat), mynat.

Fixpoint to_mynat (n: nat): mynat :=
  match n with
    | O => MO
    | S n' => MS (to_mynat n')
  end.
Example test_to_mynat1: to_mynat 0 = MO. Proof. auto. Qed.
Example test_to_mynat2: to_mynat 3 = MS (MS (MS MO)). Proof. auto. Qed.

Fixpoint myadd (x: mynat) (y: mynat): mynat :=
  match x with
    | MO => y
    | MS x' => MS (myadd x' y)
  end.
Notation "x + y" := (myadd x y).
Example test_myadd1: (to_mynat 1) + (to_mynat 0) = to_mynat 1. Proof. auto. Qed.
Example test_myadd2: (to_mynat 2) + (to_mynat 3) = to_mynat 5. Proof. auto. Qed.

Definition plus_0_l:
  forall (n: mynat),
  MO + n = n
:=
  fun (n: mynat) =>
    myeq_refl n.

Theorem plus_0_l':
  forall (n: mynat),
  MO + n = n.
Proof.
  intros n.
  apply myeq_refl.
Qed.

Print plus_0_l.
Print plus_0_l'.


Definition plus_0_r:
  forall (n: mynat),
  n + MO = n
:=
  fun (n: mynat) =>
  mynat_ind
    (fun (n: mynat) => n + MO = n)
    (myeq_refl MO)
    (
      fun (n: mynat) (IHn: n + MO = n) =>
        myeq_ind_r (fun (y: mynat) => MS y = MS n) n (n + MO) (myeq_refl (MS n)) IHn
    )
    n.

Theorem plus_0_r':
  forall (n: mynat),
  n + MO = n.
Proof.
  intros n.
  induction n.

    +
    apply myeq_refl.

    +
    simpl.
    eapply (myeq_ind_r (fun y => MS y = MS n)).
    apply myeq_refl.
    apply IHn.
Qed.

Print plus_0_r.
Print plus_0_r'.
