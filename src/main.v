Set Printing All.

Inductive myeq {A: Type}: A -> A -> Prop :=
  | myeq_refl: forall (x: A), myeq x x.
Notation "x = y" := (myeq x y): type_scope.
Hint Constructors myeq.

Theorem myeq_spec:
  forall (A: Type) (x y: A),
  eq x y <-> myeq x y.
Proof.
  intros A x y.
  split;
  intros H;
  inversion H;
  constructor.
Qed.

Inductive mynat: Type :=
  | MO: mynat
  | MS: forall (_: mynat), mynat.

Definition mynat_myind:
  forall
    (P: forall (_: mynat), Prop)
    (fmo: P MO)
    (fms: forall (n': mynat), P n' -> P (MS n')),
  forall (n: mynat), P n :=
  fun
    (P: forall (_: mynat), Prop)
    (fmo: P MO)
    (fms: forall (n': mynat), P n' -> P (MS n')) =>
    fix rec (n: mynat) :=
      match n with
        | MO => fmo
        | MS n' => (fms n') (rec n')
      end.

Definition myadd:
  forall (x y: mynat), mynat :=
  fix myadd (x: mynat) (y: mynat): mynat :=
    match x with
      | MO => y
      | MS x' => MS (myadd x' y)
    end.
Notation "x + y" := (myadd x y).
Example test_myadd1':
  (MS MO) + (MO) = (MS MO).
Proof.
  auto.
Qed.
Definition test_myadd1:
  (MS MO) + (MO) = (MS MO) :=
  myeq_refl (MS MO).
Example test_myadd2':
  (MS (MS MO)) + (MS (MS (MS MO))) = MS (MS (MS (MS (MS MO)))).
Proof.
  auto.
Qed.
Definition test_myadd2:
  (MS (MS MO)) + (MS (MS (MS MO))) = MS (MS (MS (MS (MS MO)))) :=
  myeq_refl (MS (MS (MS (MS (MS MO))))).

Theorem plus_0_l':
  forall (n: mynat),
  MO + n = n.
Proof.
  intros n.
  apply myeq_refl.
Qed.

Definition plus_0_l:
  forall (n: mynat),
  MO + n = n :=
  fun (n: mynat) =>
    myeq_refl n.

Print plus_0_l'.
Print plus_0_l.

Definition eq_ind_r:
  forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, eq y x -> P y.
  intros A x P H y H0.
  elim eq_sym with (1 := H0). assumption.
Defined.

Lemma myeq_ind_r':
  forall [A: Type] (P: A -> Prop) (x: A) (y: A),
  P x ->
  y = x ->
  P y.
Proof.
  intros A P x y HPx Heq.
  induction Heq.
  apply HPx.
Qed.

Definition myeq_ind_r:
  forall [A: Type] (P: A -> Prop) (x: A) (y: A),
  P x ->
  y = x ->
  P y :=
  fun (A: Type) (P: A -> Prop) (x: A) (y: A) (HPx: P x) (Heq: y = x) =>
    myeq_ind
      A
      (fun (a b: A) => forall (Pb: P b), P a)
      (fun (_: A) => fun pa => pa)
      y
      x
      Heq
      HPx.

Print myeq_ind_r'.
Print myeq_ind_r.

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
  
Definition plus_0_r:
  forall (n: mynat),
  n + MO = n :=
  fun (n: mynat) =>
  mynat_myind
    (fun (n: mynat) => n + MO = n)
    (myeq_refl MO)
    (
      fun (n: mynat) (IHn: n + MO = n) =>
        myeq_ind_r (fun (y: mynat) => MS y = MS n) n (n + MO) (myeq_refl (MS n)) IHn
    )
    n.

Print plus_0_r'.
Print plus_0_r.
