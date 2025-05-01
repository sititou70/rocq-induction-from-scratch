Set Printing All.

Inductive myeq {A: Type}: A -> A -> Prop :=
  | myeq_refl: forall (x: A), myeq x x.
Notation "x = y" := (myeq x y): type_scope.
Hint Constructors myeq.

Definition myeq_myind:
  forall
    (A: Type)
    (P: forall (x y: A), Prop)
    (fmyeq_refl: forall refl_x, P refl_x refl_x),
  forall (x y: A) (Heq: myeq x y),
    P x y :=
  fun
    (A: Type)
    (P: forall (x y: A), Prop)
    (fmyeq_refl: forall refl_x, P refl_x refl_x) =>
    fix rec (x y: A) (Heq: myeq x y) :=
      match Heq with
        | myeq_refl refl_x => fmyeq_refl refl_x
      end.

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
  forall (n: mynat),
    P n :=
  fun
    (P: forall (_: mynat), Prop)
    (fmo: P MO)
    (fms: forall (n': mynat), P n' -> P (MS n')) =>
    fix rec (n: mynat) :=
      match n with
        | MO => fmo
        | MS n' => (fms n') (rec n')
      end.
