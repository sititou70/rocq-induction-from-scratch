Require Import definitions.

(* Set Printing All. *)

Definition myadd:
  forall (x y: mynat), mynat :=
  fix myadd (x: mynat) (y: mynat): mynat :=
    match x with
      | MO => y
      | MS x' => MS (myadd x' y)
    end.
Notation "x + y" := (myadd x y).

Definition mymul:
  forall (x y: mynat), mynat :=
  fix mymul (x: mynat) (y: mynat): mynat :=
    match x with
      | MO => MO
      | MS x' => y + (mymul x' y)
    end.
Notation "x * y" := (mymul x y).

Definition sum:
  forall (n: mynat), mynat :=
  fix sum (n: mynat): mynat :=
    match n with
      | MO => MO
      | MS n' => n + sum n'
    end.

Definition myeq_sym:
  forall [A: Type] [x y: A],
  forall (Heq: x = y),
  y = x :=
  fun (A: Type) (x y: A) (Heq: x = y) =>
    match Heq with
      | myeq_refl refl_x => myeq_refl refl_x
    end.

Definition myeq_ind_r:
  forall [A: Type] (P: A -> Prop) (x: A) (y: A),
  P x ->
  y = x ->
  P y :=
  fun
    (A: Type)
    (P: A -> Prop)
    (x: A)
    (y: A)
    (HPx: P x)
    (Heq: y = x) =>
      myeq_myind
        A
        (fun (x y: A) => forall (Py: P y), P x)
        (fun (refl_x: A) => fun (Prefl_x: P refl_x) => Prefl_x)
        y
        x
        Heq
        HPx.

Definition plus_0_r:
  forall (n: mynat),
  n + MO = n :=
  fun (n: mynat) =>
    (
      mynat_myind
        (fun (n: mynat) => n + MO = n)
        (myeq_refl MO)
        (
          fun (n: mynat) (IHn: n + MO = n) =>
            myeq_ind_r
              (fun (target: mynat) => MS target = MS n)
              n
              (n + MO)
              (myeq_refl (MS n))
              IHn
        )
    )
      n.
  
Definition plus_MS_move:
  forall (x y: mynat),
  (MS x) + y = x + (MS y) :=
  fun (x y: mynat) =>
    (
      mynat_myind
        (fun (x: mynat) => (MS x) + y = x + (MS y))
        (myeq_refl (MS y))
        (
          fun (x: mynat) (IHx: (MS x) + y = x + (MS y)) =>
            myeq_ind_r
              (fun (target: mynat) => MS target = MS x + MS y)
              (x + (MS y))
              ((MS x) + y)
              (myeq_refl ((MS x) + (MS y)))
              IHx
        )
    )
      x.

Definition plus_comm_base:
  forall (y: mynat),
  MO + y = y + MO :=
  fun (y: mynat) =>
    (
      mynat_myind
        (fun (y: mynat) => MO + y = y + MO)
        (myeq_refl MO)
        (
          fun (y: mynat) (IHy: MO + y = y + MO) =>
            myeq_ind_r
              (fun (target: mynat) => MO + MS y = MS target)
              (MO + y)
              (y + MO)
              (myeq_refl (MS y))
              (myeq_sym IHy)
  )
    )
      y.
Definition plus_comm_induction:
forall (x y: mynat) (IHx: x + y = y + x),
(MS x) + y = y + (MS x) :=
fun (x y: mynat) (IHx: x + y = y + x) =>
  (
    mynat_myind
      (fun (y: mynat) => (MS x) + y = y + (MS x))
      (plus_0_r (MS x))
      (
        fun (y: mynat) (IHy: (MS x) + y = y + (MS x)) =>
          let exp1:
            MS ((MS x) + y) = MS ((MS x) + y) :=
            (myeq_refl (MS ((MS x) + y)))
          in
          let exp2:
            MS (x + (MS y)) = MS ((MS x) + y) :=
            myeq_ind_r
              (fun (target: mynat) => MS target = MS ((MS x) + y))
              ((MS x) + y)
              (x + (MS y))
              exp1
              (myeq_sym (plus_MS_move x y))
          in
          let exp3:
            MS (x + (MS y)) = MS (y + (MS x)) :=
            myeq_ind_r
              (fun (target: mynat) => MS (x + (MS y)) = MS target)
              ((MS x) + y)
              (y + (MS x))
              exp2
              (myeq_sym IHy)
          in
          let exp4:
            (MS x) + (MS y) = MS y + (MS x) :=
            exp3
          in
          exp4
      )
  )
    y.
Definition plus_comm:
  forall (x y: mynat),
  x + y = y + x :=
  fun (x y: mynat) => 
    (
      mynat_myind
        (fun (x: mynat) => x + y = y + x)
        (plus_comm_base y)
        (fun (x: mynat) (IHx: x + y = y + x) => plus_comm_induction x y IHx)
    )
      x.

Definition plus_assoc:
  forall (x y z: mynat),
  (x + y) + z = x + (y + z) :=
  fun (x y z: mynat) =>
    (
      mynat_myind
        (fun (x: mynat) => (x + y) + z = x + (y + z))
        (myeq_refl (y + z))
        (
          fun (x: mynat) (IHx: (x + y) + z = x + (y + z)) =>
            myeq_ind_r
              (fun (target: mynat) => MS target = (MS x) + (y + z))
              (x + (y + z))
              ((x + y) + z)
              (myeq_refl (MS (x + (y + z))))
              IHx
        )
    )
      x.

Definition mul_dist:
  forall (x y z: mynat),
  x * (y + z) = (x * y) + (x * z) :=
  fun (x y z: mynat) =>
    (
      mynat_myind
        (fun (x: mynat) => x * (y + z) = (x * y) + (x * z))
        (myeq_refl MO)
        (
          fun (x: mynat) (IHx: x * (y + z) = (x * y) + (x * z)) =>
            let exp1:
              (y + (x * y)) + (z + (x * z)) = (y + (x * y)) + (z + (x * z)) :=
              myeq_refl ((y + (x * y)) + (z + (x * z)))
            in
            let exp2:
              ((y + (x * y)) + z) + (x * z) = (y + (x * y)) + (z + (x * z)) :=
              myeq_ind_r
                (fun (target: mynat) => target = (y + (x * y)) + (z + (x * z)))
                ((y + (x * y)) + (z + (x * z)))
                (((y + (x * y)) + z) + (x * z))
                exp1
                (plus_assoc (y + (x * y)) z (x * z))
            in
            let exp3:
              (y + ((x * y) + z)) + (x * z) = (y + (x * y)) + (z + (x * z)) :=
              myeq_ind_r
                (fun (target: mynat) => target + (x * z) = (y + (x * y)) + (z + (x * z)))
                ((y + (x * y)) + z)
                (y + ((x * y) + z))
                exp2
                (myeq_sym (plus_assoc y (x * y) z))
            in
            let exp4:
              (y + (z + (x * y))) + (x * z) = (y + (x * y)) + (z + (x * z)) :=
              myeq_ind_r
                (fun (target: mynat) => (y + target) + (x * z) = (y + (x * y)) + (z + (x * z)))
                ((x * y) + z)
                (z + (x * y))
                exp3
                (myeq_sym (plus_comm (x * y) z))
            in
            let exp5:
              ((y + z) + (x * y)) + (x * z) = (y + (x * y)) + (z + (x * z)) :=
              myeq_ind_r
                (fun (target: mynat) => target + (x * z) = (y + (x * y)) + (z + (x * z)))
                (y + (z + (x * y)))
                ((y + z) + (x * y))
                exp4
                (plus_assoc y z (x * y))
            in
            let exp6:
              (y + z) + ((x * y) + (x * z)) = (y + (x * y)) + (z + (x * z)) :=
              myeq_ind_r
                (fun (target: mynat) => target = (y + (x * y)) + (z + (x * z)))
                (((y + z) + (x * y)) + (x * z))
                ((y + z) + ((x * y) + (x * z)))
                exp5
                (myeq_sym (plus_assoc (y + z) (x * y) (x * z)))
            in
            let exp7:
              (y + z) + (x * (y + z)) = (y + (x * y)) + (z + (x * z)) :=
              myeq_ind_r
                (fun (target: mynat) => (y + z) + target = (y + (x * y)) + (z + (x * z)))
                ((x * y) + (x * z))
                (x * (y + z))
                exp6
                IHx
            in
            let exp8:
              (MS x) * (y + z) = ((MS x) * y) + ((MS x) * z) :=
              exp7
            in
            exp8
          )
    )
      x.

Definition mul_0_r:
  forall (n: mynat),
  n * MO = MO :=
  mynat_myind
    (fun (n: mynat) => n * MO = MO)
    (myeq_refl MO)
    (fun (n: mynat) (IHn: n * MO = MO) => IHn).

Definition mul_1_r:
  forall (n: mynat),
  n * (MS MO) = n :=
  mynat_myind
    (fun (n: mynat) => n * (MS MO) = n)
    (myeq_refl MO)
    (
      fun (n: mynat) (IHn: n * (MS MO) = n) =>
        let exp1:
          MS n = MS n :=
          myeq_refl (MS n)
        in
        let exp2:
          MS MO + n = MS n :=
          exp1
        in
        let exp3:
          MS MO + (n * (MS MO)) = MS n :=
          myeq_ind_r
            (fun (target: mynat) => MS MO + target = MS n)
            n
            (n * (MS MO))
            exp2
            IHn
        in
        let exp4:
          MS n * MS MO = MS n :=
          exp3
        in
        exp4
    ).
  
Definition mul_comm:
  forall (x y: mynat),
  x * y = y * x :=
  fun (x y: mynat) =>
    mynat_myind
      (fun (y: mynat) => x * y = y * x)
      (mul_0_r x)
      (
        fun (y: mynat) (IHy: x * y = y * x) =>
          let exp1:
            x + (x * y) = x + (x * y) :=
            myeq_refl (x + (x * y))
          in
          let exp2:
            x + (x * y) = x + (y * x) :=
            myeq_ind_r
              (fun (target: mynat) => x + (x * y) = x + target)
              (x * y)
              (y * x)
              exp1
              (myeq_sym IHy)
          in
          let exp3:
            (x * (MS MO)) + (x * y) = x + (y * x) :=
            myeq_ind_r
              (fun (target: mynat) => target + (x * y) = x + (y * x))
              x
              (x * (MS MO))
              exp2
              (mul_1_r x)
          in
          let exp4:
            x * ((MS MO) + y) = x + (y * x) :=
            myeq_ind_r
              (fun (target: mynat) => target = x + (y * x))
              ((x * (MS MO)) + (x * y))
              (x * ((MS MO) + y))
              exp3
              (mul_dist x (MS MO) y)
          in
          let exp5:
            x * MS y = MS y * x :=
            exp4
          in
          exp5
      )
        y.

Definition main:
  forall (n: mynat),
  MS (MS MO) * (sum n) = n * (MS n) :=
  fun (n: mynat) =>
    mynat_myind
      (fun (n: mynat) => MS (MS MO) * (sum n) = n * (MS n))
      (myeq_refl MO)
      (
        fun (n: mynat) (IHn: MS (MS MO) * (sum n) = n * (MS n)) =>
          let exp1:
            (MS n) * (MS (MS n)) = (MS n) * (MS (MS n)) :=
            myeq_refl ((MS n) * (MS (MS n)))
          in
          let exp2:
            (MS n) * (MS (MS MO) + n) = (MS n) * (MS (MS n)) :=
            exp1
          in
          let exp3:
            ((MS n) * MS (MS MO)) + ((MS n) * n) = (MS n) * (MS (MS n)) :=
            myeq_ind_r
              (fun (target: mynat) => target = (MS n) * (MS (MS n)))
              ((MS n) * (MS (MS MO) + n))
              (((MS n) * MS (MS MO)) + ((MS n) * n))
              exp2
              (myeq_sym (mul_dist (MS n) (MS (MS MO)) n))
          in
          let exp4:
            (MS (MS MO) * (MS n)) + ((MS n) * n) = (MS n) * (MS (MS n)) :=
            myeq_ind_r
              (fun (target: mynat) => target + ((MS n) * n) = (MS n) * (MS (MS n)))
              ((MS n) * MS (MS MO))
              (MS (MS MO) * (MS n))
              exp3
              (myeq_sym (mul_comm (MS n) (MS (MS MO))))
          in
          let exp5:
            (MS (MS MO) * (MS n)) + (n * (MS n)) = (MS n) * (MS (MS n)) :=
            myeq_ind_r
              (fun (target: mynat) => (MS (MS MO) * (MS n)) + target = (MS n) * (MS (MS n)))
              ((MS n) * n)
              (n * (MS n))
              exp4
              (myeq_sym (mul_comm (MS n) n))
          in
          let exp6:
            (MS (MS MO) * (MS n)) + (MS (MS MO) * (sum n)) = (MS n) * (MS (MS n)) :=
            myeq_ind_r
              (fun (target: mynat) => (MS (MS MO) * (MS n)) + target = (MS n) * (MS (MS n)))
              (n * (MS n))
              (MS (MS MO) * (sum n))
              exp5
              IHn
          in
          let exp7:
            MS (MS MO) * ((MS n) + (sum n)) = (MS n) * (MS (MS n)) :=
            myeq_ind_r
              (fun (target: mynat) => target = (MS n) * (MS (MS n)))
              ((MS (MS MO) * (MS n)) + (MS (MS MO) * (sum n)))
              (MS (MS MO) * ((MS n) + (sum n)))
              exp6
              (mul_dist (MS (MS MO)) (MS n) (sum n))
          in
          let exp8:
            MS (MS MO) * (sum (MS n)) = (MS n) * (MS (MS n)) :=
            exp7
          in
          exp8
      )
        n.
