Definition lem := forall p, p \/ ~p.
Print lem.

Definition frobenius := forall (A: Set)(p: A->Prop)(q: Prop),
  (forall x: A, q \/ p x) <-> (q \/ forall x: A, p x).

Theorem lem_to_frobenius: lem -> frobenius.
Proof.
unfold lem, frobenius.
firstorder.
(*assert (G := H q).
destruct G.*)
destruct (H q).
left.
assumption.
right.
intro.
destruct (H0 x).
elim H1.
assumption.
assumption.
Qed.

