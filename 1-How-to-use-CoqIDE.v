Definition pierce := forall p q: Prop, ((p -> q) -> p) -> p.
Definition lem := forall a, a \/ ~a.

Theorem pierce_equiv_lem: pierce <-> lem.
Proof.
unfold pierce, lem.
firstorder.
apply H with (q := ~(a \/ ~a)).
firstorder.
destruct (H p).
assumption.
firstorder.
Qed.
