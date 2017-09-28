Definition lem := forall p, p \/ ~p.
Print lem.

Definition frobenius := forall (A: Set)(p: A->Prop)(q: Prop),
  (forall x: A, q \/ p x) <-> (q \/ forall x: A, p x).

(*Parameter S: Set.
Parameter q: Prop.
Lemma strange: forall x: S, q.

Definition A := {y : S | q}.
Print A.*)

Theorem frobenius_to_lem: frobenius -> lem.
Proof.
unfold lem, frobenius.
firstorder.
destruct (H {_: unit | p} (fun _ => False) p) as [G _].
(*clear H1.
rename H0 into G.*)
cut (p \/ ({_ : unit | p} -> False)).
intros [K1 | K2].
left.
assumption.
right.
intro.
apply K2.
exists tt.
assumption.
apply G.
(*intros.
destruct x.*)
intros [u J].
left.
assumption.
Qed.

