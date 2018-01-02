Set Implicit Arguments.

Definition surj(X Y: Type)(f: X->Y): Prop := forall y, exists x, f x = y.

Theorem Cantor X : ~ exists f: X->X->Prop, surj f.
Proof.
intros [f A].
pose (g:=fun x => ~ f x x).
destruct (A g) as [x B].
assert (C:g x <-> f x x).
{
  rewrite B; tauto.
}
unfold g in C.
tauto.
Qed.


