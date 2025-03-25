From mathcomp Require Import classical_sets.

Declare Scope wp_mathcomp_sets.

Implicit Type T : Type.

Definition element_of {T} (A : set T) (x : T) := A x.
Definition subset_of {T} (A B : set T) := subset A B.

Notation "A ⊂ B" := (subset_of A B) (at level 45) : wp_mathcomp_sets.
Notation "A ∩ B" := (setI A B) (at level 45) : wp_mathcomp_sets.
Notation "x ∈ A" := (element_of A x) (at level 70) : wp_mathcomp_sets.