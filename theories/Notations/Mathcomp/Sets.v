From mathcomp Require Import classical_sets.
Require Import Waterproof.Notations.Sets.

Declare Scope wp_mathcomp_sets.

Implicit Type T : Type.

Notation "A ⊂ B" := (subset A B) (at level 45) : wp_mathcomp_sets.
Notation "A ∩ B" := (setI A B) (at level 45) : wp_mathcomp_sets.
Notation "x ∈ A" := (is_true (in_set A x)) (at level 70) : wp_mathcomp_sets.

Definition in_subset {T} (A : set T) (x : T) := A x.

Declare Scope wp_mathcomp_pred_subset.
Delimit Scope wp_mathcomp_pred_subset with pfs.

Notation "∈ A" := (in_subset A) (at level 69, A at next level) : wp_mathcomp_pred_subset.

Declare Scope wp_mathcomp_subset.

Notation "'∀' x Q , P" :=
  (seal (fun z : subset_type (Q)%pfs -> Prop => forall x : (subset_type (Q)%pfs), is_true (in_set z x) -> P) Q%pfs)
  (at level 200, x binder, right associativity) : wp_mathcomp_subset.

Notation "'for' 'all' x Q , P" :=
  (seal (fun z : subset_type (Q)%pfs -> Prop => forall x : (subset_type (Q)%pfs), is_true (in_set z x) -> P) Q%pfs)
  (at level 200, x binder, right associativity, only parsing) : wp_mathcomp_subset.