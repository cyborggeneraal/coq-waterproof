Require Import Lra.
Require Import Coq.Sets.Ensembles.

Require Import Notations.

Lemma subset_refl {U : Type} (A : subset U):
    A ⊂ A.
Proof.
    intros x h.
    exact h.
Qed.

Lemma set_extensionality {U : Type} (A B : subset U):
    A = B ↔ A ⊂ B ∧ B ⊂ A.
Proof.
    split.
    {
        intro h.
        rewrite h.
        split.
        apply subset_refl.
        apply subset_refl.
    }
    {
        intros [hAB hBA].
        apply Extensionality_Ensembles.
        split.
        exact hAB.
        exact hBA.
    }
Qed.