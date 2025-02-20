Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Require Import Tactics.
Require Import Automation.
Require Import Libs.Sets.
Require Import Notations.Common.
Require Import Notations.Reals.
Require Import Notations.Sets.
Require Import Chains.

Lemma subset_trans {U : Type} (A B C : subset U):
    A ⊂ B → B ⊂ C → A ⊂ C.
Proof.
    Assume that (A ⊂ B) (i).
    Assume that (B ⊂ C) (ii).
    It suffices to show (∀x, x ∈ A → x ∈ C). (* Does not understand ∀x ∈ A, x ∈ C *)
    Take x : U.
    Assume that (x ∈ A).
    By (i) it holds that (∀x, x ∈ A → x ∈ B) (iii).
    By (ii) it holds that (∀x, x ∈ B → x ∈ C) (iv). 
    By (iv) it suffices to show (x ∈ B).
    By (iii) it suffices to show (x ∈ A).
    We conclude that (x ∈ A).
Qed.

Lemma empty_subset {U : Type} (A : subset U) :
    ∅ ⊂ A.
Proof.
    It suffices to show that (∀x, x ∈ ∅ → x ∈ A). (* Does not understand ∀x ∈ ∅, x ∈ A *)
    Take x : U.
    Assume that (x ∈ ∅).
    destruct _H.
Qed.

Lemma subset_refl {U : Type} (A : subset U) :
    A ⊂ A.
Proof.
    It suffices to show that (∀x, x ∈ A → x ∈ A). (* Does not understand ∀x ∈ A, x ∈ A *)
    Take x : U.
    Assume that (x ∈ A).
    We conclude that (x ∈ A).
Qed.

Lemma subset_anti_sym {U : Type} (A B : subset U) :
    A ⊂ B → B ⊂ A → A = B. (* Cannot split wedge in premise *)
Proof.
    Assume that (A ⊂ B).
    Assume that (B ⊂ A).
    apply set_extensionality. (* Cannot automate this *)
    We show both statements.
    {
        We conclude that (A ⊂ B).
    }
    {
        We conclude that (B ⊂ A).
    }
Qed.