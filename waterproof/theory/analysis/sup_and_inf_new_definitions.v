(** * Suprema and infima

Authors:
    - Jim Portegies

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

Require Import Reals.
Require Import Lra.
Require Import Classical.
Require Import Classical_Pred_Type.

Require Import Waterproof.selected_databases.
Require Import Waterproof.AllTactics.
Require Import Waterproof.contradiction_tactics.basic_contradiction.
Require Import Waterproof.load_database.All.
Require Import Waterproof.notations.notations.
Require Import Waterproof.definitions.set_definitions.
Require Import Waterproof.set_search_depth.To_5.
Require Import Waterproof.set_intuition.Disabled.
Require Import Waterproof.load_database.DisableWildcard.


Ltac2 Eval global_database_selection.

(** ## Upper bounds

A number $M : ℝ$ is called an **upper bound** of a subset $A : ℝ \to \mathsf{Prop}$ of the real numbers, if for all $a : ℝ$, if $a ∈ A$ then $a ≤ M$.*)
Definition is_upper_bound (A : subsets_R) (M : ℝ) :=
  ∀ a : A, a ≤ M.
(** We say that a subset $A : ℝ \to \mathsf{Prop}$ is bounded above if there exists an $M : ℝ$ such that $M$ is an upper bound of $A$.
*)
Definition is_bounded_above (A : subsets_R) :=
  ∃ M : ℝ, is_upper_bound A M.
(** ## The supremum

A real number $L : ℝ$ is called the **supremum** of a subset $A : ℝ \to \mathsf{Prop}$ if it is the smallest upper bound.
*)
Definition is_sup (A : subsets_R) (L : ℝ) :=
  (is_upper_bound A L) ∧ (∀ M : ℝ, is_upper_bound A M ⇒ (L ≤ M) ).
(** 
We have to use `Waterproof.definitions.set_definitions` since `is_in`
  is doubly defined in [notations.v] as
  [Definition is_in {D : Set} := fun (A : (D → Prop)) 
   ↦ (fun (x : D) ↦ A x).]
*)
(* Notation is_in := Waterproof.definitions.set_definitions.is_in. *)

Lemma equivalence_upper_bounds :
  ∀ (A : subsets_R) (L : ℝ),
    is_upper_bound A L ⇔
    Raxioms.is_upper_bound (is_in A) L.
Proof.
    Take A : subsets_R, L : ℝ.
    We show both directions.
    Assume L_upp_bd : (is_upper_bound A L).
    Expand the definition of Raxioms.is_upper_bound.
    Expand the definition of is_upper_bound in L_upp_bd.
    Take x : ℝ.
    Assume w : (is_in A x).
    Define b := (mk_element_R (is_in A) x w).
    By L_upp_bd it holds that H : (b ≤ L).
    Apply H.

    Assume L_is_upp_bd : (Raxioms.is_upper_bound (is_in A) L).
    Expand the definition of is_upper_bound.
    Expand the definition of Raxioms.is_upper_bound in L_is_upp_bd.
    Take a : (subsets_R_to_elements A).
    Apply L_is_upp_bd.
    (** TODO subsets_elements_satisfy_predicate does not exist??? *)
    (* By subset_elements_satisfy_predicate it holds that h2: (is_in A a). *)
    (* By L_is_upp_bd it holds that (a ≤ L). *)

    
    This concludes the proof.
Qed.

Lemma equivalence_sup_lub :
  ∀ (A : subsets_R) (M : ℝ),
  is_lub (is_in A) M
  ⇔ is_sup A M.
Proof.
    Take A : subsets_R, M : ℝ.
    We show both directions.

    Assume M_is_sup_A : (is_lub (is_in A) M).
    Expand the definition of is_lub in M_is_sup_A.
    Expand the definition of Raxioms.is_upper_bound in M_is_sup_A.
    Expand the definition of is_sup.
    We show both statements.
    Expand the definition of is_upper_bound.
    Take a : (subsets_R_to_elements A).
    destruct M_is_sup_A as [Mp1 Mp2].
    By Mp1 it holds that H : (a ≤ M).
    Apply H.

    Take M0 : ℝ.
    Assume M_is_ub_A : (is_upper_bound A M0).
    destruct M_is_sup_A as [M_is_R_ub_A M_is_R_lub_A].
    destruct (equivalence_upper_bounds A M0). 
    Apply (M_is_R_lub_A M0 (H M_is_ub_A)).

    Assume M_is_sup_A : (is_sup A M).
    Expand the definition of is_lub.
    Expand the definition of is_sup in M_is_sup_A.
    We show both statements.
    Expand the definition of Raxioms.is_upper_bound.
    destruct M_is_sup_A. 
    Expand the definition of is_upper_bound in H.
    Take x : ℝ. 
    Assume x_in_A : (is_in A x). 
    Define b := (mk_element_R (is_in A) x x_in_A).
    By H it holds that H1 : (b ≤ M).
    Apply H1.

    Take b : ℝ.
    Assume M_is_R_lub_A : (Raxioms.is_upper_bound (is_in A) b).
    destruct M_is_sup_A as [M_is_ub_A M_is_lub_A].
    Apply (M_is_lub_A b).
    destruct (equivalence_upper_bounds A b).
    Apply (H0 M_is_R_lub_A).
Qed.



(** ## The completeness axiom

The completeness axiom of the real numbers says that when a subset $A$ of the real numbers is bounded from above, and when there exists an element in the set, then there exists an $L$ such that $L$ is the supremum of $A$.*)
Lemma R_complete : ∀ (A : subsets_R) (x : A),
  is_bounded_above A ⇒ mk_subset_R (fun M : ℝ => is_sup A M).
Proof.
    Take A : subsets_R.
    Take a : (subsets_R_to_elements A).
    Assume A_bdd_above : (is_bounded_above A).
    We claim that H : (sig (is_lub (is_in A))).
    Apply completeness.
    Expand the definition of is_bounded_above in A_bdd_above.
    Expand the definition of is_upper_bound in A_bdd_above.
    Expand the definition of bound.
    Choose M such that A_bdd_by_M according to A_bdd_above.
    Choose m := M.
    We need to show that (∀ a : ℝ, is_in A a ⇒ a ≤ M).
    Expand the definition of Raxioms.is_upper_bound.
    Take x : ℝ.
    Assume w : (is_in A x).
    Define b := (mk_element_R (is_in A) x w).
    ltac1:(pose proof (A_bdd_by_M b)).
    This follows by assumption.
    Choose y := a.
    We prove by induction on y.
    This follows by assumption.
    Choose M such that M_upp_bd according to H.

    destruct (equivalence_sup_lub A M) as [M_is_sup_A H2]. 
    specialize (M_is_sup_A M_upp_bd).
    exists M. 
    exact M_is_sup_A.
Qed.



(** 
Axiom completeness : ∀ A : ℝ → Prop,
      is_bounded_above A ⇒ 
        ((∃ x : ℝ, x ∈ A) ⇒ { M : ℝ | is_sup A M }).
```*)
(** ## Lower bounds

A number $m : ℝ$ is called a lower bound of a subset $A : ℝ → \mathsf{Prop}$, if for all $a : \mathbb{R}$, if $a \in A$ then $a ≥ m$.*)
Definition is_lower_bound (A : subsets_R) (m : ℝ) :=
  ∀ a : A, m ≤ a.
(** We say that a subset $A : ℝ → \mathsf{Prop}$ is bounded below if there exists an $m : ℝ$ such that $m$ is a lower bound of $A$.*)
Definition is_bounded_below (A : subsets_R) :=
  ∃ m : ℝ, is_lower_bound A m.
(** ## The infimum

A real number $m : ℝ$ is called the **infimum** of a subset $A : ℝ → \mathsf{Prop}$ if it is the largest lower bound.*)
Definition is_inf :=
  fun (A : subsets_R) m 
    => (is_lower_bound A m) ∧ (∀ l : R, is_lower_bound A l ⇒ l ≤ m).
(** ## Reflection of a subset of ℝ in the origin

Before we continue showing properties of the infimum, 
we first introduce the reflection of subsets of $\mathbb{R}$ 
in the origin. 
Given a subset $A : ℝ → \mathsf{Prop}$, 
we consider the set $-A$ 
(which we write as $\mathsf{set\_opp} A$), defined by*)
Definition set_opp (A : subsets_R)  :=
  mk_subset_R (fun (x : ℝ) ↦ (is_in A (-x))).


Definition original_elem {A : subsets_R} : (set_opp A) -> A.
Proof.
    intro opp_a.
    (** TODO: this does not work for some reason *)
    (* It is not a forall goal. Also [intros] doesn't do anything here *)
    (* Take opp_a : (set_opp A). *)
    It holds that H1 : (is_in (set_opp A) (opp_a)).
    It holds that H2 : (is_in A (-opp_a)).
    exact (mk_element_R (is_in A) (-opp_a) H2).
Defined.


Lemma neg_opp_is_original_elem {A : subsets_R} : 
  forall opp_a : (set_opp A), -opp_a = original_elem opp_a.
Proof.
    Take opp_a : (subsets_R_to_elements (set_opp A)).
    It holds that H : (-opp_a =  original_elem opp_a).
    Apply H.
Qed.


(** TODO: add this to additional lemmas.. *)
(** Hint Resolve neg_opp_is_original_elem : additional.*)
Lemma upp_bd_set_to_low_bd_set_opp :
  ∀ (A : subsets_R) (M : ℝ),
    is_upper_bound A M ⇒ 
      is_lower_bound (set_opp A) (-M).
Proof.
    Take A : subsets_R, M : ℝ.
    Assume M_upp_bd : (is_upper_bound A M).
    We need to show that (∀ a : (set_opp A),-M ≤ a).
    Expand the definition of is_lower_bound.
    Take opp_a : (subsets_R_to_elements (set_opp A)).
    Define a := (original_elem opp_a).
    It holds that H1 : (is_in A a).
    By M_upp_bd it holds that H2 : (a ≤ M).
    It holds that H3 : (-opp_a = a).
    It holds that H4 : (-M ≤ opp_a).
    Apply H4.
Qed.


Lemma low_bd_set_to_upp_bd_set_opp :
  ∀ (A : subsets_R) (m : ℝ),
    is_lower_bound A m ⇒
      is_upper_bound (set_opp A) (-m).
Proof.
    Take A : subsets_R, m : ℝ.
    Assume m_low_bd : (is_lower_bound A m).
    We need to show that (∀ opp_a : (set_opp A), opp_a ≤ -m).
    Expand the definition of is_upper_bound.
    Take opp_a : (subsets_R_to_elements (set_opp A)).
    Define a := (original_elem opp_a).
    By m_low_bd it holds that H1 : (m ≤ a).
    It holds that H2 : (-opp_a = a).
    This concludes the proof.
Qed.


Lemma low_bd_set_opp_to_upp_bd_set :
  ∀ (A : subsets_R) (m : ℝ),
    is_lower_bound (set_opp A) m ⇒ 
      is_upper_bound A (-m).
Proof.
    Take A : (subsets_R), m : ℝ.
    Assume m_low_bd : (is_lower_bound (set_opp A) m).
    We need to show that (∀ a : A, a ≤ -m).
    Expand the definition of is_upper_bound.
    Take a : (subsets_R_to_elements A).
    Write m_low_bd as (∀ b : (set_opp A), m ≤ b).
    We claim that minmin_a_in_A : (is_in A (--a)).
    Write goal using (--a = a) as (is_in A a).
    It holds that H : (is_in A a).
    This concludes the proof.
    It holds that min_a_in_set_opp_A : (is_in (set_opp A) (-a)).
    (** By m_low_bd it holds that (m ≤ -a) (m_le_min_a).*)
    Define c := (mk_element_R _ (-a) min_a_in_set_opp_A).
    We claim that m_le_c : (m ≤ c).
    Apply m_low_bd.
    It holds that m_le_min_a : (m ≤ -a).
    This concludes the proof.
Qed.


Lemma upp_bd_set_opp_to_low_bd_set :
  ∀ (A : subsets_R) (M : ℝ),
    is_upper_bound (set_opp A) M ⇒
      is_lower_bound A (-M).
Proof.
    Take A : (subsets_R), M : ℝ.
    Assume M_upp_bd : (is_upper_bound (set_opp A) M).
    We need to show that (∀ a : A, -M ≤ a).
    Expand the definition of is_lower_bound.
    Take a : (subsets_R_to_elements A).
    We claim that minmin_a_in_A : (is_in A (--a)).
    Write goal using (--a = a) as (is_in A a).
    This follows immediately.
    It holds that min_a_in_set_opp_A : (is_in (set_opp A) (-a)).
    Define c := (mk_element_R _ (-a) (min_a_in_set_opp_A)).
    By M_upp_bd it holds that mina_le_M : (c ≤ M).
    It holds that min_a_le_M : (-a ≤ M).
    This concludes the proof.
Qed.


Lemma bdd_below_to_bdd_above_set_opp :
  ∀ (A : subsets_R),
    is_bounded_below A ⇒ is_bounded_above (set_opp A).
Proof.
    Take A : (subsets_R). 
    Assume A_bdd_below : (is_bounded_below A).
    We need to show that (∃ M : ℝ, is_upper_bound (set_opp A) M).
    Expand the definition of is_bounded_above.
    Write A_bdd_below as (∃ m : ℝ, is_lower_bound A m).
    Choose m such that m_low_bd according to A_bdd_below.
    Choose M := (-m).
    We need to show that (is_upper_bound (set_opp A) (-m)).
    Expand the definition of is_upper_bound.
    By low_bd_set_to_upp_bd_set_opp it holds that H_con : (is_upper_bound (set_opp A) (-m)).
    This concludes the proof.
Qed.


Lemma sup_set_opp_is_inf_set :
  ∀ (A : subsets_R) (M : ℝ),
    is_sup (set_opp A) M ⇒ is_inf A (-M).
Proof.
    Take A : (subsets_R), M : ℝ.
    Assume M_is_sup : (is_sup (set_opp A) M).
    Expand the definition of is_inf.
    We need to show that (is_lower_bound A (-M) ∧ ∀ l : ℝ, is_lower_bound A l ⇒ l ≤ -M).
    We show both statements.
    We claim that H0 : (is_upper_bound (set_opp A) M).
    Expand the definition of is_upper_bound.
    Take a : (subsets_R_to_elements (set_opp A)).
    Expand the definition of is_sup in M_is_sup.
    destruct M_is_sup as [Mp1 Mp2].
    Expand the definition of is_upper_bound in Mp1.
    By Mp1 it holds that M_upp_bd : (is_upper_bound (set_opp A) M).
    This concludes the proof.

    By upp_bd_set_opp_to_low_bd_set it holds that H1 : (is_lower_bound A (-M)).
    Apply H1.

    We need to show that (∀ l : ℝ, is_lower_bound A l ⇒ l ≤ -M).
    Take l : ℝ.
    Assume l_low_bd : (is_lower_bound A l).
    Expand the definition of is_sup in M_is_sup.
    Because M_is_sup both Mp1 and Mp2.
    By Mp1 it holds that H1 : (∀ b : ℝ, is_upper_bound (set_opp A) b ⇒ M ≤ b).
    By low_bd_set_to_upp_bd_set_opp it holds that H2 : (is_upper_bound (set_opp A) (-l)).
    By H1 it holds that H3 : (M ≤ -l).
    This concludes the proof.
Qed.


Lemma exists_inf :
  ∀ (A : (subsets_R)) (x : A), is_bounded_below A ⇒
    mk_subset_R (fun (m : ℝ) ↦ is_inf A m).
Proof.
    Take A : (subsets_R).
    Take z : (subsets_R_to_elements A).
    Assume A_bdd_below : (is_bounded_below A).
    Define B := (set_opp A).
    We claim that B_bdd_above : (is_bounded_above B).
    Apply bdd_below_to_bdd_above_set_opp.
    Apply A_bdd_below.
    We claim that min_min_z_in_A : (is_in A (--z)).
    Write goal using (--z = z) as (is_in A z).
    This concludes the proof.

    It holds that min_z_in_B : (is_in (set_opp A) (-z)).
    Define c := (mk_element_R _ (-z) (min_z_in_B)).
    Define L := (R_complete B c B_bdd_above).
    We claim that L_is_sup_B : (is_sup B L).
    Choose Lel such that witness according to L.
    Apply witness.
    By sup_set_opp_is_inf_set it holds that minL_is_inf_A : (is_inf A (-L)).
    (** TODO : remove this exact *)
    exact (mk_element_R _ (-L) minL_is_inf_A).
Qed.

(** ### A supremum is an upper bound

If $M$ is the supremum of a set $A$, it is also an upper bound.*)
Lemma sup_is_upp_bd :
  ∀ A : (subsets_R),
    ∀ M : ℝ,
      is_sup A M ⇒ is_upper_bound A M.
Proof.
    Take A : (subsets_R).
    Take M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    Write M_is_sup_A as (is_upper_bound A M ∧ (∀ b: ℝ, is_upper_bound A b ⇒ M ≤ b) ).
    Because M_is_sup_A both A_upp_bd and every_upper_bound_smaller.
    It follows that (is_upper_bound A M).
Qed.

(** ### Any upper bound is greater than or equal to the supremum*)
Lemma any_upp_bd_ge_sup :
  ∀ A : (subsets_R),
    ∀ M L : ℝ,
      is_sup A M ⇒ (is_upper_bound A L ⇒ M ≤ L).
Proof.
    Take A : (subsets_R).
    Take M : ℝ.
    Take L : ℝ.
    (** TODO: fix this intro *)
    intro A_is_sup_M. 
(*    Assume A_is_sup_M : (is_supp A M). *)
    Assume L_is_upp_bd_A : (is_upper_bound A L).
    Because A_is_sup_M both M_is_upp_bd and any_upp_bd_le_M.
    (** We need to show that $M \leq L$.*)
    We conclude that (M ≤ L).
Qed.
(** ## Infima*)
(** ## An infimum is a lower bound*)
Lemma inf_is_low_bd :
  ∀ A : (subsets_R),
    ∀ m : ℝ,
      is_inf A m ⇒ is_lower_bound A m.
Proof.
    Take A : (subsets_R).
    Take m : R.
    Assume m_is_inf_A : (is_inf A m).
    Because m_is_inf_A both m_is_low_bd and any_low_bd_ge_m.
    By m_is_low_bd we conclude that (is_lower_bound A m).
Qed.
(** ## Any lower bound is less than or equal to the infimum*)
Lemma any_low_bd_ge_inf :
  ∀ A : (subsets_R),
    ∀ m l : ℝ,
      is_inf A m ⇒ is_lower_bound A l ⇒ l ≤ m.
Proof.
    Take A : (subsets_R).
    Take m : ℝ.
    Take l : ℝ.
    (** TODO: fix this intro *)
    intro m_is_inf_A.
    (* Assume m_is_inf_A : (is_inf A m). *)
    Assume l_is_low_bd_A : (is_lower_bound A l).
    Because m_is_inf_A both m_low_bd and any_low_bd_le_m.
    We conclude that (l ≤m).
Qed.

(** ### $\varepsilon$-characterizations*)
Lemma exists_almost_maximizer :
  ∀ (A : subsets_R) (M : ℝ),
    is_sup A M ⇒
      ∀ (L : ℝ), L < M ⇒ 
        ∃ a : A, L < a.
Proof.
    Take A : (subsets_R).
    Take M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    Take L : ℝ.
    Assume L_lt_M : (L < M).
    We argue by contradiction.
    We claim that H0 : (∀ x : A, ¬ (L < x)).
    Apply not_ex_all_not.
    Apply H.
    We claim that H1 : (∀ x : A, x ≤ L).
    Take x : (subsets_R_to_elements A).
    It holds that H2 : (¬(L < x)).
    We need to show that (x ≤ L).
    We conclude that (x ≤ L).
    By H1 it holds that H3 : (is_upper_bound A L).
    (** TODO: why can't this be done automatically? *)
    We claim that H4 : (M ≤ L).
    Apply (any_upp_bd_ge_sup A).
    Apply M_is_sup_A.
    Apply H3.
    It holds that H5 : (¬(M ≤ L)).
    Contradiction.
Qed.

Lemma exists_almost_maximizer_ε :
  ∀ (A : subsets_R) (M : ℝ),
    is_sup A M ⇒
      ∀ (ε : ℝ), ε > 0 ⇒ 
        ∃ a : A, M - ε < a.
Proof.
    Take A : (subsets_R).
    Take M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    Take ε : ℝ.
    Assume ε_gt_0 : (ε > 0).
    It holds that H1 : (M - ε < M). 
    (** TODO: fix this *)
    apply exists_almost_maximizer with (L := M- ε) (M := M); assumption.
Qed.

Lemma max_or_strict :
  ∀ (A : subsets_R) (M : ℝ),
    is_sup A M ⇒ 
      (is_in A M) ∨ (∀ a : A, a < M).
Proof.
    Take A : (subsets_R).
    Take M : ℝ.
    Assume M_is_sup_A : (is_sup A M).
    We argue by contradiction. 
    By not_or_and it holds that H1 : ((¬ (is_in A M)) ∧ 
      ¬(∀ a : A, a < M) ).
    Because H1 both H2 and H3.
    (** TODO: fix *)
    (** We only show the proposition on the *)
    right
    (** hand side of the or-sign, i.e. we will show that for all $a \in \mathbb{R}$, if $a \in A$ then $a < M$*)
    .
    Take a : (subsets_R_to_elements A).
    By sup_is_upp_bd it holds that M_upp_bd : (is_upper_bound A M).
    It holds that a_le_M : (a ≤ M).
    We claim that a_is_not_M : (¬(element _ a = M)).
    We argue by contradiction.
    We claim that H4 : ((element _ a = M) ⇒ False).
    Assume a_eq_M : (element _ a = M).
    We claim that M_in_A : (is_in A M).
    Rewrite using (M=a).
    We conclude that (is_in A a).
    Contradiction.
    We conclude that (element _ a ≠ M).
    We conclude that (a < M).
Qed.
(** * Lemmas for convenience*)
Lemma bounded_by_upper_bound_propform :
  ∀ (A : subsets_R) (M : ℝ) (b : ℝ),
    is_upper_bound A M ⇒ is_in A b ⇒ b ≤ M.
Proof.
    Take A : subsets_R.
    Take M : ℝ.
    Take b : ℝ.
    (** TODO: fix 
    Assume M_upp_bd : (is_upper_bound A M). *)
    intro M_upp_bd.
    Assume b_in_A : (is_in A b).
    Define c := (mk_element_R (is_in A) b b_in_A).
    Expand the definition of is_upper_bound in M_upp_bd.
    By M_upp_bd it holds that c_le_M : (c ≤ M).
    We conclude that (b ≤ M).
Qed.

Lemma bounded_by_lower_bound_propform :
  ∀ (A : subsets_R) (m : ℝ) (b : ℝ),
    is_lower_bound A m ⇒ is_in A b ⇒ m ≤ b.
Proof.
    Take A : subsets_R.
    Take m : ℝ.
    Take b: ℝ.
    (** TODO: fix 
    Assume m_low_bd : (is_lower_bound A m). *)
    intro m_low_bd.
    Assume b_in_A : (is_in A b).
    Define c := (mk_element_R (is_in A) b b_in_A).
    Expand the definition of is_lower_bound in m_low_bd.
    By m_low_bd it holds that m_le_c : (m ≤ c).
    We conclude that (m ≤ b).
Qed.

Global Hint Resolve bounded_by_upper_bound_propform : additional.
Global Hint Resolve bounded_by_lower_bound_propform : additional.
(** ### **Hints***)
Hint Extern 1 => (unfold is_sup) : unfolds.
Hint Extern 1 => (unfold is_inf) : unfolds.
