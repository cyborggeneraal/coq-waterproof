(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Require Import Coq.Reals.Reals.
Require Import Lra.

(* Set Default Timeout 1. *)

Require Import Waterproof.Automation.
Require Import Waterproof.Notations.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

Waterproof Enable Automation RealsAndIntegers.

(* lra only works in the [R_scope] *)
Local Open Scope R_scope.
Lemma zero_lt_one: 0 < 1.
Proof.
    ltac1:(lra).
Qed.

(* This axiom does not make sense, 
    but therefore we can be sure that [waterprove]
    does not know it without *explicitly* being told to use it.*)
Local Parameter x_var : R.
Local Parameter H_x_is_10 : x_var = 10.
Lemma x_is_10 : x_var = 10.
Proof.
  exact H_x_is_10.
Qed.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [By ... it holds that ... : ...] *)

(** * Test 1
    Base case: intoduce a sublemma with a lemma that proves it
    immediately.

    NOTE: [waterprove] can apparently also find
    [zero_lt_one] by itself.
*)
Lemma test_by_it_holds_1: 0 = 0.
Proof.
    By zero_lt_one it holds that (0 < 1).
Abort.

(** * Test 2
    Base case: intoduce a sublemma with a lemma that proves it
    immediately. 
    The sublemma cannot be proven without the given lemma!

*)

Lemma test_by_it_holds_2: True.
Proof.
    (* This is just to test if the extra lemma is really needed: *)
    Fail It holds that (x_var = 10).
    
    By (H_x_is_10) it holds that (x_var = 10).
Abort.

(** * Test 3
    Corner case: try a sublemma that cannot be solved,
    at least not with the default lemmas and the provided lemma.
*)
Lemma test_by_it_holds_3: 0 = 0.
Proof.
    Fail By zero_lt_one it holds that (1 > 2).
Abort.


(* -------------------------------------------------------------------------- *)
(** * Testcases for [It holds that ... : ...] *)

(** * Test 1
    Base case: intoduce a sublemma that can be proven immediately.
*)
Lemma test_it_holds_1: 0 = 0.
Proof.
    It holds that (True) (i).
    assert_hyp_has_type @i constr:(True).
Abort.


(** * Test 2
    Corner case: try a sublemma that cannot be solved,
    at least not with the default lemmas [waterprove] uses.
*)
Lemma test_it_holds_2: 0 = 0.
Proof.
    Fail It holds that (1 > 2).
Abort.

(** * Example for the SUM.
    Somewhat more realistic context.
*)

Open Scope nat_scope.
Inductive even : nat -> Prop :=
    even0 : even 0
  | evenS : forall x:nat, even x -> even (S (S x)).

Lemma it_holds_example: forall x:nat, x > 1 /\ x < 3 -> even x.
Proof.
    intros x h.
    It holds that (x = 2) (i).
    rewrite (i). (* Change the goal to "even 2"*)
    apply evenS. (* Change the goal to "even 0"*)
    apply even0.
Qed.


(* Test 4: Check what error is thrown when a hypothesis identifier is already in use.*)
Goal forall x:nat, x > 1 /\ x < 3 -> even x.
Proof.
    intros x h.
    Fail It holds that (x = 2) (h).
    It holds that (x = 2) (i).
Abort.


(** Tests for restricted version of 'By ...' clause *)
Variable A B : Prop.
Variable f : A -> B.

(* Test 5: regular check that assertion works. *)
Goal A -> False.
Proof.
  intro H.
  pose f.
  It holds that B.
Abort.

(* Test 6: check that assertion works with label *)
Goal A -> False.
Proof.
  intro H.
  pose f.
  It holds that B (i).
Abort.

(* Test 7: check that assertion fails with label that is already used. *)
Goal A -> False.
Proof.
  intro H.
  pose f.
  Fail It holds that B (H).
Abort.

(* Test 7b: assertion fails if label already used, even before it is checked whether 
    assertion is actually valid.
 *)
Goal A -> False.
Proof.
intro H.
Fail It holds that B (H).
Abort.

(* Test 8: 'By ...' succeeds if additional lemma is needed for proof assertion. *)
Goal A -> False.
Proof.
  intro H.
  By f it holds that B.
Abort.
(* Test 8b: also when lemma is included in local hypotheses. *)
Goal A -> False.
Proof.
  intro H.
  pose f.
  By f it holds that B.
Abort.

(* Test 9: 'By ...' fails if additional lemma is not enough to prove assertion. *)
Goal False.
Proof.
  Fail By f it holds that B.
Abort.

(* Test 10: 'By ...' succeeds if additional lemma is not needed for proof assertion. *)
Variable g : B -> A.
Goal A -> False.
Proof.
  intro H.
  pose f.
  Fail By g it holds that B.
Abort.




