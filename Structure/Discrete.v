Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Structure.Groupoid.
Require Export Category.Structure.Thin.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import EqNotations.

(* Usually one defines a category to be discrete, if (informally)
   [∀ x y (f : x ~> y), x = y ∧ f ≈ id]. But this definition is too
   strong, since in our definition of [Cat] we only consider
   categories up to equivalence.

   So we define a category to be discrete, if all morphisms are
   isomorphisms and all parallel morphisms are equal (i.e. [≈]).
   I.e. a thin Groupoid.
*)
Definition is_Discrete (C : Category) :=
  is_Thin C ∧ is_Groupoid C.

Lemma is_Discrete_invariant : Invariant is_Discrete.
Proof.
  apply Invariant_one_sided.
  proper.
  destruct X0.
  split.
  - apply (is_Thin_invariant x); assumption.
  - apply (is_Groupoid_invariant x); assumption.
Qed.
