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
   isomorphisms and all morphisms are equal (i.e. [≈]).
   I.e. a thin Groupoid.
*)
Definition is_Discrete (C : Category) :=
  is_Thin C ∧ is_Groupoid C.
