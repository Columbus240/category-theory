Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import EqNotations.

(* In a thin category, all parallel morphisms are equal (i.e. [≈]). *)
Definition is_Thin (C : Category) :=
  forall x y (f g : x ~> y), f ≈ g.
