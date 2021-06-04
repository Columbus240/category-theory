Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import EqNotations.

(* A category is a groupoid, if all morphisms are isomorphisms. *)
Definition is_Groupoid (C : Category) :=
  forall x y (f : x ~> y), ∃ iso, (to iso = f).
