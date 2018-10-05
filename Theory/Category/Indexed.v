Set Warnings "-notation-overridden".

Require Import Category.Theory.Category.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition IndexedCategory (S : Category) := S^op ⟶ Cat.
