Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The "thin-ification" of a category. I.e. define all parallel
   morphisms to be equal. *)
Program Definition Thin (C : Category) : Category :=
  {| obj := obj[C];
     hom := @hom C;
     homset X Y := full_setoid _;
     compose := @compose C;
  |}.

Require Import Category.Structure.Thin.

Lemma Thin_is_Thin (C : Category) :
  is_Thin (Thin C).
Proof.
  red. intros. constructor.
Qed.
