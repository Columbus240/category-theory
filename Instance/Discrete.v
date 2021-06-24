Set Warnings "-notation-overridden".
Set Universe Polymorphism.

Require Import Category.Lib.Datatypes.
Require Import Category.Lib.Setoid.
Require Import Category.Theory.Category.
Require Import Category.Structure.Discrete.

(* The discrete category over a given type/setoid. *)
Definition Discrete {X : Type} (S : Setoid X) : Category :=
  {| obj := X;
     hom x y := x ≈ y;
     homset x y := full_setoid _;

     id := @Equivalence_Reflexive _ _ (@setoid_equiv _ S);
     compose := λ (x y z : X) (f : y ≈ z) (g : x ≈ y), transitivity g f;

     compose_respects _ _ _ _ _ _ _ _ _ := tt;
     id_left _ _ _ := tt;
     id_right _ _ _ := tt;

     comp_assoc _ _ _ _ _ _ _ := tt;
     comp_assoc_sym _ _ _ _ _ _ _ := tt;
  |}.
