Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op :=
  @Build_Functor (C^op) (D^op) F
    (λ (x y : C ^op) (f : x ~{ C ^op }~> y), @fmap C D F y x f)
    (λ (x y : C ^op) (f g : x ~{ C ^op }~> y), @fmap_respects _ _ F y x f g)
    (λ x : C ^op, fmap_id)
    (λ (x y z : C ^op) (f : y ~{ C ^op }~> z)
      (g : x ~{ C ^op }~> y), @fmap_comp _ _ F _ _ _ g f).

Notation "F ^op" := (@Opposite_Functor _ _ F)
  (at level 7, format "F ^op") : functor_scope.

Open Scope functor_scope.

Corollary Opposite_Functor_invol `{F : C ⟶ D} : (F^op)^op = F.
Proof. reflexivity. Qed.

Definition contramap `{F : C^op ⟶ D} `(f : x ~{C}~> y) :
  F y ~{D}~> F x := fmap (op f).

Global Program Instance Faithful_op {C D F} (H : @Faithful C D F) : Faithful F^op :=
  {| fmap_inj _ _ _ _ X :=
       @fmap_inj _ _ _ H _ _ _ _ X |}.

Global Program Instance Full_op {C D F} {H : @Full C D F} : Full F^op :=
  {| prefmap x y g := @prefmap _ _ _ H _ _ g;
     prefmap_respects _ _ := prefmap_respects;
     prefmap_id := prefmap_id;
     prefmap_comp _ _ _ _ _ := prefmap_comp _ _ _ _ _;
     fmap_sur _ _ := fmap_sur;
   |}.
