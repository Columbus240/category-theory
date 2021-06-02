Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Naturality.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoidal.

Context {C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;                        (* unit_obj *)
  tensor : C ∏ C ⟶ C where "x ⨂ y" := (tensor (x, y));

  unit_left  {x} : I ⨂ x ≅ x;  (* lambda *)
  unit_right {x} : x ⨂ I ≅ x;  (* rho *)

  tensor_assoc {x y z} : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z);  (* alpha *)

  (* alpha, lambda and rho are all natural isomorphisms. *)

  to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ unit_left << I ⨂ x ~~> y >> unit_left ∘ bimap id g;
  from_unit_left_natural {x y} (g : x ~> y) :
    bimap id g ∘ unit_left⁻¹ << x ~~> I ⨂ y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ unit_right << x ⨂ I ~~> y >> unit_right ∘ bimap g id;
  from_unit_right_natural {x y} (g : x ~> y) :
    bimap g id ∘ unit_right⁻¹ << x ~~> y ⨂ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap g (bimap h i) ∘ tensor_assoc
      << (x ⨂ z) ⨂ v ~~> y ⨂ w ⨂ u >>
    tensor_assoc ∘ bimap (bimap g h) i;

  from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap (bimap g h) i ∘ tensor_assoc⁻¹
      << x ⨂ z ⨂ v ~~> (y ⨂ w) ⨂ u >>
    tensor_assoc⁻¹ ∘ bimap g (bimap h i);

  (* The above observe the following coherence conditions *)

  triangle_identity {x y} :
    bimap unit_right id
      << (x ⨂ I) ⨂ y ~~> x ⨂ y >>
    bimap id unit_left ∘ tensor_assoc;

  pentagon_identity {x y z w} :
    bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
      << ((x ⨂ y) ⨂ z) ⨂ w ~~> x ⨂ (y ⨂ (z ⨂ w)) >>
    tensor_assoc ∘ tensor_assoc
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "x ⨂ y" := (@tensor _ _ (x%object, y%object))
  (at level 30, right associativity) : object_scope.
Notation "x ⨂[ M ] y" := (fobj[@tensor _ M] (x, y))
  (at level 30, only parsing, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.
Notation "f ⨂[ M ] g" := (bimap[@tensor _ M] f g)
  (at level 30, only parsing, right associativity) : morphism_scope.

Require Import Category.Structure.Terminal.

Program Fixpoint tensor_power_obj {C : Category} `{@Terminal C} `{@Monoidal C}
         (n : nat) (x : C) :=
  match n with
  | O => terminal_obj
  | S n' => tensor (x, tensor_power_obj n' x)
  end.

Definition tensor_power_fmap {C : Category} `{@Terminal C} `{@Monoidal C} (n : nat) {x y : C} (f : x ~> y) : (tensor_power_obj n x) ~> (tensor_power_obj n y).
Proof.
  induction n.
  - simpl. apply one.
  - simpl.
    apply tensor.
    simpl.
    split; assumption.
Defined.

Program Definition tensor_power {C : Category} `{@Terminal C} `{@Monoidal C}
         (n : nat) : C ⟶ C :=
  {| fobj := tensor_power_obj n;
     fmap x y f := tensor_power_fmap n f;
  |}.
Next Obligation.
  proper.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite X. reflexivity.
Qed.
Next Obligation.
  induction n.
  - simpl. apply one_unique.
  - simpl. rewrite IHn. cat.
Qed.
Next Obligation.
  induction n.
  - simpl. cat.
  - simpl. rewrite IHn.
    rewrite <- fmap_comp.
    simpl.
    reflexivity.
Qed.
