Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Morphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Isomorphism.

Context {C : Category}.

(* This defines what it means for two objects in a category to be
   "isomorphic". This requires both witnesses to the isomoprhism, and proof
   their compositions are equivalent to identity in both directions. Since
   this is a computationally relevant definition, having an isomorphism allows
   for conversion of objects within definitions.

   An isomorphism in Cat is the same as an equivalence of categories. In order
   to get actual isomorphism between categories, the compositions F ○ G and G
   ○ F need to be equal, rather than equivalent, to identity. Since this is
   usually too strong a notion, it does not have its own abstraction here. *)

Class Isomorphism (x y : C) : Type := {
  to   : x ~> y;
  from : y ~> x;

  iso_to_from : to ∘ from ≈ id;
  iso_from_to : from ∘ to ≈ id
}.

Arguments to {x y} _.
Arguments from {x y} _.
Arguments iso_to_from {x y} _.
Arguments iso_from_to {x y} _.

Infix "≅" := Isomorphism (at level 91) : category_scope.

Global Program Instance iso_id {x : C} : x ≅ x := {
  to   := id;
  from := id
}.

Global Program Definition iso_sym {x y : C} `(f : x ≅ y) : y ≅ x := {|
  to   := from f;
  from := to f;

  iso_to_from := iso_from_to f;
  iso_from_to := iso_to_from f
|}.

Global Program Definition iso_compose {x y z : C} `(f : y ≅ z) `(g : x ≅ y) :
  x ≅ z := {|
  to   := to f ∘ to g;
  from := from g ∘ from f
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to g)).
  rewrite iso_to_from; cat.
  apply iso_to_from.
Defined.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (from f)).
  rewrite iso_from_to; cat.
  apply iso_from_to.
Defined.

Global Program Instance isomorphism_equivalence : Equivalence Isomorphism := {
  Equivalence_Reflexive  := @iso_id;
  Equivalence_Symmetric  := @iso_sym;
  Equivalence_Transitive := fun _ _ _ g f => iso_compose f g
}.

Definition ob_equiv : crelation C := fun x y => x ≅ y.

Global Program Instance ob_setoid : Setoid C.

Definition isomorphism_equiv {x y : C} : crelation (x ≅ y) :=
  fun f g => (to f ≈ to g) * (from f ≈ from g).

Global Program Instance isomorphism_equiv_equivalence {x y : C} :
  Equivalence (@isomorphism_equiv x y).
Next Obligation. firstorder reflexivity. Qed.
Next Obligation. firstorder; symmetry; assumption. Qed.
Next Obligation.
  firstorder;
    try (transitivity (to y0); assumption);
    try (transitivity (from y0); assumption).
Qed.

Global Program Instance isomorphism_setoid {x y : C} : Setoid (x ≅ y) := {
  equiv := isomorphism_equiv;
  setoid_equiv := isomorphism_equiv_equivalence
}.

Local Obligation Tactic := program_simpl.

Global Program Instance Isomorphism_Proper :
  Proper (Isomorphism ==> Isomorphism ==> iffT) Isomorphism.
Next Obligation.
  proper.
    refine (iso_compose _ (iso_sym X)).
    exact (iso_compose _ X1).
  refine (iso_compose _ X).
  refine (iso_compose _ X1).
  exact (iso_sym X0).
Defined.

Global Program Instance Isomorphism_flip_Proper :
  Proper (Isomorphism ==> Isomorphism ==> Basics.flip iffT) Isomorphism.
Next Obligation.
  unfold Basics.flip.
  proper.
    refine (iso_compose _ X).
    refine (iso_compose _ X1).
    exact (iso_sym X0).
  refine (iso_compose _ (iso_sym X)).
  exact (iso_compose _ X1).
Defined.

End Isomorphism.

Declare Scope isomorphism_scope.
Delimit Scope isomorphism_scope with isomorphism.
Open Scope isomorphism_scope.

Notation "x ≅ y" := (@Isomorphism _%category x%object y%object)
  (at level 91) : isomorphism_scope.
Notation "x ≅[ C ] y" := (@Isomorphism C%category x%object y%object)
  (at level 91, only parsing) : isomorphism_scope.

Arguments to {_%category x%object y%object} _%morphism.
Arguments from {_%category x%object y%object} _%morphism.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

Coercion to : Isomorphism >-> hom.

Notation "f '⁻¹'" := (from f) (at level 9, format "f '⁻¹'") : morphism_scope.

Global Hint Unfold isomorphism_equiv : core.

Ltac isomorphism :=
  unshelve (refine {| to := _; from := _ |}; simpl; intros).

Global Program Instance iso_to_monic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Monic iso.
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_from_to iso).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

Global Program Instance iso_from_monic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Monic (iso⁻¹).
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_to_from iso).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

Global Program Instance iso_to_epic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Epic iso.
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_to_from iso).
  rewrite !comp_assoc.
  rewrites; reflexivity.
Qed.

Global Program Instance iso_from_epic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Epic (iso⁻¹).
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_from_to iso).
  rewrite !comp_assoc.
  rewrites; reflexivity.
Qed.

Global Program Instance Monic_Retraction_Iso
        {C : Category} {x y : C} `(r : @Retraction _ _ _ f) `(m : @Monic _ _ _ f) :
  x ≅ y := {
  to := f;
  from := retract
}.
Next Obligation.
  destruct r; simpl.
  apply monic.
  rewrite comp_assoc.
  rewrite <- retract_comp; cat.
Qed.
Next Obligation.
  destruct r; simpl.
  apply monic.
  rewrite comp_assoc.
  rewrite retract_comp; cat.
Qed.

Global Program Instance Epic_Section_Iso
        {C : Category} {x y : C} `(s : @Section _ _ _ f) `(e : @Epic _ _ _ f) :
  x ≅ y := {
  to := f;
  from := section
}.
Next Obligation.
  destruct s; simpl.
  specialize (epic y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite section_comp; cat.
Qed.
Next Obligation.
  destruct s; simpl.
  specialize (epic y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite <- section_comp; cat.
Qed.

Notation "f ⊙ g" := (@iso_compose _ _ _ _ f g) (at level 40, left associativity).

Lemma iso_from_unique {C : Category} {x y : C} (iso : x ≅ y) (g : y ~> x) :
  iso ∘ g ≈ id ->
  g ∘ iso ≈ id ->
  g ≈ from iso.
Proof.
  intros.
  rewrite <- id_left.
  rewrite <- (iso_from_to iso).
  rewrite comp_assoc_sym.
  rewrite X.
  apply id_right.
Qed.

Corollary iso_to_unique {C : Category} {x y : C} (iso : x ≅ y) (g : x ~> y) :
  (from iso) ∘ g ≈ id ->
  g ∘ (from iso) ≈ id ->
  g ≈ to iso.
Proof.
  apply (Isomorphism_from_unique (iso_sym iso)).
Qed.

(* A property is called [Invariant] if it is preserved by
   isomorphisms. *)
Definition Invariant {C : Category} (P : C -> Type) :=
  Proper (Isomorphism ==> iffT) P.

(* by symmetry, it suffices to prove only one direction of [iffT] in
   the definition of [Invariant] *)
Lemma Invariant_one_sided {C : Category} (P : C -> Type) :
  Proper (Isomorphism ==> arrow) P -> Invariant P.
Proof.
  intros.
  red in X.
  proper.
  - specialize (X x y X0).
    apply X. assumption.
  - specialize (X y x (iso_sym X0)).
    apply X. assumption.
Qed.

(* If we have multiple equivalent formulations of a property and one
   is invariant, then the other is as well. *)
Lemma Invariant_Proper' (C : Category) (P0 P1 : C -> Type) :
  (forall x : C, P0 x ↔ P1 x) ->
  Invariant P0 -> Invariant P1.
Proof.
  intros.
  apply Invariant_one_sided.
  proper.
  rewrite <- X in *.
  apply (X0 x); assumption.
Qed.

Lemma Invariant_Proper (C : Category) (P0 P1 : C -> Type) :
  (forall x : C, P0 x ↔ P1 x) ->
  Invariant P0 ↔ Invariant P1.
Proof.
  intros; split; apply Invariant_Proper'; try assumption.
  symmetry. apply X.
Qed.
