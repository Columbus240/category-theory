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

Require Import Category.Instance.Cat.

Lemma is_Groupoid_invariant : Invariant is_Groupoid.
Proof.
  apply Invariant_one_sided.
  proper.
  - destruct X.
    simpl in to, from.
    destruct iso_to_from.
    unshelve eexists.
    + assumption.
    + pose proof (e _ _ f).
      simpl in X.
      red in X0.
      specialize (X0 _ _ (fmap[from] f)) as [g].
      unshelve eapply (_ ∘ fmap[to] (Isomorphism.from g) ∘ _);
        apply x1.
    + simpl.
      destruct X0.
      simpl in e.
      simpl.
      destruct x2 as [? x2].
      simpl in e0.
      simpl. subst.
      apply (iso_to_epic (x1 y0)).
      apply (iso_from_monic (x1 y0)).
      rewrite id_left.
      rewrite Isomorphism.iso_from_to.
      rewrite !comp_assoc_sym.
      rewrite Isomorphism.iso_from_to.
      rewrite id_right.
      rewrite !comp_assoc.
      rewrite <- (e _ _ f).
      simpl.
      rewrite <- fmap_comp.
      rewrite iso_to_from.
      cat.
    + simpl.
      destruct X0.
      simpl in e.
      destruct x2 as [? x2].
      simpl in e0. simpl. subst.
      apply (iso_to_epic (x1 x0)).
      apply (iso_from_monic (x1 x0)).
      rewrite id_left.
      rewrite Isomorphism.iso_from_to.
      rewrite !comp_assoc.
      rewrite Isomorphism.iso_from_to.
      rewrite id_left.
      rewrite !comp_assoc_sym.
      rewrite (comp_assoc _ f _).
      rewrite <- (e _ _ f).
      simpl.
      rewrite <- fmap_comp.
      rewrite iso_from_to0.
      cat.
  - simpl.
    destruct X. simpl.
    destruct iso_to_from.
    simpl.
    reflexivity.
Qed.
