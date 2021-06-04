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

Require Import Category.Instance.Cat.
Require Import Category.Theory.Isomorphism.

(* thin-ness is preserved by equivalence. *)
Lemma is_Thin_invariant : Invariant is_Thin.
Proof.
  apply Invariant_one_sided.
  proper.
  destruct X.
  red in X0.
  simpl in to, from.
  specialize (X0 _ _ (fmap[from] f) (fmap[from] g)).
  assert (fmap[to] (fmap[from] f) ≈ fmap[to] (fmap[from] g)).
  { rewrite X0. reflexivity. }
  destruct iso_to_from.
  simpl in *.
  rewrite !e in X.
  apply (iso_from_monic (x1 y0)).
  apply (iso_to_epic (x1 x0)).
  assumption.
Qed.
