Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Category.Indexed.
Require Export Category.Theory.Functor.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
(* Unset Transparent Obligations. *)

(** The inhabitants of a Coq type can be seen as a concrete category whose
    only morphisms are identities. *)

Program Definition MembersOf (A : Type) : Category := {|
  obj := A;
  hom := fun x y => x = y;
  homset := fun x y => {| equiv := fun _ _ => x = y |}
|}.

(** The category of transformations between predicates over a Coq type. *)

Program Definition Predicates (A : Type) : Category := {|
  obj := A -> Type;
  hom := fun x y => forall i, x i -> y i;
  homset := fun x y =>
    {| equiv := fun f g => ∀ i x, f i x = g i x |};
  id := fun _ _ a => a;
  compose := fun _ _ _ x y _ a => x _ (y _ a);
|}.
Next Obligation.
  equivalence.
  congruence.
Qed.
Next Obligation.
  proper.
  congruence.
Qed.

Require Import Category.Instance.Coq.

Program Definition TransformsIndexed : IndexedCategory Coq := {|
  fobj := Predicates;
  fmap := fun _ _ h =>
    {| fobj := fun x => x \o h;
       fmap := fun _ _ f a => f (h a) |}
|}.
Next Obligation.
  proper.
  - simpl.
    construct; try congruence; simpl_eq; simpl.
    + now destruct (H i).
    + now destruct (H i).
  - simpl; simpl_eq; simpl.
    now destruct (H i).
Qed.

(** An indexed functor is a functor between indexed categories. *)

Class IndexedFunctor (S : Category) (C D : IndexedCategory S) : Type := {
  iobj {i : S} : C i ⟶ D i;
  imap_iso {x y : S} (f : x ~> y) :
    fmap[D] f ○ @iobj y ≅[Fun] @iobj x ○ fmap[C] f;
  imap {x y : S} (f : x ~> y) : @iobj x _ ~> @iobj x _
}.

(* Any object from Coq^op indexes the coslice of Coq on that object. *)

Program Definition Predicated : IndexedCategory Coq := {|
  fobj := fun x => Coslice Coq x;
  fmap := fun _ _ f => _
|}.
Next Obligation.
  construct.
  - destruct X.
    exists x.
    intuition.
  - destruct x, y; simpl in *.
    destruct f0.
    exists x1.
    intros.
    apply e.
  - proper.
    simpl in *.
    congruence.
  - destruct x; simpl; auto.
  - destruct x, y, z, f0, g; simpl in *.
    congruence.
Defined.
Next Obligation.
  proper; simpl.
  - construct.
    + exists id; intros; simpl.
      now rewrite H.
    + exists id; intros; simpl.
      now rewrite H.
    + auto.
    + auto.
  - auto.
Qed.

Program Definition Coq_IndexedFunctor :
  IndexedFunctor _ TransformsIndexed TransformsIndexed.
Proof.
  construct.
  - construct; intuition.
  - construct; simpl.
    + construct; simpl; auto.
    + construct; simpl; auto.
    + auto.
    + auto.
Defined.

Goal forall x y f g, transform[to (@imap _ _ _ Coq_IndexedFunctor x y f)] = g.
Proof.
  simpl; intros.
Abort.
