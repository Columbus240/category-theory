Set Warnings "-notation-overridden".
Set Universe Polymorphism.

Require Import Category.Lib.Datatypes.
Require Import Category.Lib.Setoid.
Require Import Category.Theory.Category.
Require Import Category.Structure.Discrete.

(* The discrete category over a given type/setoid. *)
Program Definition Discrete {X : Type} (S : Setoid X) : Category :=
  {| obj := X;
     hom x y := x ≈ y;
     homset x y := full_setoid _;

     id := @Equivalence_Reflexive _ _ (@setoid_equiv _ S);
     compose := λ (x y z : X) (f : y ≈ z) (g : x ≈ y), transitivity g f
  |}.
Next Obligation.
  proper.
Qed.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.

Lemma Discrete_is_Discrete {X : Type} (S : Setoid X) :
  is_Discrete (Discrete S).
Proof.
  split.
  - red. intros. constructor.
  - red. intros.
    unshelve eexists.
    + unshelve econstructor.
      * assumption.
      * simpl in *. symmetry. assumption.
      * constructor.
      * constructor.
    + reflexivity.
Qed.

Require Import Category.Instance.Cat.
Require Import Category.Theory.Isomorphism.

(* A category is discrete iff it is equivalent to a [Discrete]
   category over some setoid. *)
Proposition Discrete_char (C : obj[Cat]) :
  (is_Discrete C) ↔ { X : Type & { S : Setoid X & C ≅ (Discrete S)}}.
Proof.
  split.
  - intros.
    destruct X.
    exists (obj[C]).
    exists ob_setoid.
    unshelve econstructor.
    + unshelve econstructor.
      * apply Datatypes.id.
      * simpl. intros.
        apply i0. assumption.
      * intros. proper.
      * intros. simpl. exact tt.
      * intros. simpl. exact tt.
    + unshelve econstructor.
      * apply Datatypes.id.
      * simpl. intros.
        destruct f. assumption.
      * simpl. intros. proper.
      * simpl. reflexivity.
      * simpl. intros.
        subst. simpl.
        cat.
    + simpl.
      eexists.
      * intros. reflexivity.
      * constructor.
    + simpl. cat.
  - intros.
    destruct X as [X [S ?]].
    destruct (Discrete_is_Discrete S).
    destruct i; simpl in to, from.
    assert (is_Thin C).
    { red; intros.
      pose (fmap[to] f).
      pose (fmap[to] g).
      specialize (i0 _ _ h h0).
      unfold h, h0 in i0.
      pose (fmap[from] h).
      pose (fmap[from] h0).
      assert (h1 ≈ h2).
      { unfold h1, h2, h, h0.
        rewrite i0. reflexivity.
      }
      simpl in *.
      destruct iso_from_to.
      unfold h1, h2, h, h0 in H.
      clear h1 h2 h h0.
      rewrite e in H.
      rewrite e in H.
      apply (iso_from_monic (x0 y)).
      apply (iso_to_epic (x0 x)).
      assumption.
    }
    split.
    { assumption. }
    red; intros.
    specialize (i1 _ _ (fmap[to] f)) as [iso].
    pose (fmap_iso from _ _ iso).
    destruct iso_from_to.
    unshelve eexists.
    + unshelve eexists.
      * apply f.
      * simpl in x0, e0.
        pose proof (x0 x).
        pose proof (x0 y).
        unshelve eapply (_ ∘ (Isomorphism.from i) ∘ _).
        -- apply X1.
        -- apply X2.
      * simpl. apply X0.
      * simpl. apply X0.
    + simpl. reflexivity.
Defined.
