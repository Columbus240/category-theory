Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Require Import Lib.Tactics.
Require Import Lib.Setoid.
Require Import Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import RelationClasses.

Program Definition Pos : Category := {|
  obj  := { A : Type & { R : A -> A -> Prop & { PO : PreOrder R & @PartialOrder _ eq eq_equivalence R PO }}};
  hom  := fun A B : _ =>
            { f : projT1 A -> projT1 B |
              forall a0 a1 : projT1 A,
                (projT1 (projT2 A)) a0 a1 ->
                (projT1 (projT2 B)) (f a0) (f a1) };
  homset := fun _ _ =>
              {| equiv := fun f g =>
                            forall x,
                              (proj1_sig f) x =
                              (proj1_sig g) x |};
  id := fun _ =>
          exist _ (fun x => x) _;
  compose := fun _ _ _ g f =>
               exist _ (fun x => g (f x)) _;
|}.
Next Obligation.
  equivalence.
  transitivity ((` y) x0); auto.
Qed.
Next Obligation.
  proper.
  simpl in *.
  rewrite H, H0.
  reflexivity.
Qed.

Require Import Poset.

Require Import Construction.Subcategory.
Require Import Instance.Cat.

Program Definition Pos' : Subcategory Cat :=
  {| sobj C := { T : Type & { R : relation T & { P : PreOrder R & { PA : @Antisymmetric _ eq eq_equivalence R & Poset P = C }}}};
     shom _ _ _ _ _ := True;
  |}.

Definition Pos0 := Sub _ Pos'.

Require Import Theory.Natural.Transformation.

Program Definition NaturalTransform_Id {C D : Category}
        (F : @Functor C D) : @Transform C D F F := {|
  transform x := id[F x];
  |}.
Next Obligation.
  cat.
Qed.
Next Obligation.
  cat.
Qed.

(* Vertical composition of natural transformations *)
Program Definition NatTransform_vert_comp {C D : Category}
        {F G H : @Functor C D} (NT0 : @Transform C D F G)
        (NT1 : @Transform C D G H) : @Transform C D F H := {|
  transform x := (transform[NT1] x) ∘ (transform[NT0] x);
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  rewrite naturality.
  reflexivity.
Qed.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- naturality_sym.
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  rewrite naturality_sym.
  reflexivity.
Qed.

Global Program Instance Transform_Setoid {C D : Category} (F G : @Functor C D) :
  Setoid (@Transform C D F G) :=
  {| equiv N0 N1 :=
       forall x, equiv (transform[N0] x) (transform[N1] x); |}.
Next Obligation.
  equivalence.
  transitivity (y x0); auto.
Qed.

Axiom Admit : forall T, T.

(* The category of functors between [C] and [D] *)
Program Definition FunctorCat (C D : Category) := {|
  obj := @Functor C D;
  hom := @Transform C D;
  homset F G := @Transform_Setoid C D F G;
  id := NaturalTransform_Id;
|}.
Next Obligation.
  refine (NatTransform_vert_comp g f).
Defined.
Next Obligation.
  proper.
Qed.
Next Obligation.
  cat.
Qed.
Next Obligation.
  cat.
Qed.
Next Obligation.
  cat.
Qed.
Next Obligation.
  cat.
Qed.

Definition NatIsom {C D : Category} (F G : @Functor C D) : Type :=
  @Isomorphism (FunctorCat C D) F G.

Record Cat_Equivalent (C D : Category) := {
  ce_to : @Functor C D;
  ce_from : @Functor D C;
  ce_d_isom : NatIsom (Compose ce_to ce_from) (@Id D);
  ce_c_isom : NatIsom (Compose ce_from ce_to) (@Id C);
}.

Lemma Pos_to_Pos0 : @Functor Pos Pos0.
Proof.
  unshelve econstructor.
  + simpl.
    intros.
    destruct X as [A [R [PO]]].
    exists (Poset PO), A, R, PO.
    unshelve eexists.
    reflexivity.
  + intros. simpl.
    destruct x as [Ax [Rx [POx]]], y as [Ay [Ry [POy]]].
    simpl in *.
    unshelve eexists.
    2: constructor.
    unshelve econstructor.
    * simpl. refine (proj1_sig f).
    * intros.
      simpl in *.
      pose proof (proj2_sig f).
      apply (H _ _ f0).
    * intros. simpl. proper.
    * intros. cat.
    * intros. cat.
  + intros.
    destruct x as [Ax [Rx [POx]]], y as [Ay [Ry [POy]]].
    simpl.
    proper.
    rewrite H.
    reflexivity.
  + intros.
    destruct x as [Ax [Rx [POx]]].
    simpl.
    unshelve eexists.
    * intros. reflexivity.
    * intros. constructor.
  + intros.
    destruct x as [Ax [Rx [POx]]],
             y as [Ay [Ry [POy]]],
             z as [Az [Rz [POz]]].
    simpl in *.
    unshelve eexists; intros.
    * reflexivity.
    * constructor.
Defined.

Lemma Pos0_to_Pos : @Functor Pos0 Pos.
Proof.
  unshelve econstructor.
  + simpl. intros.
    destruct X as [x [T [R [P [PA]]]]].
    exists T, R, P.
    repeat red. intros.
    split; intros.
    * repeat red. subst; split.
      -- reflexivity.
      -- red. reflexivity.
    * repeat red in H. destruct H.
      red in H0. apply PA; assumption.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]],
             y as [y [Ty [Ry [Py [PAy]]]]].
    simpl.
    destruct f. simpl in *.
    subst. clear s.
    destruct x0. simpl in *.
    exists fobj.
    intros.
    auto.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]],
             y as [y [Ty [Ry [Py [PAy]]]]].
    simpl in *. subst. simpl in *.
    proper. simpl in *.
    pose proof (x1 x0).
    destruct H.
    apply PAy; assumption.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]].
    simpl in *. subst. simpl in *.
    auto.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]],
             y as [y [Ty [Ry [Py [PAy]]]]],
             z as [z [Tz [Rz [Pz [PAz]]]]].
    simpl in *. subst. simpl in *.
    intros. destruct g as [g], f as [f].
    simpl. reflexivity.
Defined.

Lemma Pos_Pos0_Equiv_Pos0_0 :
  @Transform _ _ (Compose Pos_to_Pos0 Pos0_to_Pos) (@Id _).
Proof.
  unshelve econstructor.
  + simpl. intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]].
    unshelve eexists.
    2: { constructor. }
    simpl.
    subst.
    apply Id.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]],
             y as [y [Ty [Ry [Py [PAy]]]]].
    destruct f as [f].
    simpl in *.
    subst.
    simpl.
    unshelve eexists.
    * intros.
      reflexivity.
    * intros.
      assumption.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]],
             y as [y [Ty [Ry [Py [PAy]]]]].
    destruct f as [f].
    simpl in *.
    subst. simpl.
    unshelve eexists.
    * intros.
      reflexivity.
    * intros.
      assumption.
Defined.

Lemma Pos_Pos0_Equiv_Pos0_1 :
  @Transform _ _ (@Id _) (Compose Pos_to_Pos0 Pos0_to_Pos).
Proof.
  unshelve econstructor.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]].
    simpl.
    unshelve eexists.
    2: { constructor. }
    subst.
    apply Id.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]],
             y as [y [Ty [Ry [Py [PAy]]]]].
    destruct f as [f].
    simpl in *.
    subst. simpl.
    unshelve eexists.
    * intros.
      reflexivity.
    * intros.
      assumption.
  + intros.
    destruct x as [x [Tx [Rx [Px [PAx]]]]],
             y as [y [Ty [Ry [Py [PAy]]]]].
    destruct f as [f].
    simpl in *.
    subst. simpl.
    unshelve eexists.
    * intros.
      reflexivity.
    * intros.
      assumption.
Defined.

Lemma Pos_Pos0_Equiv_Pos_0 :
  @Transform _ _ (Compose Pos0_to_Pos Pos_to_Pos0) (@Id _).
Proof.
  unshelve econstructor.
  - intros.
    simpl in x.
    destruct x as [Ax [Rx [POx]]].
    simpl.
    eexists (Datatypes.id).
    intros. assumption.
  - intros.
    simpl in x, y.
    destruct x as [Ax [Rx [POx]]],
             y as [Ay [Ry [POy]]].
    simpl.
    intros. reflexivity.
  - intros.
    destruct x as [Ax [Rx [POx]]],
             y as [Ay [Ry [POy]]].
    simpl. intros. reflexivity.
Defined.

Lemma Pos_Pos0_Equiv_Pos_1 :
  @Transform _ _ (@Id _) (Compose Pos0_to_Pos Pos_to_Pos0).
Proof.
  unshelve econstructor.
  - intros.
    simpl in x.
    destruct x as [Ax [Rx [POx]]].
    simpl.
    eexists (Datatypes.id).
    intros. assumption.
  - intros.
    simpl in x, y.
    destruct x as [Ax [Rx [POx]]],
             y as [Ay [Ry [POy]]].
    simpl.
    intros. reflexivity.
  - intros.
    destruct x as [Ax [Rx [POx]]],
             y as [Ay [Ry [POy]]].
    simpl. intros. reflexivity.
Defined.

(* Claim: [Pos] and [Pos0] are equivalent categories. *)
Program Definition Pos_Pos0_Equivalent : Cat_Equivalent Pos Pos0 :=
  {| ce_to := Pos_to_Pos0;
     ce_from := Pos0_to_Pos;
     ce_d_isom :=
       {| to := Pos_Pos0_Equiv_Pos0_0;
          from := Pos_Pos0_Equiv_Pos0_1;
       |};
     ce_c_isom :=
       {| to := Pos_Pos0_Equiv_Pos_0;
          from := Pos_Pos0_Equiv_Pos_1;
       |};
  |}.
Next Obligation.
  simpl.
  unshelve eexists.
  - intros.
    reflexivity.
  - intros.
    constructor.
Defined.
Next Obligation.
  simpl.
  unshelve eexists.
  - intros. reflexivity.
  - intros. constructor.
Defined.
