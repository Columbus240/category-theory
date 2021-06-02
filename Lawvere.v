(* Lawvere Theories *)

(* To define Lawvere Theories we need a skeleton of the category of finite sets. *)
Set Universe Polymorphism.

Require Import Theory.Category.
Require Import Theory.Isomorphism.

Definition skeletal (C : Category) : Prop :=
  forall x y : C, x ≅ y -> x = y.

Require Import Construction.Subcategory.

Require Import Theory.Functor.
Require Import Lib.Setoid.
Require Import Lib.Foundation.

Require Import Instance.Cat.

(* A subcategory [D] of a category [C] is a skeleton of [C],
   if [D] (as category) is skeletal and the inclusion-functor from [D]
   to [C] is part of an equivalence.
 *)
Definition skeleton (C : Cat) (D : Subcategory C) :=
  skeletal (Sub C D) /\
  (exists iso : (Sub C D) ≅ C, to iso = (Incl C D)).

Require Import Instance.Sets.

Fixpoint Fin (n : nat) : Set :=
  match n with
  | O => Empty_set
  | S n' => option (Fin n')
  end.

(* From CPDT by Adam Chlipala *)
Ltac dep_destruct E :=
  let x := fresh "x" in
  remember E as x; simpl in x; dependent destruction x;
  try match goal with
      | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
      end.

Theorem Fin_bij_impl_eq (n m : nat) (f : Fin n -> Fin m) (g : Fin m -> Fin n) :
  (forall x, f (g x) = x) -> (forall x, g (f x) = x) -> n = m.
Proof.
  generalize dependent m.
  induction n; intros.
  { destruct m; [reflexivity|].
    destruct (g None).
  }
  destruct m.
  { destruct (f None). }
  specialize (IHn m).
  unshelve erewrite IHn; try reflexivity.
  - (* define [f0] *)
    intros.
    destruct (f (Some H1)) eqn:E0; [assumption|].
    destruct (f None) eqn:E1; [assumption|].
    pose proof (H0 None).
    rewrite E1 in H2.
    rewrite <- E0 in H2.
    rewrite H0 in H2.
    discriminate H2.
  - (* define [g0] *)
    intros.
    destruct (g (Some H1)) eqn:E0; [assumption|].
    destruct (g None) eqn:E1; [assumption|].
    pose proof (H None).
    rewrite E1 in H2.
    rewrite <- E0 in H2.
    rewrite H in H2.
    discriminate H2.
  - intros.
    simpl.
    remember (f (Some (match g (Some x) with _ => _ end))) as Q.
    induction n.
    + simpl.
      assert (g (Some x) = None).
      { destruct (g (Some x)) eqn:E.
        - destruct f0.
        - reflexivity.
      }
    destruct (_) eqn:E.
    + 
    remember (Some (match g (Some x) with _ => _ end)) as q.
    assert ({ p | g (Some x) = Some p } + {g (Some x) = None}).
    { admit. }
    destruct H1.
    + destruct s.
    remember (g (Some x)) as q.
    destruct (g (Some x)).
    induction m.
    + simpl.

Program Definition Fin_setoid (n : nat) : SetoidObject :=
  {| carrier := Fin.t n;
     is_setoid :=
       {| equiv := eq;
       |};
  |}.

Definition Fin_cat : Subcategory Sets := @Build_FullSubcategory Sets (fun A => { n : nat & A = Fin_setoid n }).

Lemma Fin_cat_skeletal : skeletal (Sub _ Fin_cat).
Proof.
  red.
  simpl in *.
  intros.
  destruct x, y.
  destruct s, s0.
  subst.
  destruct H.
  simpl in *.
  destruct to, from.
  simpl in *.
  destruct x, x0.
  simpl in *.
  clear u u0.
  destruct (Fin_bij_eq _ _ morphism morphism0); try assumption.
  reflexivity.
Defined.

Require Import Coq.Vectors.Vector.

Definition nat_funct_comp {x y z : nat} (f : Vector.t (Fin.t y) z) (g : Vector.t (Fin.t x) y) : Vector.t (Fin.t x) z.
Proof.
  induction f.
  { constructor. }
  apply cons.
  2: { apply IHf. }
  apply (nth g h).
Defined.

Definition fin_set_id (x : nat) : Vector.t (Fin.t x) x.
Proof.
  - induction x.
    + constructor.
    + constructor.
      * apply Fin.F1.
      * refine (map _ IHx); clear IHx.
        apply Fin.FS.
Defined.

(* The category of finite sets. *)
Program Definition FinSets : Category :=
  {|
  obj := nat;
  hom n m := Vector.t (Fin.t n) m;
  homset n m :=
    {| equiv := eq |};
  compose x y z f g := nat_funct_comp f g;
  id x := fin_set_id x;
  |}.
Proof.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

Lemma FinSets_skeletal : skeletal FinSets.
Proof.
  red.
  intros.
  destruct H.
  red in to.
  red in from.
  red in iso_from_to.
  red in iso_to_from.
