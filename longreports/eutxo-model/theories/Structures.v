From Coq Require Import
     List
     Relations
     Lia.
Import ListNotations.

(* Most of this should be refactored to use `coq-ext-lib`*)

(* option functor, applicative, monad, foldable, traversable utils *)
Definition fmap_option {A B : Type} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some x' => Some (f x')
  end.

Definition return_option {A : Type} := Some A.

Definition applic_option {A B : Type} (f : option (A -> B)) (x : option A) : option B
  :=
    match f with
    | None => None
    | Some f' => fmap_option f' x
    end.
Notation "f <*> x" := (applic_option f x) (at level 41, left associativity).

Definition bind_option {A B : Type} (x : option A) (fm : A -> option B) : option B :=
  match x with
  | None => None
  | Some x' => fm x'
  end.
Notation "A >>= F" := (bind_option A F) (at level 42, left associativity).

(* Defined to None out if any item of xs is None *)
Fixpoint foldright_option {A B : Type}
           (f : B -> A -> A) (z : A) (xs : list (option B))
  : option A :=
  match xs with
  | nil => Some z
  | (x :: xs') => fmap_option f x <*> foldright_option f z xs'
  end.

(* Defined such that sequenceA_list_option nil = None instead of Some nil *)
Fixpoint sequenceA_list_option {A : Type} (xs : list (option A)) : option (list A) :=
  match xs with
  | nil => None
  | (x::xs) =>
    match x with
    | None => None
    | Some x' => fmap_option (cons x') (sequenceA_list_option xs)
    end
  end.

Definition traverse_list_option {A B : Type} (f : A -> option B) (xs : list A) : option (list B) :=
  sequenceA_list_option (map f xs).

Definition singleton {A : Type} (x : A) := @cons A x nil.

Definition option_app {A : Type} (xs ys : option (list A)) : option (list A) :=
  match xs with
  | None => None
  | Some xs' => fmap_option (@app A xs') ys
  end.

Fixpoint applic_list' {A B : Type} (fs : list (A -> B)) (xs : list A) : option (list B) :=
  match fs in list _ return list A -> option (list B) with
  | nil => fun xs' => Some nil
  | (f::fs') => fun xs' => option_app (Some (map f xs')) (applic_list' fs' xs')
  end xs.

Fixpoint applic_list {A B : Type} (fs : list (A -> B)) (xs : list A) : list B :=
  match fs in list _ return list A -> list B with
  | nil => fun _ => nil
  | (f::fs') => fun xs' => (map f xs') ++ (applic_list fs' xs')
  end xs.

Notation "fs <*> xs" := (applic_list fs xs) (at level 41, left associativity) : list_scope.

Definition cartesian_product {A B : Type} (xs : list A) (ys : list B) : list (A * B) :=
  map pair xs <*> ys.



(*Total order for intervals*)
Class TotalOrder {A : Type} (Rel : relation A) : Type :=
  {
  to__refl : forall (x : A), Rel x x;
  to__transitive : forall (x y z : A), Rel x y -> Rel y z -> Rel x z;
  to__antisymmetric : forall (x y : A), Rel x y -> Rel y x -> x = y;
  to__stronglyconnected : forall (x y : A), Rel x y \/ Rel y x
  }.

Lemma le__refl : forall (x : nat), x <= x.
Proof. lia. Qed.
Lemma le__transitive : forall (x y z : nat), x <= y -> y <= z -> x <= z.
Proof. lia. Qed.
Lemma le__antisymmetric : forall (x y : nat), x <= y -> y <= x -> x = y.
Proof. lia. Qed.
Lemma le__stronglyconnected : forall (x y : nat), x <= y \/ y <= x.
Proof. lia. Qed.

Instance leTO__nat : TotalOrder le :=
  {
  to__refl := le__refl;
  to__transitive := le__transitive;
  to__antisymmetric := le__antisymmetric;
  to__stronglyconnected := le__stronglyconnected
  }.

Record Interval {A : Type} {Rel : relation A}
       (toA : TotalOrder Rel)
       (a b : A) : Type := mkInterval
  {
    x : A;
    inInterval : Rel a x /\ Rel x b
  }.


Definition mkNatInterval (lft rgt : nat) (x : nat) (H : lft <= x /\ x <= rgt) : Interval leTO__nat lft rgt :=
  mkInterval nat le leTO__nat lft rgt x H.
