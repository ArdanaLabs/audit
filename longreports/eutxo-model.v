Require Import List.
Require Import Ensembles.
Require Import Reals.
Require Import Relations.
Require Import RelationClasses.
Require Import Lia.

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


Definition Quantity := posreal.
Definition Tick := nat.
Definition Address := nat.
Definition Data := Type.
Definition Datahash (data : Data) := data -> nat.

Definition TxId := nat.
Definition txId {A B : Type} := (A -> B) -> TxId.
Definition scriptAddr :
Record InputInfo
Definition scriptAddr :

Record Output : Type :=
  mkOutput
    {
      value : Quantity;
      addr : Address;
      datumHash : Datahash
    }.


Record Input : Type :=
  mkInput
    {
      outputRef : OutputRef;
      validator : Script;
      datum : Data;
      redeemer : Data
    }.
