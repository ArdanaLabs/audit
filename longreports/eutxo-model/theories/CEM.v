(*Constraint emitter machines

 There may be some ideas in the agda version https://github.com/omelkonian/formal-utxo/blob/a1574e685d5eef7bfa46ec14c877a20e00b0b8e5/StateMachine/Base.agda
 but we're trying to do something different, with itrees. *)

From ITree Require Import
     ITree.

From EUTXO Require Import
     (*Structures*)
     Lens
     Types
     Valid.

Import ITreeNotations.
Import LensNotations.

Inductive IO : Type -> Type :=
| Read (A : Type) : IO A
| Write (A : Type) : A -> IO unit.

Definition read : itree IO Tx := embed (@Read Tx).
Definition write : Tx -> itree IO unit := embed (@Write Tx).


Check IO Tx.
Check itree IO Tx.
Check embed (@Read Tx).

Definition example : itree IO unit :=
  n <- read;;
  write n.

Compute observe example.
Check embed.
(*
From Coq Require Import Arith.
Parameter tx : Tx.
Check id.

Definition test_interp : itree IO unit -> bool := fun t =>
  match observe t with
  | VisF e k =>
    match e in IO X return (X -> _) -> _ with
    | (Read nat) => fun id =>
      match observe (k (id SOME_NUMBER)) with
      | VisF (Write Tx n) _ => n =? SOME_NUMBER
      | _ => false
      end
    | _ => fun _ => false
    end (fun x => x)
  | _ => false
  end.
Check id.
Example test : test_interp example = true := eq_refl.
*)


Section TakingIdeasFromAgdaCodebase.
  Variable S : Type.
  Variable I : Type.
  Record TxConstraints : Type :=
    mkTxConstraints
      {
        forge : option Quantity; (* value in agda codebase *)
        lft : Tick;
        rgt : Tick
      }.

  Definition TxConstraints' : Type := Tx -> Prop.
  Variable final : S -> bool.
  Variable step : S -> I -> option (S * TxConstraints').
End TakingIdeasFromAgdaCodebase.

