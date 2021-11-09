From Coq Require Import
     String
     Reals
     List
     Ensembles
.

(*Scripting language*)
Inductive script_aexp : Type :=
| Script_ANum (n : nat)
| Script_AId (x : string)
| Script_APlus (a1 a2 : script_aexp).

Fixpoint script_aeval (st : string -> nat) (a : script_aexp) : nat :=
  match a with
  | Script_ANum n => n
  | Script_AId x => st x
  | Script_APlus a1 a2 => (script_aeval st a1) + (script_aeval st a2)
  end.

Inductive script : Type :=
| ScrSkip
| ScrAss (x : string) (a : script_aexp)
| ScrSeq (s1 s2 : script).

Coercion Script_ANum : nat >-> script_aexp.
Coercion Script_AId : string >-> script_aexp.


(*base types*)
Definition Quantity := R. (* don't want to push around the proof obligation for the nonnegreal type.*)
Definition Tick := nat.
Definition Address := nat.
Definition Data := Type.
Definition data := Quantity.
Definition Datahash (data : Data) := data -> nat.
(* WARNING: datahash is set to constant*)
Definition datahash : Datahash Quantity :=
  fun x => 1.
Definition HashValue := nat.

Definition TxId := nat.

Definition Script := script.
Definition ScriptAddr := Script -> option Address.
(* WARNING: scriptAddr set to constant*)
Definition scriptAddr (s : Script) : option Address := Some 1.

(*derived types*)
Record Output : Type :=
  mkOutput
    {
      value : Quantity;
      addr : Address;
      datumHash : HashValue
    }.

Record OutputRef : Type :=
  mkOutputRef
    {
      txid : TxId;
      index : nat
    }.

Record Input : Type :=
  mkInput
    {
      outputRef : OutputRef;
      validator : Script;
      datum : data;
      redeemer : data
    }.

Definition mkValidityInterval (lft rgt : nat) (x : nat) : Prop := lft <= x /\ rgt <= x.
Record Tx : Type :=
  mkTx
    {
      inputs : list Input; (*This is Set in paper but I think this will be more convenient than "Ensemble Input"*)
      outputs : list Output;
      tx_validityInterval : Tick -> Prop
    }.

(*Not invertible but it'll typecheck.*)
Definition txId (tx : Tx) : TxId
  :=
    let inputs' := inputs tx in
    let outrefs' := map outputRef inputs' in
    let outrefs_prod := map (fun x => txid x * index x) outrefs' in
    fold_right (fun n m => n + m) 0 outrefs_prod.

Definition Ledger : Type := list Tx.

Record OutputInfo : Type :=
  mkOutputInfo
    {
      oi_value : Quantity;
      oi_validatorHash : Address;
      oi_datumHash : Datahash Quantity
    }.

Record InputInfo : Type :=
  mkInputInfo
    {
      ii_outputRef : OutputRef;
      ii_validatorHash : Address;
      ii_datum : data;
      ii_redeemer : data;
      ii_value : Quantity
    }.

(**The Context type is a summary of the information contained in the Tx type in Figure 3,
situated in the context of a validating transaction, and made suitable for consumption in a script.
 *)
Record Context' : Type :=
  mkContext'
    {
      inputInfo : list InputInfo; (*paper is Set, but we think this will be better than Ensemble InputInfo*)
      outputInfo : list OutputInfo;
      ctxt_lft : Tick;
      ctxt_rgt : Tick;
      ctxt_validityInterval : Tick -> Prop; (*forall x, ctxt_lft <= x /\ x <= ctxt_rgt;*)
      thisInput : nat
    }.

(*Figure 5.*)
Definition LookupTx : Type := Ledger -> TxId -> option Tx.
Fixpoint lookupTx (l : Ledger) (txid : TxId) : option Tx :=
  match l with
  | nil => None
  | (tx :: l) =>
    let txid := txId tx in
    if txid =? (txId tx) then Some tx else lookupTx l txid
  end.

Definition UnspentTxOutputs : Type := Tx -> Ensemble OutputRef.
Definition unspentTxOutputs (tx : Tx) (outref : OutputRef) : Prop :=
  txid outref = txId tx /\ index outref = 1. (*Should be a foldWithOr somehow
                                           but I don't understand what `id` means in the paper here.*)

Definition UnspentOutputs : Type := Ledger -> Ensemble OutputRef.
Fixpoint unspentOutputs (l : Ledger) (outref : OutputRef) : Prop :=
  match l with
  | nil => False
  | (tx :: l) =>
    let outrefs' := map (fun tx => map outputRef (inputs tx)) l in
    let complementTerm := List.In outref (List.concat outrefs') in
    (In _ (unspentOutputs l) outref /\ not complementTerm) \/ unspentTxOutputs tx outref
  end.

Definition GetSpentOutput : Type := Input -> Ledger -> option Output.
Definition getSpentOutput (i : Input) (l : Ledger) : option Output :=
  match lookupTx l (txid (outputRef i)) with
  | None => None
  | Some tx =>
    let idx := index (outputRef i) in
    let outputs' := outputs tx in
    nth_error outputs' idx
  end.
