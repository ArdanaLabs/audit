From Coq Require Import
     List
     Reals
     Ensembles.

From EUTXO Require Import
     Structures
     Types.

(*Figure 6.*)
Definition value_preserved__suminputs (tx : Tx) (l : Ledger) : option Quantity :=
  let inputs' := inputs tx in
  let spentOutputs := map (Basics.flip getSpentOutput l) inputs' in
  let spentValues := map (fmap_option value) spentOutputs in
  foldright_option Rplus 0%R spentValues.

Definition value_preserved__sumoutputs (tx : Tx) (l : Ledger) : option Quantity :=
  match l with
  | nil => None
  | (tx' :: l') =>
    let outputs' := outputs tx in
    let outputsValues := map value outputs' in
    let totalValue := fold_right Rplus 0%R outputsValues in
    Some totalValue
  end.

Definition value_preserved (tx : Tx) (l : Ledger) : Prop :=
  value_preserved__suminputs tx l = value_preserved__sumoutputs tx l.

(*  *)
Definition no_double_spent (tx : Tx) : Prop :=
  let inputs' := inputs tx in
  let inputs_product := cartesian_product inputs' inputs' in
  let thepredicate := fun t => outputRef (fst t) = outputRef (snd t) -> fst t = snd t in
  Forall thepredicate inputs_product.

(* WARNING: currently returns True for None = None *)
Definition validator_scripts_match_output_addresses (tx : Tx) (l : Ledger) : Prop :=
  let thepredicate_lhs := fun inp => scriptAddr (validator inp) in
  let thepredicate_rhs := fun inp => match getSpentOutput inp l with
                                  | None => None
                                  | Some outp => Some (addr outp)
                                  end in
  let thepredicate := fun inp => thepredicate_lhs inp = thepredicate_rhs inp in
  Forall thepredicate (inputs tx).

Variable h : Datahash Quantity.
Variable x' : Quantity.
Check h x'.

Definition datum_match_output_hash (tx : Tx) (l : Ledger) : Prop :=
  let thepredicate_lhs := fun inp => Some (datahash (datum inp)) in
  let thepredicate_rhs := fun inp => match getSpentOutput inp l with
                                  | None => None
                                  | Some outp => Some (datumHash outp)
                                  end in
  let thepredicate := fun inp => thepredicate_lhs inp = thepredicate_rhs inp in
  Forall thepredicate (inputs tx).

Check Included.
Definition EUTXOValid : Type := Tick -> Tx -> Ledger -> Prop.
Definition EUTXO_valid (currentTick : Tick) (tx : Tx) (l : Ledger) :=
  (*The current tick is within the validity interval*)
  (tx_validityInterval tx) currentTick /\
  (* All outputs have nonnegative values *)
  fold_right and True (map (fun out => (value out >= 0)%R) (outputs tx)) /\ (*This one is redundant because of my type constraint value : Quantity = nonegreal !NVMNVM: I actually removed that constraint because I didn't want to push the proof around.*)
  (* All inputs refer to unspent outputs *)
  (Included OutputRef (fun outref => List.In outref (map outputRef (inputs tx))) (unspentOutputs l)) /\
  (* Value is preserved *)
  value_preserved tx l /\
  (* No output is double spent *)
  no_double_spent tx /\
  (* All inputs validate*)
  True (* TODO *) /\
  (* Validator scripts match output addresses *)
  validator_scripts_match_output_addresses tx l /\
  (* Each datum matches its output hash *)
  datum_match_output_hash tx l
.
