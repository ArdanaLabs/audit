(*Constraint emitter machines*)


Require Import List.
Require Import Ensembles.
Require Import Reals.
Require Import Relations.
Require Import RelationClasses.
Require Import Lia.
Require Import String.

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
      id : TxId;
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
      (*For interval, lol i'm not using my record. This amounts to a "Ensemble nat"*)
      tx_validityInterval : Tick -> Prop
    }.

(*Not invertible but it'll typecheck.*)
Definition txId (tx : Tx) : TxId
  :=
    let inputs' := inputs tx in
    let outrefs' := map outputRef inputs' in
    let outrefs_prod := map (fun x => id x * index x) outrefs' in
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
  id outref = txId tx /\ index outref = 1. (*Should be a foldWithOr somehow
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
  match lookupTx l (id (outputRef i)) with
  | None => None
  | Some tx =>
    let idx := index (outputRef i) in
    let outputs' := outputs tx in
    nth_error outputs' idx
  end.

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

(* Constraint Emitting Machines *)
Variable S : Type.
Variable I : Type.
(* https://github.com/omelkonian/formal-utxo/blob/a1574e685d5eef7bfa46ec14c877a20e00b0b8e5/StateMachine/Base.agda *)
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






(*Lens plagiarize https://github.com/bedrocksystems/coq-lens/blob/master/theories/Lens.v*)
(* The theory is that will help me work with Tx objects. *)
Set Primitive Projections.

Record Lens (a b c d : Type) : Type :=
  mkLens {
  view : a -> c;
  over : (c -> d) -> a -> b
  }.

Arguments over {_ _ _ _} _ _ _.
Arguments view {_ _ _ _} _ _.

Definition lens_compose {a b c d e f : Type}
           (l1 : Lens a b c d) (l2 : Lens c d e f)
  : Lens a b e f :=
  {| view := fun (x : a) => view l2 (view l1 x);
     over := fun (f0 : e -> f) => over l1 (over l2 f0)
  |}.


Section ops.
  Context {a b c d : Type} (l : Lens a b c d).

  Definition set (new : d) : a -> b :=
    over l (fun _ => new).
End ops.

Module LensNotations.
  Declare Scope lens_scope.
  Delimit Scope lens_scope with lens.
  Bind Scope lens_scope with Lens.

  Notation "X -l> Y" := (Lens X X Y Y)
    (at level 99, Y at level 200, right associativity) : type_scope.
  Notation "a & b" := (b a) (at level 50, only parsing, left associativity) : lens_scope.
  Notation "a %= f" := (over a f) (at level 49, left associativity) : lens_scope.
  Notation "a .= b" := (set a b) (at level 49, left associativity) : lens_scope.
  Notation "a .^ f" := (view f a) (at level 45, left associativity) : lens_scope.
  (* level 19 to be compatible with Iris .@ *)
  Notation "a .@ b" := (lens_compose a b) (at level 19, left associativity) : lens_scope.
End LensNotations.

Import LensNotations.

Variable tx1 tx2 : Tx.

Variable ltxi : Tx -l> Input.
Variable ltxo : Tx -l> Output.
Variable inp : Input.
Check (ltxi .= inp)%lens.


(* Quickchick *)
From QuickChick Require Import QuickChick.

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h::t => if h =? x then t else h :: remove x t
  end.

Conjecture removeP : forall x l, not (List.In x (remove x l)).

QuickChick removeP.
