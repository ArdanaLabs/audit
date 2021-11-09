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

Definition lens {a b c d : Type} (ac : a -> c) (adb : a -> d -> b) : Lens a b c d :=
  {| view := ac; over := fun (f : c -> d) (x : a) => adb x (f (ac x)) |}.

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

