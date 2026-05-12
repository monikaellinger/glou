Require Import List Arith.
Import ListNotations.

(* Find the minimum of two naturals *)
Definition min_nat (a b : nat) : nat :=
  if a <=? b then a else b.

(* Find the minimum element of a non-empty list *)
Fixpoint list_min (l : list nat) (default : nat) : nat :=
  match l with
  | []     => default
  | x :: rest => min_nat x (list_min rest x)
  end.

(* Remove the first occurrence of a value from a list *)
Fixpoint remove_first (n : nat) (l : list nat) : list nat :=
  match l with
  | []     => []
  | x :: rest =>
      if x =? n then rest
      else x :: remove_first n rest
  end.

(* Selection sort: repeatedly extract the minimum *)
Fixpoint selection_sort (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O    => l   (* out of fuel (won't happen if fuel = length l) *)
  | S f  =>
      match l with
      | []     => []
      | x :: _ =>
          let m := list_min l x in
          m :: selection_sort f (remove_first m l)
      end
  end.

(* Convenience wrapper: fuel = length of list *)
Definition sort (l : list nat) : list nat :=
  selection_sort (length l) l.

(* ── Examples ── *)

Compute sort [3; 1; 4; 1; 5; 9; 2; 6].
(* Expected: [1; 1; 2; 3; 4; 5; 6; 9] *)

Compute sort [].
(* Expected: [] *)

Compute sort [42; 7; 3].
(* Expected: [3; 7; 42] *)
