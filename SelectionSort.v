(** * Selection Sort in Rocq (Coq)
    Full implementation + correctness proof.
    Requires Coq/Rocq standard library. *)

From Stdlib Require Import List Permutation Arith Bool Recdef.
Import ListNotations.

(* ================================================================= *)
(** ** Helper: select *)

(** [select x l = (y, l')] where [y] is the minimum of [x :: l]
    and [l'] is all the remaining elements. *)
Fixpoint select (x : nat) (l : list nat) : nat * list nat :=
  match l with
  | []     => (x, [])
  | h :: t =>
      if x <=? h
      then let (j, l') := select x t in (j, h :: l')
      else let (j, l') := select h t in (j, x :: l')
  end.

(* ================================================================= *)
(** ** selsort with fuel *)

Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _,      O    => []
  | [],     _    => []
  | x :: r, S n' =>
      let (y, r') := select x r in
      y :: selsort r' n'
  end.

Definition selection_sort (l : list nat) : list nat :=
  selsort l (length l).

(* ================================================================= *)
(** ** Sortedness *)

Inductive sorted : list nat -> Prop :=
  | sorted_nil  : sorted []
  | sorted_1    : forall i, sorted [i]
  | sorted_cons : forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Hint Constructors sorted : core.

Definition is_a_sorting_algorithm (f : list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).

(* ================================================================= *)
(** ** le_all notation *)

Definition le_all x xs := Forall (fun y => x <= y) xs.
Hint Unfold le_all : core.
Infix "<=*" := le_all (at level 70, no associativity).

(* ================================================================= *)
(** ** Lemmas about select *)

Lemma select_perm : forall x l y r,
    select x l = (y, r) -> Permutation (x :: l) (y :: r).
Proof.
  intros x l.
  induction l as [| h t IH]; intros y r Hsel.
  - simpl in Hsel. injection Hsel as <- <-. apply Permutation_refl.
  - simpl in Hsel.
    destruct (x <=? h) eqn:Hle.
    + destruct (select x t) as [j l'] eqn:Esel.
      injection Hsel as <- <-.
      (* x::h::t ~ j::h::l' *)
      (* By IH: x::t ~ j::l' *)
      specialize (IH j l' Esel).
      (* Permutation (x::h::t) (j::h::l') *)
      apply perm_trans with (h :: x :: t).
      * apply perm_swap.
      * apply perm_trans with (h :: j :: l').
        -- apply perm_skip. exact IH.
        -- apply perm_swap.
    + destruct (select h t) as [j l'] eqn:Esel.
      injection Hsel as <- <-.
      (* x::h::t ~ j::x::l' *)
      specialize (IH j l' Esel).
      (* Permutation (h::t) (j::l') *)
      apply perm_trans with (h :: x :: t).
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Lemma select_rest_length : forall x l y r,
    select x l = (y, r) -> length l = length r.
Proof.
  intros x l y r Hsel.
  apply select_perm in Hsel.
  apply Permutation_length in Hsel.
  simpl in Hsel. omega.
Qed.

Lemma select_fst_leq : forall al bl x y,
    select x al = (y, bl) -> y <= x.
Proof.
  induction al as [| h t IH]; intros bl x y Hsel.
  - simpl in Hsel. injection Hsel as <- <-. le_refl.
  - simpl in Hsel.
    destruct (x <=? h) eqn:Hle.
    + destruct (select x t) as [j l'] eqn:Esel.
      injection Hsel as <- <-.
      apply IH with l'. exact Esel.
    + destruct (select h t) as [j l'] eqn:Esel.
      injection Hsel as <- <-.
      apply Nat.leb_gt in Hle.
      specialize (IH l' h j Esel).
      omega.
Qed.

Lemma select_smallest : forall al bl x y,
    select x al = (y, bl) -> y <=* bl.
Proof.
  induction al as [| h t IH]; intros bl x y Hsel.
  - simpl in Hsel. injection Hsel as <- <-.
    unfold le_all. apply Forall_nil.
  - simpl in Hsel.
    destruct (x <=? h) eqn:Hle.
    + destruct (select x t) as [j l'] eqn:Esel.
      injection Hsel as <- <-.
      apply Nat.leb_le in Hle.
      specialize (IH l' x j Esel).
      (* y <=* h::l' *)
      unfold le_all. apply Forall_cons.
      * (* j <= h *)
        apply le_trans with x.
        -- apply select_fst_leq with t l'. exact Esel.
        -- exact Hle.
      * exact IH.
    + destruct (select h t) as [j l'] eqn:Esel.
      injection Hsel as <- <-.
      apply Nat.leb_gt in Hle.
      specialize (IH l' h j Esel).
      unfold le_all. apply Forall_cons.
      * (* j <= x *)
        apply le_trans with h.
        -- apply select_fst_leq with t l'. exact Esel.
        -- omega.
      * exact IH.
Qed.

Lemma select_in : forall al bl x y,
    select x al = (y, bl) -> In y (x :: al).
Proof.
  induction al as [| h t IH]; intros bl x y Hsel.
  - simpl in Hsel. injection Hsel as <- <-. left. reflexivity.
  - simpl in Hsel.
    destruct (x <=? h) eqn:Hle.
    + destruct (select x t) as [j l'] eqn:Esel.
      injection Hsel as <- <-.
      specialize (IH l' x j Esel).
      simpl in IH. simpl.
      destruct IH as [-> | Hin].
      * left. reflexivity.
      * right. right. exact Hin.
    + destruct (select h t) as [j l'] eqn:Esel.
      injection Hsel as <- <-.
      specialize (IH l' h j Esel).
      simpl in IH. simpl.
      destruct IH as [-> | Hin].
      * right. left. reflexivity.
      * right. right. exact Hin.
Qed.

(* ================================================================= *)
(** ** le_all helper *)

Lemma le_all__le_one : forall lst y n,
    y <=* lst -> In n lst -> y <= n.
Proof.
  intros lst y n Hall Hin.
  rewrite Forall_forall in Hall.
  apply Hall. exact Hin.
Qed.

(* ================================================================= *)
(** ** Permutation correctness of selsort *)

Lemma selsort_perm : forall n l,
    length l = n -> Permutation l (selsort l n).
Proof.
  induction n as [| n' IH]; intros l Hlen.
  - destruct l; simpl in Hlen; [apply Permutation_refl | discriminate].
  - destruct l as [| x r].
    + simpl. apply Permutation_refl.
    + simpl.
      destruct (select x r) as [y r'] eqn:Esel.
      apply perm_trans with (y :: r').
      * apply select_perm. exact Esel.
      * apply perm_skip.
        apply IH.
        simpl in Hlen.
        apply select_rest_length in Esel.
        omega.
Qed.

Lemma selection_sort_perm : forall l,
    Permutation l (selection_sort l).
Proof.
  intro l. unfold selection_sort.
  apply selsort_perm. reflexivity.
Qed.

(* ================================================================= *)
(** ** Sortedness of selsort *)

Lemma cons_of_small_maintains_sort : forall bl y n,
    n = length bl ->
    y <=* bl ->
    sorted (selsort bl n) ->
    sorted (y :: selsort bl n).
Proof.
  intros bl y n Hlen Hle Hsorted.
  destruct (selsort bl n) as [| h t] eqn:E.
  - apply sorted_1.
  - apply sorted_cons.
    + apply le_all__le_one with bl.
      * exact Hle.
      * (* h is in bl, via permutation *)
        assert (Hperm : Permutation bl (selsort bl n)).
        { apply selsort_perm. exact Hlen. }
        rewrite E in Hperm.
        apply Permutation_in with (h :: t).
        -- apply Permutation_sym. exact Hperm.
        -- left. reflexivity.
    + exact Hsorted.
Qed.

Lemma selsort_sorted : forall n al,
    length al = n -> sorted (selsort al n).
Proof.
  induction n as [| n' IH]; intros al Hlen.
  - destruct al; simpl in Hlen; [apply sorted_nil | discriminate].
  - destruct al as [| x r].
    + apply sorted_nil.
    + simpl.
      destruct (select x r) as [y r'] eqn:Esel.
      apply cons_of_small_maintains_sort.
      * apply select_rest_length in Esel. simpl in Hlen. omega.
      * apply select_smallest with x r. exact Esel.
      * apply IH. apply select_rest_length in Esel. simpl in Hlen. omega.
Qed.

Lemma selection_sort_sorted : forall al,
    sorted (selection_sort al).
Proof.
  intro al. unfold selection_sort.
  apply selsort_sorted. reflexivity.
Qed.

Theorem selection_sort_is_correct :
    is_a_sorting_algorithm selection_sort.
Proof.
  unfold is_a_sorting_algorithm. intro al.
  split.
  - apply selection_sort_perm.
  - apply selection_sort_sorted.
Qed.

(* ================================================================= *)
(** ** selsort' using Function + measure (no fuel) *)

Function selsort' l {measure length l} :=
  match l with
  | []     => []
  | x :: r =>
      let (y, r') := select x r in
      y :: selsort' r'
  end.
Proof.
  intros l x r _ y r' Esel.
  simpl. apply select_rest_length in Esel. omega.
Defined.

Example selsort'_example :
    selsort' [3;1;4;1;5;9;2;6;5] = [1;1;2;3;4;5;5;6;9].
Proof. reflexivity. Qed.

Lemma selsort'_perm : forall n l,
    length l = n -> Permutation l (selsort' l).
Proof.
  induction n as [| n' IH]; intros l Hlen.
  - destruct l; simpl in Hlen; [apply Permutation_refl | discriminate].
  - destruct l as [| x r].
    + simpl. apply Permutation_refl.
    + rewrite selsort'_equation.
      destruct (select x r) as [y r'] eqn:Esel.
      apply perm_trans with (y :: r').
      * apply select_perm. exact Esel.
      * apply perm_skip.
        apply IH.
        apply select_rest_length in Esel.
        simpl in Hlen. omega.
Qed.

Lemma cons_of_small_maintains_sort' : forall bl y,
    y <=* bl ->
    sorted (selsort' bl) ->
    sorted (y :: selsort' bl).
Proof.
  intros bl y Hle Hsorted.
  destruct (selsort' bl) as [| h t] eqn:E.
  - apply sorted_1.
  - apply sorted_cons.
    + apply le_all__le_one with bl.
      * exact Hle.
      * assert (Hperm : Permutation bl (selsort' bl)).
        { apply selsort'_perm with (length bl). reflexivity. }
        rewrite E in Hperm.
        apply Permutation_in with (h :: t).
        -- apply Permutation_sym. exact Hperm.
        -- left. reflexivity.
    + exact Hsorted.
Qed.

Lemma selsort'_sorted : forall n al,
    length al = n -> sorted (selsort' al).
Proof.
  induction n as [| n' IH]; intros al Hlen.
  - destruct al; simpl in Hlen.
    + rewrite selsort'_equation. apply sorted_nil.
    + discriminate.
  - destruct al as [| x r].
    + rewrite selsort'_equation. apply sorted_nil.
    + rewrite selsort'_equation.
      destruct (select x r) as [y r'] eqn:Esel.
      apply cons_of_small_maintains_sort'.
      * apply select_smallest with x r. exact Esel.
      * apply IH. apply select_rest_length in Esel. simpl in Hlen. omega.
Qed.

Theorem selsort'_is_correct :
    is_a_sorting_algorithm selsort'.
Proof.
  unfold is_a_sorting_algorithm. intro al.
  split.
  - apply selsort'_perm with (length al). reflexivity.
  - apply selsort'_sorted with (length al). reflexivity.
Qed.
