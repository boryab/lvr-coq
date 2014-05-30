(** LVR Vaje *)
(** Petek, 23. maj 2014 *)
(** Dokazovanje pravilnosti urejevalnih algoritmov. *)

(** NOTE: sort je zastarel; upoabljamo Sorting. *)
(** Require Import sort. *)
Require Import Sorting.
Require Import List.
Require Import Bool.
Require Import ZArith.

Local Open Scope list_scope.

Eval compute in (razdeli (Z.leb 5) (10 :: 1 :: 1 :: 3 :: 8 :: 7 :: 5 :: nil)%Z).

Eval compute in (urejen ((1 :: 2 :: 3 :: nil)%Z)).

(** Inserts x into lst, assuming lst is sorted list *)
Fixpoint insert (x : Z) (lst : list Z) : list Z :=
  match lst with
    | nil => x :: nil
    | y :: t =>
      if Z.leb x y then x :: y :: t else y :: (insert x t)
  end.

Eval compute in (insert 3 (2 :: 1 :: 4 :: 5 :: nil)%Z).

(** Poskus definicije insertion sorta *)
Fixpoint insertion_sort (lst : list Z) :=
  match lst with
    | nil => nil
    | x :: nil => x :: nil
    | x :: t => insert x (insertion_sort t)
   end.

Eval compute in (insertion_sort (3 :: 1 :: 7 :: 9 :: 12 :: 22 :: 2 :: nil)%Z).


(** Petek, 30. maj 2014 *)

(** Trdimo, da insertion_sort deluje pravilno. *)
Lemma Insertion_sort_Sorted (lst : list Z) :
  enak (insertion_sort lst)
Proof.
  admit.
Qed.
