Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Require Import Arith TwistedFunctor Maps.

Import ListNotations.
Import C.Notations.

(** The classic Hello World program. *)
Definition hello_world (argv : list LString.t) : C.t System.effect unit :=
  System.log (LString.s "Hello world!").


(*We will use Id defined in Maps as Ptr.*)

Inductive Pointer (name : id) (points_to : nat) (buf_len : nat) (skip_len : nat): Type :=
| ptr : Pointer name points_to buf_len skip_len.

Fixpoint alloc (loc : nat) () (ptr : Pointer name points_to buf_len skip_len) : nat -> nat ->  -> PointsTo 

Definition PointsTo (p : Pointer _ _ _ _) (loc : nat) : Prop :=
  match p with
  | ptr _ l _ _ => eq_nat l loc
  end.

Check ptr (Id 2) 32 50.


Definition beq_ptr id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.


