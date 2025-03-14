From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Export Strings.String.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Program.Equality.
From Coq Require Import Init.Nat.
From Coq Require Import PeanoNat. Import Nat.
From Coq Require Import EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Program.Equality.
From Coq Require Import Setoids.Setoid.
From LF Require Import ModalLogic.


(** Leibniz Identity of Indiscernibles
    
    Given objects x and y, if
    it is the case that for every property F
    object x has F if and only if object y has F,
    then x is identical to y.
*)

(* Two objects a, b are indiscernible if in a given world,
   for any ModalProp p, p holds of a iff p holds of b *)
Definition indiscernible (a b : object) : ModalProp :=
  forallM p, p a <->M p b.

Theorem identity_of_indiscernibles :
  holdsInAllWorlds (forallM a, forallM b,
    (indiscernible a b) ->M a =M b).
Proof.
  intros w a b.
  intros Hi.
  unfold "=M".
  unfold indiscernible in Hi.
  unfold M_all in Hi.
  unfold "<->M" in Hi.
  specialize Hi with (x := (fun a => a =M b)).
  apply Hi.
  unfold "=M".
  reflexivity.
Qed.

(*
  The converse is the Indiscernibility of Identicals
  which states that, given objects x and y, if x and y
  are identical then it is the case that for every property F
  object x and y both have F.
*)
Theorem indiscernibility_of_identicals :
  holdsInAllWorlds (forallM a, forallM b,
    (a =M b) ->M (indiscernible a b)).
Proof.
  intros w a b.
  intros Heq.
  unfold indiscernible.
  unfold "=M" in Heq.
  unfold M_all.
  unfold "<->M".
  split.
  - rewrite Heq. intros H. apply H.
  - rewrite Heq. intros H. apply H.
Qed.


(* The bidirectional statement of the previous two results. *)
Theorem leibniz_law :
  holdsInAllWorlds (forallM a, forallM b,
    (a =M b) <->M (indiscernible a b)).
Proof.
  intros w a b.
  split.
  - apply indiscernibility_of_identicals.
  - apply identity_of_indiscernibles.
Qed.

