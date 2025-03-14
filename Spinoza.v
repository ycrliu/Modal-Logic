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



(* God is an essence *)
Parameter God : object.

(** produced_by x y w: "at world w, y produces x." **)
Parameter produced_by : object -> object -> world -> Prop.

(* create a separate notion for "self cause" *)
Parameter self_caused : object -> world -> Prop.

(* x is a substance at world w **)
Parameter Sub : object -> world -> Prop.

(* x exists at world w. *)
Parameter E : object -> world -> Prop.

(* Principle 6: A substance cannot be produced by another substance *)
Axiom principle6 :
  forall w x,
    Sub x w ->
    ~ (exists y, y <> x /\ produced_by x y w).

(* Everything is produced by something *)
Axiom everything_has_some_cause' :
  forall w x, E x w -> exists y, produced_by x y w.

(* This version does not explicitly require existence *)
Axiom everything_has_some_cause :
  forall w x, exists y, produced_by x y w.

(* define the notion of self cause *)
Axiom self_caused_def :
  forall w x, produced_by x x w -> self_caused x w.

Axiom self_caused_implies_necessary_existence :
  forall w x,
    self_caused x w ->
    forall w', R w w' -> E x w'.

(* A substance is self caused (Statement 2 in Spinoza)
  This version does not explicitly require existence *)
Lemma substance_self_caused :
  forall w x,
    Sub x w -> self_caused x w.
Proof.
  intros w x HS.
  specialize everything_has_some_cause with (w := w) (x := x) as HC.
  destruct HC as [y Hprod].
  (* show that there is no other y' (rephrase principle 6) *)
  assert (HnoOther : ~ (exists y', y' <> x /\ produced_by x y' w)).
  {
    apply principle6.
    apply HS.
  }
  (* show that the entity which caused x is x=y itself *)
  assert (H : y = x).
  {
    specialize classic with (P := (y = x)).
    intros [Heq | Hneq].
    - apply Heq.
    - exfalso.
      apply HnoOther.
      exists y.
      split.
      + apply Hneq.
      + apply Hprod.
  }
  rewrite H in Hprod.
  apply self_caused_def.
  apply Hprod. 
Qed.

Lemma substance_is_self_caused_if_it_exists :
  forall w x,
    Sub x w ->
    E x w ->
    self_caused x w.
Proof.
  intros w x HS HE.
  specialize (everything_has_some_cause') with (w := w) (x := x) as HC.
  apply HC in HE.
  destruct HE as [y Hprod].
  assert (~ (exists y', y' <> x /\ produced_by x y' w)) as HnoOther.
  {
    apply principle6.
    apply HS.
  }

  assert (H : y = x).
  {
    specialize classic with (P := (y = x)).
    intros [Heq | Hneq].
    - apply Heq.
    - exfalso.
      apply HnoOther.
      exists y.
      split.
      + apply Hneq.
      + apply Hprod.
  }
  rewrite H in Hprod.
  apply self_caused_def.
  apply Hprod.
Qed.


(*
  Prop 1p7: If anything is a substance, then its existence involves essence
*)

Lemma essence_of_substance_involves_existence :
  forall w x,
    Sub x w ->
    box (fun w' => E x w') w.
Proof.
  intros w x Hsub w' HR.
  (* x is self_caused at w (previous lemma) *)
  specialize (substance_self_caused w x Hsub) as Hself.
  (* self_caused => necessary existence *)
  apply self_caused_implies_necessary_existence with (x := x) (w := w).
  - apply Hself.
  - apply HR.
Qed.

(* This version of that lemma involves existence as a precondition *)
Lemma essence_of_substance_involves_existence' :
  forall w x,
    Sub x w ->
    E x w ->
    box (fun w' => E x w') w.
Proof.
  intros w x Hsub Hex w' HR.
  (* x is self_caused at w (previous lemma) *)
  specialize (substance_is_self_caused_if_it_exists w x Hsub Hex) as Hself.
  (* self_caused => necessary existence *)
  apply self_caused_implies_necessary_existence with (x := x) (w := w).
  - apply Hself.
  - apply HR.
Qed.
  

(* God is necessarily a substance *)
Axiom God_is_substance : forall w, Sub God w.

(*
  Axiom 7
  If a thing can be conceived as not existing,
  then its essence does not involve existence
*)
Axiom Axiom7 :
  forall x, holdsInAllWorlds (fun w =>
    (dia (fun w' => ~ E x w') w) ->
    ~ (box (fun w' => E x w') w)).


(* Assume that God does not necessarily exist for the purposes
  of reaching a contradiction (this is the result of Statements 4-6
  in Spinoza's
  reductio argument) *)
Axiom Assumption6 :
  holdsInAllWorlds (dia (fun w => ~ E God w)).


(* combine Assumption 6 with Axiom 7 *)
Lemma God_essence_does_not_involve_existence :
  holdsInAllWorlds (
    ~M (box (fun w' => E God w'))).
Proof.
  intros w.
  intros contra.
  unfold box in *.
  specialize Assumption6 as As6.
  specialize Axiom7 with (x := God) as Ax7.
  unfold holdsInAllWorlds in *.
  specialize As6 with w.
  unfold dia in As6.
  specialize Ax7 with w.
  apply Ax7 in As6.
  (* As6 and contra are direct contradictions *)
  apply As6 in contra.
  destruct contra.
Qed.


(* Combine God_is_substance with the lemma that
  essence_of_substance_involves_existence *)
Lemma God_essence_involves_existence :
  holdsInAllWorlds (
    box (fun w' => E God w')).
Proof.
  intros w.
  specialize God_is_substance as HGS.
  specialize essence_of_substance_involves_existence as HE.
  apply HE.
  apply HGS.
Qed.


(* derive a contradiction from the previous 2 lemmas *)
Theorem God_necessarily_exists : 
  holdsInAllWorlds (fun w0 => box (fun w' => E God w') w0).
Proof.
  intros w.
  specialize God_essence_does_not_involve_existence as GNE.
  specialize God_essence_involves_existence as GE.
  unfold holdsInAllWorlds in *.
  specialize GNE with w.
  specialize GE with w.
  apply GNE in GE.
  destruct GE.
Qed.

