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


(** Moore's Paradox

  Moore's Paradox applies statements such as
    p /\ "I believe ~p"
  
  This is satisfiable in S5 modal logic, which we will
  formalize below. To do so, we need to also formalize
  what it means to believe a proposition.
*)

(*
  We will show that Moore's Paradox holds in some world.
  However, we need a concrete model with a certain number of worlds
  to do this. We will make worlds coincide with the natural numbers
  giving us an infinite number of worlds.

  Since we redefined worlds, we also need to redefine the other
  machinery which is built on worlds.
*)
Definition world := nat.
Definition ModalProp := world -> Prop.
Definition holdsInAllWorlds (p : ModalProp) : Prop :=
  forall w, p w.

(* New equivalence relation on worlds for belief + the
   axioms that make RB an equivalence relation. All worlds
   are accessible from one another. *)
Definition RB (u v : world) : Prop := True.

(* Belief operator *)
Definition Bel (p : ModalProp) (w : world) : Prop :=
   forall w', RB w w' -> p w'.

Definition moore_paradox (p : ModalProp) :=
  fun w => p w /\ ~ (Bel p w).

Definition p : ModalProp := fun w => w = 0.

(* Define a prop that holds in one world, namely 0 *)
Lemma moore_paradox_holds :
  moore_paradox p 0.
Proof.
  unfold moore_paradox.
  split.
  - reflexivity.
  - unfold Bel.
    intros contra.
    specialize contra with (w' := 1).
    unfold p in contra.
    discriminate contra.
    unfold RB.
    apply I.
Qed.
 


