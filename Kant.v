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


(** Kant *)

(* We can extend the S5 implemented so far, with new relations, into
  DDL, which gives additional machinery like obligation for Kantian ethics *)

Parameter agent : Type.

(* Encodes: agent does a certain action in a given world. *)
Parameter does : agent -> object -> world -> Prop.

Definition DoesMP (a : agent) (action : object) : ModalProp :=
  fun w => does a action w.

(* an action is universalized when in every world, everyone does it *)
Definition universalizes (act : object) : ModalProp :=
  fun w => forall (a : agent), does a act w.

Definition noContradiction (p : ModalProp) : ModalProp :=
  fun w => ~(p w -> False).

(* according to the Categorical Imperative, an action is morally permissible
  if there exists a world such that
  the action can be universalized and there is no contradiction *)
Definition MorallyPermissible (act : object) : ModalProp :=
  fun w =>
    (dia (fun w' => universalizes act w' /\ noContradiction (universalizes act) w')) w.

Parameter R_deontic : world -> world -> Prop.

(** obligation p means: in all R_deontic-accessible worlds, p holds. *)
Definition O (p : ModalProp) : ModalProp :=
  fun w => forall w', R_deontic w w' -> p w'.

Axiom R_deontic_serial : forall w, exists w', R_deontic w w'.

Definition Perm (p : ModalProp) : ModalProp :=
  fun w => ~ (O (~M p) w).


Definition Forbid (p : ModalProp) : ModalProp :=
  fun w => O (~M p) w.


Lemma K_schema_deontic :
  holdsInAllWorlds (forallM p, forallM q,
    (O (p ->M q)) ->M (O p ->M O q)).
Proof.
  intros w.
  intros p q HO.
  unfold O in *.
  intros HOp.
  intros w' HRww'.
  specialize HO with w'.
  specialize HOp with w'.
  apply HO.
  - apply HRww'.
  - apply HOp.
    apply HRww'.
Qed.

Lemma O_nec :
  forall (p : ModalProp),
    (forall w, p w) -> (forall w, O p w).
Proof.
  intros p H w.
  unfold O.
  intros w' HR_deo.
  apply H.
Qed.

Definition possible_deontic (p : ModalProp) : ModalProp :=
  fun w => exists w', R_deontic w w' /\ p w'.

Lemma ought_implies_can :
  holdsInAllWorlds (
    forallM p, O p ->M possible_deontic p).
Proof.
  intros w p.
  intros HOp.
  unfold possible_deontic in *.
  destruct (R_deontic_serial w) as [w' HRww'].
  exists w'.
  split.
  - apply HRww'.
  - apply HOp.
    apply HRww'.
Qed.


(* Since we have both box and O, we can create statements that combine
  metaphysical necessity (box) and deontic necessity (O) *)
Definition meta_nec_deontic_obl (p : ModalProp) : ModalProp :=
  box (O p).
Definition deon_obl_meta_nec (p : ModalProp) : ModalProp :=
  O (box p).


(** Formalizing that universalizing stealing leads to a
  contradiction which
  therefore means stealing is not morally permissible
  under the categorical imperative *)

Parameter property : object.

(* "owns a o w" means agent a owns object o in world w. *)
Parameter owns : agent -> object -> world -> Prop.

(* we assume that ownership is unique *)
Axiom unique_ownership :
  forall (w : world),
    exists (owner : agent),
      owns owner property w /\
      forall (anyone : agent),
        owns anyone property w -> anyone = owner.

Parameter StealAct : object.

(* "does a StealAct w" iff a is stealing the property in w *)
Definition steals (a : agent) (w : world) : Prop :=
  exists b : agent,
    b <> a /\ owns b property w.  (* a is taking property from b, who owns it *)

Axiom does_steal_equiv :
  forall (w : world) (a : agent),
    does a StealAct w <-> steals a w.

(* universalizing stealing yields a contradiction. *)
Lemma universal_stealing_contradiction :
  forall (w : world),
    (forall a : agent, does a StealAct w) ->
    False.
Proof.
  intros w H. 
  specialize unique_ownership with w as Huow.
  destruct Huow as [owner [Howns Hunique]].
  specialize (H owner).
  rewrite does_steal_equiv in H.
  destruct H as [b [Hneq HownsB]].
  specialize (Hunique b HownsB).
  apply Hneq in Hunique.
  destruct Hunique.
Qed.


Lemma universal_stealing_not_coherent :
  forall (w : world),
    ~ noContradiction (universalizes StealAct) w.
Proof.
  intros w contra.
  unfold noContradiction in contra.
  apply contra.
  intros Hforall.
  apply universal_stealing_contradiction in Hforall.
  destruct Hforall.
Qed.

(* We can prove in all worlds that stealing is not morally permissible *)
Lemma stealing_not_permissible :
  holdsInAllWorlds (
    fun w => ~ MorallyPermissible StealAct w).
Proof.
  intros w Hperm.
  unfold MorallyPermissible in Hperm.
  destruct Hperm as [w' [HR [Huniv Hnocontr]]].
  unfold noContradiction in Hnocontr.
  unfold universalizes in Huniv.
  apply Hnocontr.
  intros HforallStealAct.
  apply universal_stealing_contradiction in HforallStealAct.
  destruct HforallStealAct.
Qed.






  