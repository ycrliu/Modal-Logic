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


(** Fitch's Paradox of Knowability *)

(*
  The system of modal logic used to prove Fitch's Paradox of Knowability uses
  K (known) and L (can be known).
  
  This is a direct extension
  from the S5 we implemented as we can encode K and L using box and dia as follows:
*)

(* p is known if p necessarily holds *)
Definition K p := box p. 

(* p is knowable if possibly, p necessarily holds (i.e. possibly, p is known) *)
Definition L p := dia (K p).

(* LHS of implication for Fitch's Paradox:
  for every proposition p, at every world w,
  p -> dia (box p) w. *)
Definition AllTruthsAreKnowable : Prop :=
  forall (p : ModalProp),
    holdsInAllWorlds (fun w => p w -> L p w).

(* RHS of implication *)
Definition AllTruthsAreKnown : Prop :=
  (forall p : ModalProp,
    holdsInAllWorlds (fun w => p w -> K p w)). 


(* We can prove a contradiction in the statement that all truths being knowable
  implies all truths are known *)
Theorem fitch :
  AllTruthsAreKnowable -> AllTruthsAreKnown.
Proof.
  intros HallKnowable p w Hpw.
  (* show a contradiction on the prop p /\ ~(box p) *)
  (* suppose ~ box p w. We define q as "p /\ ~box p". If q holds at w,
      then q must be possibly known by HallKnowable and we get dia (box q). *)
  set (q := fun w0 => p w0 /\ ~ box p w0).

  Search (_ \/ ~_).
  specialize (classic (box p w)) as PnP.
  destruct PnP.
  - apply H.
  - assert (Hqw : q w).
    {
      unfold q.
      split.
      - apply Hpw.
      - apply H.
    }
    unfold AllTruthsAreKnowable in *.
    specialize (HallKnowable q w) as Hany. (* dia (box q) *)
    assert (HDBq : dia (box q) w).
    {
      apply Hany.
      apply Hqw.
    }
    unfold dia in *.
    destruct HDBq as [w' [HRww' HBqw']].
    specialize (box_and_distributes w') as Hdistrib.
    apply Hdistrib in HBqw'.
    destruct HBqw' as [HBp' HBNB].
    specialize (box_not_p_not_p (box p)) as HNp.
    unfold holdsInAllWorlds in HNp.
    apply HNp with w' in HBNB.
    (* contradiction with box p w' *)
    apply HBNB in HBp'.
    destruct HBp'.
Qed.

