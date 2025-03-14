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
From Coq Require Import Logic.Classical_Pred_Type.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Program.Equality.

(** Basics *)

(* Worlds and objects in a model *)
Parameter world : Type.
Parameter object : Type.

(* Modal proposition that depends on a world *)
Definition ModalProp := world -> Prop.

Definition M_eq (a b : object) (w : world) := a = b.
Definition M_not (p : ModalProp) (w : world) := ~(p w).
Definition M_neq (a b : object) (w : world) := ~(a = b).
Definition M_conj (p1 p2 : ModalProp) (w : world) := (p1 w) /\ (p2 w).
Definition M_dis (p1 p2 : ModalProp) (w : world) := (p1 w) \/ (p2 w).
Definition M_implies (p1 p2 : ModalProp) (w : world) := (p1 w) -> (p2 w).
Definition M_iff (p1 p2 : ModalProp) (w : world) := (p1 w) <-> (p2 w).


(* Equivalence relation on worlds *)
Parameter R : world -> world -> Prop.


(* Axioms about R *)
Axiom R_reflexive : forall w, R w w.
Axiom R_symmetric : forall w1 w2, R w1 w2 -> R w2 w1.
Axiom R_transitive : forall w1 w2 w3, R w1 w2 -> R w2 w3 -> R w1 w3.


(** Modal Operators *)

(* 1. Necessarily (Box) *)
Definition box (p : ModalProp) : ModalProp :=
  fun w => forall w', R w w' -> p w'.

(* 2. Possibly (Diamond) *)
Definition dia (p : ModalProp) : ModalProp :=
  fun w => exists w', (R w w') /\ p w'.

(* Check if a ModalProp holds over all worlds *)
Definition holdsInAllWorlds (p : ModalProp) : Prop :=
  forall w, p w.

(** Quantifiers over objects *)
Definition M_all {t : Type} (p : t -> ModalProp) (w : world) : Prop
  :=
  forall x, p x w.
Definition M_exists {t : Type} (p : t -> ModalProp) (w : world) : Prop :=
  exists x, p x w.


Notation "x =M y" := (M_eq x y) (at level 70, right associativity).
Notation "~M p" := (M_not p) (at level 40) : type_scope.
Notation "x <>M y" := (M_neq x y) (at level 70, right associativity).
Notation "x /\M y" := (M_conj x y) (at level 60, right associativity).
Notation "x \/M y" := (M_dis x y) (at level 60, right associativity).
Notation "x ->M y" := (M_implies x y) (at level 70, right associativity).
Notation "x <->M y" := (M_iff x y) (at level 70, right associativity).
Notation "'forallM' x , p" := (M_all (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'forallM' x : t , p" := (M_all (fun x : t => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'existsM' x , p" := (M_exists (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'existsM' x : t , p" := (M_exists (fun x : t => p))
  (at level 200, x ident, right associativity) : type_scope.


(** Proofs About Modal Logic *)

(*
  Testing that implication works
*)
Example impl_intro : forall p q : ModalProp,
  holdsInAllWorlds (fun w => (p ->M (q ->M p)) w).
Proof.
  intros p q w.
  unfold "->M".
  intros Hpw Hqw.
  apply Hpw.
Qed.

(*
  Modus ponens
  If we have p ->M q and we have p then we have q.
*)
Example modus_ponens : forall p q : ModalProp,
  holdsInAllWorlds (fun w => p w -> (p ->M q) w -> q w).
Proof.
  intros p q w.
  intros Hp Hpq.
  apply Hpq.
  apply Hp.
Qed.

(*
  Testing conjunction, disjunction, and negation
*)
Example conj_works : forall p q : ModalProp,
  holdsInAllWorlds (fun w => (p /\M q) w -> p w).
Proof.
  intros p q w.
  intros HPandQ.
  unfold "/\M" in HPandQ.
  destruct HPandQ as [H1 H2].
  apply H1.
Qed.

Example test_disj :
  forall p q : ModalProp,
    holdsInAllWorlds (fun w => (p \/M q) w -> (~M (p \/M q)) w -> False).
Proof.
  intros p q w.
  intros HPorQ.
  intros contra.
  unfold "\/M" in *.
  unfold "~M" in contra.
  destruct HPorQ as [ H | H ].
  - apply contra. left. apply H.
  - apply contra. right. apply H.
Qed.


(*
  (Box p) -> p

  If p necessarily holds then p holds.
  This follows from the fact that R is reflexive on worlds.
*)
Lemma box_p_p :
  holdsInAllWorlds (forallM p, box p ->M p).
Proof.
  intros w p.
  intros H.
  unfold box in H.
  apply H.
  apply R_reflexive.
Qed.

(*
  (Box p) -> Box (Box p)

  If p necessarily holds, then it is necessarily the case that p
  necessarily holds.
  This follows from the fact that R is transitive on worlds.
*)
Lemma box_p_box_box_p : forall p : ModalProp,
  holdsInAllWorlds (fun w => box p w -> box (box p) w).
Proof.
  intros p w.
  intros HBpw.
  unfold box.
  intros w' HR.
  intros w'0 Rw'w'0.
  unfold box in HBpw.
  apply HBpw.
  apply R_transitive with w'.
  - apply HR.
  - apply Rw'w'0.
Qed.


(*
  p -> Box (Dia p)

  If p holds in world w, then it is the case that in any world
  w', p is possibly true since we can jump back to w itself.
  This follows from the fact that R is symmetric on worlds.
*)
Lemma p_box_dia_p : forall p,
  holdsInAllWorlds (fun w => p w -> box (dia p) w).
Proof.
  intros p w.
  intros HBpw.
  unfold box.
  intros w' HRww'.
  unfold dia.
  specialize HRww' as HRw'w.
  apply R_symmetric in HRw'w.
  exists w. (* just take world w itself *)
  split.
  - apply HRw'w.
  - apply HBpw.
Qed.

(*
  Dia p -> Box (Dia p)

  If possibly p, then in every accessible world
  it is the case that possibly p.
*)
Lemma dia_p_box_dia_p : forall p,
  holdsInAllWorlds (fun w => dia p w -> box (dia p) w).
Proof.
  intros p w.
  intros HDpw.
  unfold box.
  unfold dia in *.
  destruct HDpw as [w' [HRww' Hpw']].
  intros w'0 HRww'0.
  specialize HRww' as HRw'w.
  apply R_symmetric in HRw'w.
  exists w'.
  split.
  - apply R_transitive with w.
    + specialize HRww'0 as HRw'0w.
      apply R_symmetric in HRw'0w.
      apply HRw'0w.
    + apply HRww'.
  - apply Hpw'.
Qed.


(*
  Dia p <-> Not (Box (Not P))

  p possibly holds if and only if it is not the case that
  necessarily p does not hold.
*)
Lemma dia_iff_not_box_not_p : forall p,
  holdsInAllWorlds (fun w => dia p w <-> (~M (box (~M p))) w).
Proof.
  intros p w.
  split.
  - intros HDpw.
    unfold "~M".
    intros contra.
    unfold box in *.
    unfold dia in *.
    destruct HDpw as [w' [HRww' Hpw']].
    apply contra in Hpw'.
    + destruct Hpw'.
    + apply HRww'.
  - intros HNBNp.
    unfold "~M" in *.
    unfold box in *.
    unfold dia in *.
    Search (~ ~ _ -> _).
    apply NNPP. (* ~~P -> P *)
    intros HND.
    apply HNBNp.
    intros w'.
    intros HRww'.
    intros Hpw'.
    apply HND.
    exists w'.
    split.
    + apply HRww'.
    + apply Hpw'.
Qed.


(*
  ~ (Dia p) -> Box (~ p).

  If it is not the case that p possibly holds, then it is
  necessarily the case that p does not hold.
*)
Lemma not_dia_box_not_p :
  (* We can also write the proofs using this notation which
  handles writing the function which takes in a world. *)
  holdsInAllWorlds (forallM p, (~M (dia p)) ->M (box (~M p))).
Proof.
  intros w.
  unfold M_all.
  intros x.
  unfold "~M".
  unfold "->M".
  intros HNDxw.
  unfold box.
  intros w'.
  intros HRww'.
  intros contra.
  unfold dia in *.
  apply HNDxw.
  exists w'.
  split.
  - apply HRww'.
  - apply contra.
Qed.

(*
  Modus ponens but with the diamond operator
*)
Lemma modus_ponens_dia :
  holdsInAllWorlds (
    forallM p, forallM q, (dia p) ->M (box (p ->M q) ->M (dia q))).
Proof.
  intros w.
  (* letting the notation handle the worlds allows us to work on
  the level of ModalProps *)
  intros p q.
  intros HDp.
  intros HBptoq.
  unfold dia in *.
  unfold box in *.
  destruct HDp as [w' [HRww' Hpw']].
  exists w'.
  split.
  - apply HRww'.
  - apply HBptoq in HRww'.
    specialize modus_ponens as MP.
    apply MP with (p := p) (q := q).
    apply Hpw'.
    apply HRww'.
Qed.

(*
  Law of the excluded middle:
  Box (p or ~p)
*)
Lemma lem : 
  holdsInAllWorlds (forallM p, box (p \/M (~M p))).
Proof.
  intros w p.
  intros w' HRww'.
  unfold "\/M" in *.
  specialize classic with (p w') as HL.
  apply HL.
Qed.


(*
  Box (~ p) -> ~ (Dia p)
  If p necessarily does not hold then necessarily p cannot possibly hold
*)
Lemma box_not_p_not_dia_p :
  holdsInAllWorlds (forallM p, (box (~M p)) ->M (~M (dia p))).
Proof.
  intros w.
  intros p.
  intros HBNp.
  unfold "~M" in *.
  intros contra.
  unfold dia in contra.
  destruct contra as [w' [HRww' Hpw']].
  unfold box in HBNp.
  apply HBNp in HRww'.
  apply HRww' in Hpw'.
  destruct Hpw'.
Qed.


(*
  Dia (Box p) -> p
  If possibly p necessarily holds then p holds.
*)
Lemma dia_box_p_p :
  holdsInAllWorlds (forallM p, (dia (box p)) ->M p).
Proof.
  intros w p.
  intros HDBp.
  destruct HDBp as [w' [HRww' Hpw']].
  apply Hpw'.
  apply R_symmetric.
  apply HRww'.
Qed.
    

(*
  Box (p -> q) -> (Box p -> Box q)

  If necessarily p implies q, then
  necessarily p implies necessarily q.
*)
Lemma box_distributes :
  holdsInAllWorlds
    (forallM p, forallM q, (box (p ->M q)) ->M (box p ->M box q)).
Proof.
  intros w p q.
  intros HBpq.
  intros HBp.
  unfold box in *.
  unfold "->M" in HBpq.
  intros w' HRww'.
  apply HBpq.
  - apply HRww'.
  - apply HBp.
    apply HRww'.
Qed.


(*
  Barcan Formula

  Box (forall x, P x) -> forall x, Box (P x)
*)
Lemma barcan_forward :
  forall p,
    holdsInAllWorlds (
      box (forallM x : object, p x) ->M (forallM x, box (p x))).
Proof.
  intros p w.
  intros Hb.
  unfold box in *.
  unfold M_all in *.
  intros x w' HRww'.
  apply Hb.
  apply HRww'.
Qed.

(*
  Converse Barcan Formula

  forall x, Box (P x) -> Box (forall x, P x)
*)
Lemma barcan_converse :
  forall p,
    holdsInAllWorlds (
      (forallM x, box (p x)) ->M (box (forallM x : object, p x))).
Proof.
  intros p w H.
  unfold box in *.
  unfold M_all in *.
  intros w' HRww' x.
  apply H.
  apply HRww'.
Qed.

Lemma barcan :
  forall p,
    holdsInAllWorlds (
      (forallM x, box (p x)) <->M (box (forallM x : object, p x))).
Proof.
  split.
  - apply barcan_converse.
  - apply barcan_forward.
Qed.


(*
  Dia (x = y) -> Box (x = y)

  If possibly x = y then x = y in every world.
*)
Lemma possibly_necessarily_eq :
  holdsInAllWorlds (
    forallM x : object, forallM y : object,
      dia (x =M y) ->M box (x =M y)).
Proof.
  intros w x y.
  intros HDeq.
  unfold dia in *.
  unfold box in *.
  unfold "=M" in *.
  destruct HDeq as [w' [HRww' Heq]].
  intros w'0.
  intros H.
  apply Heq.
Qed.

(*
  x = y -> Box (x = y)

  If x = y then x = y in every world.
*)
Lemma x_eq_y_box_x_eq_y :
  holdsInAllWorlds (
    forallM x : object, forallM y : object,
      (x =M y) ->M box (x =M y)).
Proof.
  intros w x y.
  intros Heq.
  intros w'.
  unfold "=M" in Heq.
  intros HRww'.
  rewrite Heq.
  reflexivity.
Qed.


(*
  Substitution inside box

  (x = y) /\ Box (P x) -> Box (P y)
*)
Lemma sub_inside_box :
  forall p,
    holdsInAllWorlds (forallM x : object, forallM y : object,
      ((x =M y) /\M box (p x)) ->M box (p y)).
Proof.
  intros p w x y.
  intros HBpx.
  destruct HBpx as [Hxy HBpx].
  unfold "=M" in Hxy.
  unfold box in *.
  intros w' HRww'.
  rewrite <- Hxy.
  apply HBpx.
  apply HRww'.
Qed.


(*
  Box p -> Dia p
  If p necessarily holds then p possibly holds
*)
Lemma box_p_dia_p :
  holdsInAllWorlds (forallM p, box p ->M dia p).
Proof.
  intros w p.
  intros HBp.
  unfold box in *.
  unfold dia in *.
  specialize HBp with w.
  exists w.
  split.
  - apply R_reflexive.
  - apply HBp.
    apply R_reflexive.
Qed.

(*
  Dia Dia p -> Dia p
  If p is possibly possible then p is possible
*)
Lemma dia_dia_p_dia_p :
  holdsInAllWorlds (forallM p, dia (dia p) ->M dia p).
Proof.
  intros w p.
  intros HDDp.
  unfold dia in *.
  destruct HDDp as [w' [HRww' [w'0 [HRw'w'0 Hpw'0]]]].
  exists w'0.
  split.
  - apply R_transitive with (w2 := w').
    + apply HRww'.
    + apply HRw'w'0.
  - apply Hpw'0.
Qed.


(*
  Dia Box p -> Box p
*)
Lemma dia_box_p_box_p :
  holdsInAllWorlds (forallM p, dia (box p) ->M box p).
Proof.
  intros w p.
  intros HDBp.
  unfold dia in *.
  unfold box in *.
  destruct HDBp as [w' [HRww' H]].
  intros w'0 HRww'0.
  apply H.
  apply R_symmetric in HRww'.
  apply R_transitive with (w2 := w).
  - apply HRww'.
  - apply HRww'0.
Qed.



(*
  Dia Box p -> Box Dia Box p
*)
Lemma dia_box_p_box_dia_box_p :
  holdsInAllWorlds (forallM p, dia (box p) ->M box (dia (box p))).
Proof.
  intros w p.
  intros H.
  unfold dia in *.
  unfold box in *.
  destruct H as [w' [HRww' H]].
  intros w'0 HRww'0.
  exists w.
  split.
  - apply R_symmetric.
    apply HRww'0.
  - intros w'1 HRww'1.
    apply H.
    apply R_symmetric in HRww'.
    apply R_transitive with (w2 := w).
    + apply HRww'.
    + apply HRww'1.
Qed.


(*
  Box distributes over /\
*)
Lemma box_and_distributes :
  holdsInAllWorlds (forallM p, forallM q, box (p /\M q) ->M box p /\M box q).
Proof.
  intros w p q HBpq.
  unfold box in *.
  split.
  - intros w' HRww'.
    specialize (HBpq) with w'.
    apply HBpq in HRww'.
    destruct HRww' as [Hp Hq].
    apply Hp.
  - intros w' HRww'.
    specialize (HBpq) with w'.
    apply HBpq in HRww'.
    destruct HRww' as [Hp Hq].
    apply Hq.
Qed.


(*
  Box (~ p) -> ~p
*)
Lemma box_not_p_not_p :
  forall p : ModalProp,
    holdsInAllWorlds (box (~M p) ->M ~M p).
Proof.
  intros p w.
  intros HB.
  unfold box in *.
  specialize HB with w.
  apply HB.
  apply R_reflexive.
Qed.



(* lifting ∃ under box in one world: *)
Lemma ex_box_to_box_ex :
  forall (p : object -> ModalProp),
    holdsInAllWorlds (
      (existsM x, box (p x)) ->M (box (existsM x, p x))).
Proof.
  intros p w.
  unfold "->M".
  unfold M_exists.
  intros H.
  destruct H as [x Hbox_p_x].
  unfold box in *.
  intros w' Rww'.
  exists x.
  apply Hbox_p_x.
  apply Rww'.
Qed.

(* lifting inside of a dia: *)
Lemma dia_ex_box_to_dia_box_ex :
  forall (p : object -> ModalProp),
    holdsInAllWorlds (
      dia (existsM x, box (p x)) ->M dia (box (existsM x, p x))).
Proof.
  intros p w H.
  unfold dia in *.
  destruct H as [w' [Rww' HexBox]].
  exists w'. split.
  - apply Rww'.
  - specialize (ex_box_to_box_ex p w') as Hlift.
    unfold "->M" in Hlift.
    apply Hlift in HexBox.
    apply HexBox.
Qed.



(*
  ~ (Box p) -> Dia (Not p)
*)
Lemma not_box_dia_not :
  forall (p : ModalProp) (w : world),
    ~ (box p w) ->
    (dia (fun w' => ~ p w') w).
Proof.
  intros p w.
  intros NHBp.
  unfold box in *.
  unfold dia in *.

  (* need to negate an implication *)
  Search (~(_ -> _) -> _).
  apply Coq.Logic.Classical_Pred_Type.not_all_ex_not in NHBp.
  destruct NHBp as [w' Hw'].
  apply Coq.Logic.Classical_Pred_Type.not_all_ex_not in Hw'.
  destruct Hw' as [HRww' NHp].
  exists w'.
  split.
  - apply HRww'.
  - apply NHp.
Qed.

