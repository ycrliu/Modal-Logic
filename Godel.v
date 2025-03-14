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

(* This formalization is based on this version of Godel's argument:
https://www.researchgate.net/publication/259145246_Godel's_God_in_IsabelleHOL
*)



Definition Property : Type := object -> ModalProp.
Parameter Positive : Property -> ModalProp.


(* Axiom A1: "Either a property or its negation is positive, but not both" *)
Axiom A1 : 
  holdsInAllWorlds (
    forallM x : Property, (Positive (fun x' : object => ~M (x x'))) <->M ~M (Positive x)).


(* Axiom A2:
  "A property necessarily implied
  by a positive property is positive"
*)
Axiom A2 : 
  holdsInAllWorlds (
    forallM x : Property, forallM y : Property,
      (Positive x /\M box (forallM x', (x x') ->M (y x'))) ->M Positive y).


Theorem T1 :
  holdsInAllWorlds (
    forallM x : Property,
      (Positive x) ->M dia (existsM x', x x')).
Proof.
  intros w.
  unfold M_all.
  intros X.
  unfold "->M".
  intros HXpos.
  unfold M_not, dia, M_exists.
  apply NNPP.
  intro Hno.

  (*
    From Hno we get: for all w' accessible from w, there are no objects
    in w' that satisfy X.  I.e., in every w' with R w w', for all x', ~(X x' w').
    This implies box (forallM x', ~M (X x')) in world w.
  *)
  assert (HboxAllNot : box (forallM x', ~M (X x')) w).
  {
    unfold box, M_all, M_not.
    intros w' Rww'. 
    Search (~(exists _,_)).
    specialize Classical_Pred_Type.not_ex_all_not with (U := world) as Hno'.
    apply Hno' with (n := w') in Hno.
    Search (~(_/\_)).
    apply not_and_or in Hno.
    destruct Hno as [NRww' | NX].
    - exfalso.
      apply NRww'.
      apply Rww'.
    - Search (~(exists _,_)).
      apply Classical_Pred_Type.not_ex_all_not.
      apply NX.
  }

  assert (HboxImpl: box (forallM x', (X x') ->M ~M (X x')) w).
  {
    unfold box.
    intros w' Rww'.
    unfold M_all.
    intros x'.
    unfold "->M", M_not.
    intros HX'.
    exfalso.
    apply (HboxAllNot w' Rww' x').
    exact HX'.
  }

  (* apply A2 with x = X and y = fun x' => ~M(X x'):
    conclude Positive (fun x' => ~M (X x')) *)
  assert (Positive (fun x' => ~M (X x')) w) as HPosNot.
  {
    specialize (A2 w) as HA2w.
    unfold M_all in HA2w.
    specialize (HA2w X (fun x' => ~M (X x'))).
    unfold "->M" in HA2w.
    apply HA2w.
    split.
    - apply HXpos.
    - apply HboxImpl.
  }

  (* by A1, positivity of ~X contradicts positivity of X *)
  specialize (A1 w) as HA1w.
  unfold M_all in HA1w.
  specialize (HA1w X).
  unfold "<->M" in HA1w.
  destruct HA1w as [HLeft _].
  (* HPosNot has Positive (~X) so by A1 we get ~Positive X. contradiction. *)
  apply HLeft in HPosNot.
  apply HPosNot in HXpos.
  destruct HXpos.
Qed.



(* D1: "A God-like being possesses all positive properties:" *)
Definition GodLike (x : object) (w : world) :=
  forall x' : Property, Positive x' w -> x' x w.


(* A3: "The property of being God-like is positive" *)
Axiom A3 :
  holdsInAllWorlds (Positive GodLike).


(* C1: "Possibly, God exists" *)
Corollary C1 :
  holdsInAllWorlds (
    dia (existsM x : object, GodLike x)).
Proof.
  intros w.
  apply T1.
  apply A3.
Qed.


(* A4: "Positive properties are necessarily positive:" *)
Axiom A4 :
  holdsInAllWorlds (
    forallM x : Property, Positive x ->M box (Positive x)).


(* D2: "An essence of an individual is a property possessed by it
and necessarily implying any of its properties" *)
Definition Essence (phi : Property) (x : object) (w : world) :=
  (phi x w) /\
  forall psi : Property, (psi x w) ->
    (box (forallM y : object, (phi y) ->M (psi y))) w.


(* T2: Being God-like is an essence of any God-like being: *)
Theorem T2 : 
  holdsInAllWorlds (forallM x : object, GodLike x ->M (Essence GodLike x)).
Proof.
  intros w.
  intros x HGx.
  unfold Essence.
  split.
  - apply HGx.
  - unfold GodLike in HGx.
    intros psi Hpsi.
    assert (HPpsiw : Positive psi w).
    {
      apply NNPP.
      intros contra. (* get ~Positive so we can use Axiom 1*)
      apply A1 in contra.
      apply HGx in contra.
      apply contra in Hpsi.
      destruct Hpsi.
    }

    (* because psi is positive, by Axiom 4 psi is necessarily positive, meaning 
      we can use it in every world *)
    specialize (A4 w psi) as A4_inst. 
    apply A4_inst in HPpsiw.
    intros w' HRww'.
    intros y HGyw'. 
    unfold box in HPpsiw.
    specialize (HPpsiw w' HRww'). (* psi is positive in w' *)

    (* Because y is God-like in w', y also has every positive property in w' *)
    unfold GodLike in HGyw'.
    apply HGyw' in HPpsiw.
    apply HPpsiw.
Qed.


(* D3: Necessary existence of an individual is
the necessary exemplification of all its essences: *)
Definition NecessaryExistence (x : object) (w : world) :=
  forall x' : Property, (Essence x' x w) -> box (existsM y : object, x' y) w.


(* A5 Necessary existence is a positive property: *)
Axiom A5 :
  holdsInAllWorlds (Positive NecessaryExistence).


(* T3 Necessarily, God exists *)
Theorem T3 :
  holdsInAllWorlds (box (existsM x : object, GodLike x)).
Proof.
  intros w.  
  unfold box.
  intros w' Rww'.
  (* C tells us that God possibly exists. apply that "dia" prop to w' *)
  specialize (C1 w') as HC1w'.
  destruct HC1w' as [w'' [Rw'w'' Hex]].
  (* Hex : (existsM x, GodLike x) w'' means there is some object g with GodLike g w'' *)
  destruct Hex as [g Hgodlike_gw''].

  (* T2 tells us that at w'', if g is GodLike, then GodLike is an essence of g *)
  specialize (T2 w'' g) as HEss.
  specialize (HEss Hgodlike_gw'') as Ess_g.

  (* As g is GodLike in w'' so it has all the positive properties at w'' (
    by definition of GodLike). *)
  unfold GodLike in Hgodlike_gw''.
  (* A5 tells us NecessaryExistence is positive. So g has NecessaryExistence *)
  specialize (A5 w'') as HPosNE.  
  specialize (Hgodlike_gw'' NecessaryExistence HPosNE).

  (* Since T2 told us that GodLike is an essence of g, by NecessaryExistence,
    it must exist *)
  unfold NecessaryExistence in Hgodlike_gw''.
  specialize (Hgodlike_gw'' GodLike Ess_g).

  (* Hgodlike_gw'' tells us
    for all worlds accessible from w'',
    there is necessarily a GodLike object (definition of NecessaryExistence)

    w'' is accessible from w' (follows from S5 symmetry on R w' w'')
    so we can translate this to w'  *)
  unfold box in Hgodlike_gw''.
  specialize (R_symmetric w' w'' Rw'w'') as Rw''w'.
  specialize (Hgodlike_gw'' w' Rw''w').
  apply Hgodlike_gw''.
Qed.




