(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Require Import ZAxioms ZMulOrder ZSgnAbs NZDiv.
Require Import NZAdd NZOrder ZAdd NZBase.
Require Import GenericMinMax ZMaxMin. *)
Require Import Lia.

Require Import ZAxioms ZMulOrder ZSgnAbs NZDiv ZMul ZLt.
Module Type EuclidSpec (Import A : ZAxiomsSig')(Import B : DivMod A).
 Axiom mod_always_pos : forall a b, b ~= 0 -> 0 <= B.modulo a b < abs b.
End EuclidSpec.

Module Type ZEuclid (Z:ZAxiomsSig) := NZDiv.NZDiv Z <+ EuclidSpec Z.

Module ZEuclidProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZSgnAbsProp A B)
 (Import D : ZEuclid A).

(* We put notations in a scope, to avoid warnings about redefinitions of notations *)
Infix "/" := D.div : euclid.
Infix "mod" := D.modulo : euclid.
Local Open Scope euclid.


Locate t.
 (* Module Import Private_NZDiv := Nop <+ NZDivProp A D B.


 Require Import BinInt.
 Delimit Scope Int_scope with I.
 Local Open Scope Z_scope.

 Locate t. *)

(* Begin Interval Definition *)

(* this is option t but with a diff name for clarity *)
Inductive Numeric : Type :=
    | Some (v : t)
    | None.

Record Interval := 
    Build_Interval 
    {
        minv : Numeric;
        maxv: Numeric;
    }.

Definition Interval_inv (it : Interval) : Prop :=
    match (minv it), (maxv it) with 
    | Some x, Some y => x <= y
    | _, _ => True
    end.

Definition contains (it : Interval) (n : t) : Prop :=
    match (minv it), (maxv it) with 
    | Some x, Some y => x <= n /\ n <= y
    | Some x, _ => x <= n
    | _, Some y => n <= y
    | _, _ => True
    end.

Definition contains_numeric (it : Interval) (n : Numeric) : Prop :=
    match n with
    | Some n' => contains it n'
    | None => False
    end.

Definition eq (n1 n2 : Numeric) : Prop :=
    match n1, n2 with 
    | Some x, Some y => (eq x y)
    | None, None => True
    | _, _ => False
    end.

Definition plus (n1 n2 : Numeric) : Numeric :=
    match n1, n2 with 
    | Some x, Some y => Some (x + y)
    | _, _ => None
    end.

Definition div (n1 n2 : Numeric) : Numeric :=
    match n1, n2 with 
    | Some x, Some y => if (eqb y 0) then Some (0) else Some (x / y)
    | _, _ => None
    end.

(* lt only defined for bounded values *)
Definition lt_numeric (n1 n2: Numeric) : Prop :=
    match n1, n2 with
    | Some x, Some y => x < y
    | _, _ => True
    end.

Definition gt_numeric (n1 n2: Numeric) : Prop :=
    match n1, n2 with
    | Some x, Some y => x > y
    | _, _ => True
    end.

Definition gte_numeric (n1 n2: Numeric) : Prop :=
    (gt_numeric n1 n2) \/ (eq n1 n2).

Definition lte_numeric (n1 n2: Numeric) : Prop :=
    (lt_numeric n1 n2) \/ (eq n1 n2).

Definition is_single_point (it : Interval) : Prop :=
    eq (minv it) (maxv it).


Lemma silly_interval_single : forall (st bt : Numeric), ~(eq st bt) <-> ~(is_single_point (Build_Interval st bt)).
Proof.
    split.
    {
        intros H.
        unfold is_single_point. simpl. apply H.
    }
    {
        intros H. 
        unfold is_single_point in H. 
        simpl in H. apply H.
    }
Qed.

Definition is_everything (it : Interval) : Prop :=
    and (eq (minv it) (None)) (eq (maxv it) (None)).

Definition has_upper_bound (it : Interval) : Prop :=
    (~(eq (maxv it) (None))).

Definition has_lower_bound (it : Interval) : Prop :=
    (~(eq (minv it) (None))).
    
Definition is_bounded (it : Interval) : Prop :=
    and (has_upper_bound it) (has_lower_bound it).

Lemma bounded_means_not_everything : forall (it : Interval),
    is_bounded it -> ~is_everything it.
Proof.
    intros it H.
    unfold is_bounded in H.
    destruct H as [HUpper HLower].
    unfold has_upper_bound in HUpper.
    unfold has_lower_bound in HLower.
    (* destruct HUpper as [HNotEmpty HMaxNotPosInf].
    destruct HLower as [HNotEmpty' HMinNotNegInf]. *)
    unfold is_everything.
    intuition. (* Min not neginf and max not pos inf *)
Qed.

Definition lower_bounded (it : Interval) : Prop := 
    exists n', (minv it) = Some n'.

Definition only_lower_bounded (it : Interval) : Prop := 
    lower_bounded it /\ (maxv it) = None.

Definition upper_bounded (it : Interval) : Prop := 
    exists n', (maxv it) = Some n'.

Definition only_upper_bounded (it : Interval) : Prop := 
    upper_bounded it /\ (minv it) = None.

Definition bounded (it : Interval) : Prop := 
    (lower_bounded it) /\ (upper_bounded it).

Definition is_positive_point (it : Interval) : Prop :=
    exists n', (bounded it) /\ (minv it) = Some n' /\ (maxv it) = Some n' /\ n' > 0.

Definition is_negative_point (it : Interval) : Prop :=
    exists n', (bounded it) /\ (minv it) = Some n' /\ (maxv it) = Some n' /\ n' < 0.

Require Import Tactics.
Require Import Ring.

Lemma lower_bounded_implies_t_bound :
    forall (it : Interval),
    (lower_bounded it) -> 
    exists n, (minv it) = Some n.
Proof.
    intros. unfold bounded in H. 
    unfold lower_bounded in H. 
    destruct_one_ex. (* turns H into the lower bound *)
    exists H.
    intuition.
Qed.

Lemma upper_bounded_implies_t_bound :
    forall (it : Interval),
    (upper_bounded it) -> 
    exists n, (maxv it) = Some n.
Proof.
    intros. unfold bounded in H. 
    unfold upper_bounded in H. 
    destruct_one_ex. (* turns H into the lower bound *)
    exists H.
    intuition.
Qed.

Lemma bounded_implies_t_bounds :
    forall (it : Interval),
    (bounded it) -> 
    (exists n0, (minv it) = Some n0) /\ (exists n1, (maxv it) = Some n1).
Proof.
    intros.
    unfold bounded in H.
    destruct H as [Hlower Hupper].
    split.
    {
        apply lower_bounded_implies_t_bound. intuition.
    }
    {
        apply upper_bounded_implies_t_bound. intuition.
    } 
Qed.

(* Thanks Tej! https://github.com/tchajed/coq-tricks *)
Ltac deex :=
    repeat match goal with
        | [ H: exists (name:_), _ |- _ ] =>
        let name' := fresh name in
        destruct H as [name' H]
        end.

Require Import Omega.


Lemma value_bounded : forall (i n : t),
    n <= i <= n -> i = n.
Proof.
(* TODO: do this later, how is this not built in? *)
Admitted. 

Lemma le_refl : forall (i : t),
    i <= i <= i.
Proof.
(* TODO: do this later, how is this not built in? *)
Admitted.

Lemma div_pos_bounded : forall (i j n : t),
    n > 0 /\ i <= j -> i / n <= j / n.
Proof.
Admitted.

Lemma div_neg_bounded : forall (i j n : t),
    n < 0 /\ i <= j -> j / n <= i / n.
Proof.
Admitted.

Definition div_bounded_single_pos_point (a b : Interval) : Interval :=
        let a0 := (minv a) in
        let a1 := (maxv a) in
        let bp := (minv b) in
        let e0 := (div a0 bp) in
        let e1 := (div a1 bp) in
    Build_Interval e0 e1.

(* Begin Div proofs *)
Theorem div_bounded_single_pos_point_ok : forall (a b : Interval),
    (bounded a /\ is_positive_point b) ->
        let r := (div_bounded_single_pos_point a b) in
        forall (i j : t),
            (contains a i) /\ (contains b j) ->
                (contains_numeric r (div (Some i) (Some j))).
Proof.
    intros.
    destruct H as [Ha_bounded Hb_single].
    destruct H0 as [Ha_contains_i Hb_contains_j].
    apply bounded_implies_t_bounds in Ha_bounded.
    destruct Ha_bounded as [Ha_min Ha_max].
    deex.
    unfold contains in *.
    rewrite Ha_min in Ha_contains_i.
    rewrite Ha_max in Ha_contains_i.
    unfold is_positive_point in Hb_single.
    deex. destruct Hb_single as [Hb_bounded [ Hb_min [ Hb_max Hb_pos ] ] ].
    rewrite Hb_min in Hb_contains_j.
    rewrite Hb_max in Hb_contains_j.
    unfold r.
    unfold div_bounded_single_pos_point.
    rewrite Ha_min. rewrite Hb_min.
    rewrite Ha_max. unfold div.
    destruct (eqb n' 0) eqn:E.
    { (* equal to 0 *)
        apply value_bounded in Hb_contains_j.
        rewrite <- Hb_contains_j in E.
        rewrite E.
        unfold contains_numeric. 
        unfold contains. simpl.
        apply le_refl.
    }
    { (* NOT equal to 0 *)
        apply value_bounded in Hb_contains_j.
        rewrite <- Hb_contains_j in E.
        rename Hb_contains_j into Hj_equalsn'.
        rewrite E.
        unfold contains_numeric. 
        unfold contains. simpl.
        split.
        {
            destruct Ha_contains_i as [Higt Hilt].
            rewrite Hj_equalsn'.
            apply div_pos_bounded.
            intuition. 
        }
        {
            rewrite Hj_equalsn'.
            apply div_pos_bounded.
            intuition.
        }
    }
Qed.

Definition div_lower_bounded_single_pos_point (a b : Interval) : Interval :=
        let a0 := (minv a) in
        let bp := (minv b) in
        let e0 := (div a0 bp) in
        let e1 := None in
    Build_Interval e0 e1.

Theorem div_lower_bounded_single_pos_point_ok : forall (a b : Interval),
    (only_lower_bounded a /\ is_positive_point b) ->
        let r := (div_lower_bounded_single_pos_point a b) in
        forall (i j : t),
            (contains a i) /\ (contains b j) ->
                (contains_numeric r (div (Some i) (Some j))).
Proof.
    intros.
    destruct H as [Ha_lb Hb_single].
    destruct H0 as [Ha_contains_i Hb_contains_j].
    unfold only_lower_bounded in Ha_lb.
    destruct Ha_lb as [Ha_min Ha_max].
    apply lower_bounded_implies_t_bound in Ha_min.
    deex. (* exists in Ha_lb *)
    unfold contains in *.
    rewrite Ha_min in Ha_contains_i.
    rewrite Ha_max in Ha_contains_i.
    unfold is_positive_point in Hb_single.
    deex. destruct Hb_single as [Hb_bounded [ Hb_min [ Hb_max Hb_pos ] ] ].
    rewrite Hb_min in Hb_contains_j.
    rewrite Hb_max in Hb_contains_j.
    unfold r.
    unfold div_lower_bounded_single_pos_point.
    rewrite Ha_min. rewrite Hb_min.
    unfold div.
    destruct (eqb n' 0) eqn:E. (* why do this? 0 < n' is hypothesis *)
    {
        apply value_bounded in Hb_contains_j.
        rewrite <- Hb_contains_j in E.
        rewrite E.
        unfold contains_numeric. 
        unfold contains. simpl.
        apply le_refl.
    }
    { (* NOT equal to 0 *)
        apply value_bounded in Hb_contains_j.
        rewrite <- Hb_contains_j in E.
        rename Hb_contains_j into Hj_equalsn'.
        rewrite E.
        unfold contains_numeric. 
        unfold contains. simpl.
        rewrite Hj_equalsn'.
        apply div_pos_bounded.
        intuition.
    }
Qed.


Definition div_upper_bounded_single_pos_point (a b : Interval) : Interval :=
        let a1 := (maxv a) in
        let bp := (minv b) in
        let e0 := None in
        let e1 := (div a1 bp) in
    Build_Interval e0 e1.

Theorem div_upper_bounded_single_pos_point_ok : forall (a b : Interval),
    (only_upper_bounded a /\ is_positive_point b) ->
        let r := (div_upper_bounded_single_pos_point a b) in
        forall (i j : t),
            (contains a i) /\ (contains b j) ->
                (contains_numeric r (div (Some i) (Some j))).
Proof.
    intros.
    destruct H as [Ha_ub Hb_single].
    destruct H0 as [Ha_contains_i Hb_contains_j].
    unfold only_upper_bounded in Ha_ub.
    destruct Ha_ub as [Ha_max Ha_min].
    apply upper_bounded_implies_t_bound in Ha_max.
    deex. (* exists in Ha_lb *)
    unfold contains in *.
    rewrite Ha_min in Ha_contains_i.
    rewrite Ha_max in Ha_contains_i.
    unfold is_positive_point in Hb_single.
    deex. destruct Hb_single as [Hb_bounded [ Hb_min [ Hb_max Hb_pos ] ] ].
    rewrite Hb_min in Hb_contains_j.
    rewrite Hb_max in Hb_contains_j.
    unfold r.
    unfold div_upper_bounded_single_pos_point.
    rewrite Ha_max. rewrite Hb_min.
    unfold div.
    destruct (eqb n' 0) eqn:E. (* why do this? 0 < n' is hypothesis *)
    {
        apply value_bounded in Hb_contains_j.
        rewrite <- Hb_contains_j in E.
        rewrite E.
        unfold contains_numeric. 
        unfold contains. simpl.
        apply le_refl.
    }
    { (* NOT equal to 0 *)
        apply value_bounded in Hb_contains_j.
        rewrite <- Hb_contains_j in E.
        rename Hb_contains_j into Hj_equalsn'.
        rewrite E.
        unfold contains_numeric. 
        unfold contains. simpl.
        rewrite Hj_equalsn'.
        apply div_pos_bounded.
        intuition.
    }
Qed.


Definition div_bounded_single_neg_point (a b : Interval) : Interval :=
        let a0 := (minv a) in
        let a1 := (maxv a) in
        let bn := (minv b) in
        let e0 := (div a1 bn) in
        let e1 := (div a0 bn) in
    Build_Interval e0 e1.

Theorem div_bounded_single_neg_point_ok : forall (a b : Interval),
    (bounded a /\ is_negative_point b) ->
        let r := (div_bounded_single_neg_point a b) in
        forall (i j : t),
            (contains a i) /\ (contains b j) ->
                (contains_numeric r (div (Some i) (Some j))).
Proof.
    intros.
    destruct H as [Ha_bounded Hb_single].
    destruct H0 as [Ha_contains_i Hb_contains_j].
    apply bounded_implies_t_bounds in Ha_bounded.
    destruct Ha_bounded as [Ha_min Ha_max].
    deex.
    unfold contains in *.
    rewrite Ha_min in Ha_contains_i.
    rewrite Ha_max in Ha_contains_i.
    unfold is_negative_point in Hb_single.
    deex. destruct Hb_single as [Hb_bounded [ Hb_min [ Hb_max Hb_pos ] ] ].
    rewrite Hb_min in Hb_contains_j.
    rewrite Hb_max in Hb_contains_j.
    unfold r.
    unfold div_bounded_single_neg_point.
    rewrite Ha_min. rewrite Hb_min.
    rewrite Ha_max. unfold div.
    apply value_bounded in Hb_contains_j.
    rewrite Hb_contains_j.
    destruct (eqb n' 0) eqn:E.
    { (* equal to 0 *)
        unfold contains_numeric. 
        unfold contains. simpl.
        apply le_refl.
    }
    { (* NOT equal to 0 *)
        unfold contains_numeric. 
        unfold contains. simpl.
        split.
        {
            destruct Ha_contains_i as [Higt Hilt].
            apply div_neg_bounded.
            intuition. 
        }
        {
            apply div_neg_bounded.
            intuition.
        }
    }
Qed.


Definition div_lower_bounded_single_neg_point (a b : Interval) : Interval :=
        let a0 := (minv a) in
        let bn := (minv b) in
        let e0 := None in
        let e1 := (div a0 bn) in
    Build_Interval e0 e1.

Theorem div_lower_bounded_single_neg_point_ok : forall (a b : Interval),
    (only_lower_bounded a /\ is_negative_point b) ->
        let r := (div_lower_bounded_single_neg_point a b) in
        forall (i j : t),
            (contains a i) /\ (contains b j) ->
                (contains_numeric r (div (Some i) (Some j))).
Proof.
    intros.
    destruct H as [Ha_bounded Hb_single].
    destruct H0 as [Ha_contains_i Hb_contains_j].
    unfold only_lower_bounded in Ha_bounded.
    destruct Ha_bounded as [Ha_min Ha_max].
    apply lower_bounded_implies_t_bound in Ha_min.
    destruct Ha_min as [a0 Ha_min].
    unfold contains in *.
    rewrite Ha_min in Ha_contains_i.
    rewrite Ha_max in Ha_contains_i.
    unfold is_negative_point in Hb_single.
    destruct Hb_single as [bn Hb_single].
    destruct Hb_single as [Hb_bounded [ Hb_min [ Hb_max Hb_pos ] ] ].
    rewrite Hb_min in Hb_contains_j.
    rewrite Hb_max in Hb_contains_j.
    unfold r.
    unfold div_lower_bounded_single_neg_point.
    rewrite Ha_min. rewrite Hb_min.
    unfold div.
    apply value_bounded in Hb_contains_j.
    rewrite Hb_contains_j.
    destruct (eqb bn 0) eqn:E.
    { (* equal to 0 *)
        unfold contains_numeric. 
        unfold contains. simpl.
        apply le_refl.
    }
    { (* NOT equal to 0 *)
        unfold contains_numeric. 
        unfold contains. simpl.
        apply div_neg_bounded.
        intuition.
    }
Qed.

