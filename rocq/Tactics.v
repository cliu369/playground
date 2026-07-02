From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.

(* The bdestruct tactic is borrowed from 
https://softwarefoundations.cis.upenn.edu/vfa-current/Perm.html *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.eqb_eq.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.
#[global] Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
                    evar (e: Prop);
                    assert (H: reflect e X); subst e;
                    [eauto with bdestruct
                    | destruct H as [H|H];
                      [ | try first [apply not_lt in H | apply not_le in H] ] ].
                    
Definition obind {A B : Type} (oa : option A) (f : A -> option B) : option B :=
  match oa with
  | Some a => f a
  | None => None
  end.

Notation "x >>= f" := (obind x f) 
  (at level 50, left associativity).

Notation "'do' x <- a ; b" := (obind a (fun x => b))
  (at level 60, right associativity).
