From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import EquivDec.

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
  let H := fresh in 
  let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
  [eauto with bdestruct | destruct H as [H|H];
  [ | try first [apply not_lt in H | apply not_le in H] ] ].

(* theorems for dealing with equiv_dec in conditionals *)

Ltac solve_eq_dec x y := 
  destruct (equiv_dec x y); intuition auto with *.

Section equiv_dec_lemmas.
  Context {A B : Type} `{EqDec A eq}.

  Lemma equiv_dec_refl : forall {x : A} {b c : B}, 
    (if equiv_dec x x then b else c) = b.
  Proof.
    intros. solve_eq_dec x x.
  Qed.

  Lemma equiv_dec_eqb : forall {x y : A} {b c : B},
    x = y -> 
    (if equiv_dec x y then b else c) = b.
  Proof.
    intros. solve_eq_dec x y.
  Qed.
  
  Lemma equiv_dec_negb : forall {x y : A} {b c : B},
    x <> y -> 
    (if equiv_dec x y then b else c) = c.
  Proof.
    intros. solve_eq_dec x y.
  Qed. 
End equiv_dec_lemmas.
                
