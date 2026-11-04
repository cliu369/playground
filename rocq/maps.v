(*
CF Software Foundations Maps 
*)
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Strings.String.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Classes.EquivDec.

Require Import tactics.
Require Import utils. 

Section total_map. 
  Context {K V : Type} `{EqDec K eq}. 

  Definition total_map := K -> V. 

  Definition t_empty (v : V) : total_map := 
    fun _ => v.
    
  Definition t_update (m : total_map) (x : K) (v : V) := 
    fun x' => if equiv_dec x x' then v else m x'. 

  Notation "'_' '!->' v" := (t_empty v)
    (at level 100, right associativity).
    
  Notation "x '!->' v ';' m" := (t_update m x v)
    (at level 100, v at next level, right associativity).
  
  Lemma t_apply_empty : forall (x : K) (v : V),
    (_ !-> v) x = v.
  Proof.
    intros x v. reflexivity.
  Qed.

  Lemma t_update_eq : forall (m : total_map) x v,
    (x !-> v ; m) x = v.
  Proof.
    intros m x v. unfold t_update. rewrite equiv_dec_refl. reflexivity.
  Qed.

  Theorem t_update_neq : forall (m : total_map) x1 x2 v,
    x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
  Proof.
    intros m x1 x2 v HN. unfold t_update. 
    rewrite (equiv_dec_negb HN). reflexivity.
  Qed.

  Lemma t_update_shadow : forall (m : total_map) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
  Proof.
    intros m x v1 v2. apply functional_extensionality. intros x'.
    unfold t_update. destruct (equiv_dec x x'); reflexivity.
  Qed. 

  Theorem t_update_same : forall (m : total_map) x,
    (x !-> m x ; m) = m.
  Proof.
    intros m x. apply functional_extensionality. intros x'.
    destruct (equiv_dec x x'); unfold t_update.
    - rewrite e. rewrite equiv_dec_refl. reflexivity.  
    - rewrite (equiv_dec_negb c). reflexivity.
  Qed.  

  Theorem t_update_permute : forall (m : total_map) v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
  Proof.
    intros m v1 v2 x1 x2 HN. apply functional_extensionality.
    intros x. destruct (equiv_dec x x1) as [ H1 | H1 ].
    - unfold t_update. rewrite H1. rewrite equiv_dec_refl.
      rewrite (equiv_dec_negb HN). rewrite equiv_dec_refl.
      reflexivity.
    - unfold t_update. apply symmetry in H1. rewrite !(equiv_dec_negb H1).
      destruct (equiv_dec x2 x); reflexivity. 
  Qed.
End total_map.
Arguments total_map K V : clear implicits.

(* yikes *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
  
Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Definition examplemap' :=
    ( 2 !-> true; 1 !-> true; _ !-> false).

Section partial_map.
  Context {K V : Type} `{EqDec K eq}.
  
  Definition partial_map := total_map K (option V).

  Definition empty : partial_map := t_empty None.

  Definition update (m : partial_map) (x : K) (v: V) := 
    (x !-> Some v ; m).

  Notation "x '|->' v ';' m" := (update m x v)
    (at level 100, v at next level, right associativity).

  Notation "x '|->' v" := (update empty x v)
    (at level 100). 

  Lemma apply_empty : forall (x : K),
    empty x = None.
  Proof.
    intros. unfold empty. rewrite t_apply_empty. reflexivity.
  Qed.

  Lemma update_eq : forall (m : partial_map) x v,
    (x |-> v ; m) x = Some v.
  Proof.
    intros. unfold update. rewrite t_update_eq.
    reflexivity.
  Qed.

  Theorem update_neq : forall (m : partial_map) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
  Proof.
    intros. unfold update. rewrite t_update_neq; auto.
  Qed.

  Lemma update_shadow : forall (m : partial_map) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
  Proof.
    intros m x v1 v2. unfold update. rewrite t_update_shadow.
    reflexivity.
  Qed.

  Theorem update_same : forall (m : partial_map) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
  Proof.
    intros. unfold update. rewrite <- H0. apply t_update_same.
  Qed.

  Theorem update_permute : forall (m : partial_map) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
  Proof.
    intros m x1 x2 v1 v2. unfold update. apply t_update_permute.
  Qed.

  Definition includedin (m m' : partial_map) :=
    forall x v, m x = Some v -> m' x = Some v.

  Lemma includedin_update : forall (m m' : partial_map) (x : K) (vx : V),
    includedin m m' ->
    includedin (x |-> vx ; m) (x |-> vx ; m').
  Proof.
    unfold includedin. intros m m' x vx HIn y vy.
    destruct (equiv_dec x y) as [ Hxy | Hxy ].
    - rewrite Hxy. rewrite !update_eq. auto.
    - rewrite update_neq; try rewrite update_neq; auto.
  Qed.
End partial_map.
Arguments partial_map K V : clear implicits.

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100). 

Definition examplepmap :=
  (1 |-> true ; 2 |-> false).