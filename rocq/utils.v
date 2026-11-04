(* File for random useful stuff *)
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Classes.EquivDec.

Require Import tactics. 

(* bind for option *)
Definition obind {A B : Type} (oa : option A) (f : A -> option B) : option B :=
  match oa with
  | Some a => f a
  | None => None
  end.

Notation "x >>= f" := (obind x f) 
  (at level 50, left associativity).

Notation "'do' x <- a ; b" := (obind a (fun x => b))
  (at level 60, right associativity).


(* Theorems for rewriting equiv_dec in conditionals *)
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

(* simple immutable map based on lists of key-value pairs, 
   requires K to be a type that has decidable equality *)
Section smap.    
  Context {K V : Type} `{EqDec K eq}. 

  Definition smap := list (K * V).

  Fixpoint contains (m : smap) (key : K) : bool := 
    match m with 
    | [] => false 
    | (key', _) :: rest => 
      if equiv_dec key key' then true else contains rest key
    end 
  .
  
  Fixpoint insert (m : smap) (key : K) (value : V) : smap := 
    match m with 
    | [] => [(key, value)]
    | (key', value') :: rest => 
      if equiv_dec key key' 
      then (key, value) :: rest 
      else (key', value') :: insert rest key value
    end 
  .

  Fixpoint lookup (m : smap) (key : K) : option V := 
    match m with 
    | [] => None 
    | (key', value) :: rest => 
      if equiv_dec key key' then Some value 
      else lookup rest key
    end 
  .
End smap.
Arguments smap K V : clear implicits.