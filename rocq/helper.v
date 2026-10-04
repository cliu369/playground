(* File for Helperellaneous useful stuff *)
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import List. Import ListNotations.

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

Class EqDec (A : Type) := { 
  eqb : A -> A -> bool ;
  eqb_leibniz : forall x y, eqb x y = true -> x = y 
}.

(* simple immutable map based on lists of key-value pairs, 
   requires K to be a type that has decidable equality *)
Definition SimpleMap (K V : Type) := list (K * V).

Fixpoint has {K V : Type} `{EqDec K} (m : SimpleMap K V) (key : K) : bool :=
  match m with 
  | [] => false 
  | (key', _) :: rest => 
    if eqb key key' then true else has rest key 
  end 
.

Fixpoint insert {K V : Type} `{EqDec K}
     (m : SimpleMap K V) (key : K) (value : V) : SimpleMap K V :=
  match m with
  | [] =>
      [(key, value)]
  | (key', value') :: rest =>
      if eqb key key'
      then (key, value) :: rest
      else (key', value') :: insert rest key value
  end
.

Fixpoint lookup {K V : Type} `{EqDec K} (m: SimpleMap K V) (key : K) : option V := 
  match m with 
  | [] => None 
  | (key', value) :: rest => 
    if eqb key key' then Some value
    else lookup rest key 
  end 
.

Fixpoint iseven (n: nat) : bool := 
  match n with
  | O => true
  | S O => false
  | S (S n') => iseven n'
  end
.