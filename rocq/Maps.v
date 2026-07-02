(*
CF Software Foundations Maps 
*)
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Export Strings.String.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List.
Import ListNotations.
Set Default Goal Selector "!".

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** We next introduce a convenient notation for extending an existing
    map with a new binding. *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** The [examplemap] above can now be defined as follows: *)

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

(** This completes the definition of total maps.  Note that we
    don't need to define a [find] operation on this representation of
    maps because it is just function application! *)

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(** When we use maps in later chapters, we'll need several fundamental
    facts about how they behave. *)

(** Even if you don't bother to work the following exercises,
    make sure you thoroughly understand the statements of the
    lemmas! *)

(** (Some of the proofs require the functional extensionality axiom,
    which was discussed in the [Logic] chapter.) *)

(** **** Exercise: 1 star, standard, optional (t_apply_empty)

    First, the empty map returns its default element for all keys: *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  intros A x v. reflexivity.
Qed.
  
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_eq)

    Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros A m x v. unfold t_update. rewrite String.eqb_refl. 
  reflexivity.  
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_neq)

    On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H. unfold t_update. rewrite <- String.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2. apply functional_extensionality. intros x'.
  unfold t_update. destruct ((x =? x')%string). 
  - reflexivity.
  - reflexivity.
Qed. 
(** [] *)

(** **** Exercise: 2 stars, standard (t_update_same)

    Given [string]s [x1] and [x2], we can use the tactic
    [destruct (eqb_spec x1 x2)] to simultaneously perform case
    analysis on the result of [String.eqb x1 x2] and generate
    hypotheses about the equality (in the sense of [=]) of [x1] and
    [x2].  With the example in chapter [IndProp] as a template,
    use [String.eqb_spec] to prove the following theorem, which states
    that if we update a map to assign key [x] the same value as it
    already has in [m], then the result is equal to [m]: *)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros A m x. apply functional_extensionality. intros x'.
  destruct (eqb_spec x x'). 
  - rewrite e. unfold t_update. rewrite String.eqb_refl. reflexivity.
  - unfold t_update. rewrite <- String.eqb_neq in n. 
    rewrite n. reflexivity.
Qed.   
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (t_update_permute)

    Similarly, use [String.eqb_spec] to prove one final property of
    the [update] function: If we update a map [m] at two distinct
    keys, it doesn't matter in which order we do the updates. *)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H. apply functional_extensionality.
  intros x. destruct (eqb_spec x x1) as [ H1 | H1 ].
  - unfold t_update. rewrite H1. rewrite String.eqb_refl.  
    rewrite <- String.eqb_neq in H. rewrite H. reflexivity.
  - unfold t_update. rewrite <- String.eqb_neq in H1. 
    rewrite String.eqb_sym in H1. rewrite H1. 
    destruct ((x2 =? x)%string). 
    + reflexivity.
    + reflexivity.
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(** We introduce a similar notation for partial maps: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Definition examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

(** We now straightforwardly lift all of the basic lemmas about total
    maps to partial maps.  *)

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

(** The [update_eq] lemma is used very often in proofs.  Adding it to
    Coq's global "hint database" allows proof-automation tactics such
    as [auto] to find it. *)
#[global] Hint Resolve update_eq : core.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

(** One last thing: For partial maps, it's convenient to introduce a
    notion of map inclusion, stating that all the entries in one map
    are also present in another: *)

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

(** We can then show that map update preserves map inclusion -- that is: *)

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.