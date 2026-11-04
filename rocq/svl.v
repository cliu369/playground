(*
Language with deductive verification based on 
https://dl.acm.org/doi/10.1145/3704856

Uses big-step semantics + CPS symbolic execution.
*)
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Classes.EquivDec.

Require Import tactics.
Require Import utils.
Require Import maps.

Module SVL.

Instance string_eqdec : EqDec string Logic.eq := string_dec.

Definition state := partial_map string nat. 

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              
  | APlus (a1 a2 : aexp)
  (* | AMinus (a1 a2 : aexp) *)
  | AMult (a1 a2 : aexp)
.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.

Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 1,
                      y constr at level 1) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
(* Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity). *)
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
(* Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity). *)
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
(* Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity). *)
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Fixpoint aeval (st : state) (a : aexp) : option nat :=
  match a with
  | ANum n => Some n 
  | AId x => st x                
  | <{a1 + a2}> => 
    do n1 <- aeval st a1;
    do n2 <- aeval st a2; 
    Some (n1 + n2)
  (* | <{a1 - a2}> => 
    do n1 <- aeval st a1;
    do n2 <- aeval st a2; 
    Some (n1 - n2) *)
  | <{a1 * a2}> => 
    do n1 <- aeval st a1;
    do n2 <- aeval st a2;
    Some (n1 * n2)
  end.

Fixpoint beval (st : state) (b : bexp) : option bool :=
  match b with
  | <{true}> => Some true
  | <{false}> => Some false
  | <{a1 = a2}> => 
    do n1 <- aeval st a1; 
    do n2 <- aeval st a2;
    Some (n1 =? n2)
  | <{a1 <= a2}> => 
    do n1 <- aeval st a1; 
    do n2 <- aeval st a2;
    Some (n1 <=? n2)
  | <{~ b1}> => 
    do b <- beval st b1;
    Some (negb b)
  | <{b1 && b2}> => 
    do n1 <- beval st b1;
    do n2 <- beval st b2;
    Some (andb n1 n2)
  end. 

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CAssert : bexp -> com
.

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, 
                            l custom com at level 0) : com_scope.
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = Some n ->
      st =[ x := a ]=> (x |-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = Some true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = Some false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_Assert : forall st b,
      beval st b = Some true -> 
      st =[ assert b ]=> st

where "st =[ c ]=> st'" := (ceval c st st').

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Example step1 : forall m, 
  (x |-> m) =[ y := 5 ]=>(y |-> 5; x |->m). 
Proof.
  intros. apply E_Asgn. reflexivity.
Qed.

Example com2 : com :=
  <{ if (x = 20) then x := 30 else x := 40 end }>.

Fixpoint aexp_vars (a: aexp): list string :=
  match a with 
  | ANum n => [] 
  | AId x => [x]
  | <{a1 + a2}> => (aexp_vars a1) ++ (aexp_vars a2)
  | <{a1 * a2}> => (aexp_vars a1) ++ (aexp_vars a2)
  end
.

Fixpoint bexp_vars (b: bexp) : list string := 
  match b with 
  | <{true}> => []
  | <{false}> => []
  | <{a1 = a2}> => (aexp_vars a1) ++ (aexp_vars a2)
  | <{a1 <= a2}> => (aexp_vars a1) ++ (aexp_vars a2)
  | <{~ b1}> => bexp_vars b1
  | <{b1 && b2}> => (bexp_vars b1) ++ (bexp_vars b2)
  end
.

Inductive binds (x : string) : com -> Prop :=
  | b_asgn : forall a, 
      binds x <{x := a}>
  | b_seq1 : forall c1 c2, 
      binds x c1 -> 
      binds x <{c1; c2}>
  | b_seq2 : forall c1 c2, 
      binds x c2 -> 
      binds x <{c1; c2}>
  | b_if   : forall b c1 c2, 
      binds x c1 -> 
      binds x c2 -> 
      binds x <{if b then c1 else c2 end}>
.

Inductive appears_free_in (x : string) : com -> Prop :=
  | afi_asgn : forall y a, 
      In x (aexp_vars a) -> 
      appears_free_in x <{y := a}>
  
  | afi_seq1 : forall c1 c2, 
      appears_free_in x c1 -> 
      appears_free_in x <{c1; c2}>
  
  | afi_seq2 : forall c1 c2, 
      appears_free_in x c2 -> 
      ~ binds x c1 -> 
      appears_free_in x <{c1; c2}>
  
  | afi_if_b : forall b c1 c2, 
      In x (bexp_vars b) -> 
      appears_free_in x <{if b then c1 else c2 end}>

  | afi_if_c1: forall b c1 c2, 
      appears_free_in x c1 -> 
      appears_free_in x <{if b then c1 else c2 end}>

  | afi_if_c2: forall b c1 c2, 
      appears_free_in x c2 -> 
      appears_free_in x <{if b then c1 else c2 end}>
  
  | afi_assert : forall b, 
      In x (bexp_vars b) -> 
      appears_free_in x <{assert b}>
.

Definition closed (c: com) : Prop := 
  forall x, ~ appears_free_in x c.

(* Symbolic Execution *)

Definition sym_val := nat.
Definition valuation := sym_val -> option nat.
Definition sym_aexp := valuation -> option nat.
Definition sym_bexp := valuation -> option bool.

Definition sym_implies (t1 t2 : sym_bexp) : Prop := 
  forall (V: valuation), t1 V = Some true -> t2 V = Some true.
  
Definition SUop {X Y : Type} (t : valuation -> option X)
  (uop: X -> Y) : valuation -> option Y := 
  fun (V: valuation) => 
    do v1 <- t V;
    Some (uop v1)
.

Definition SBinop {X Y: Type} (t1 t2 : valuation -> option X) 
  (binop: X -> X -> Y) : valuation -> option Y := 
  fun (V: valuation) => 
    do v1 <- t1 V;
    do v2 <- t2 V; 
    Some (binop v1 v2)
.

Definition s_store := partial_map string (sym_aexp).
Definition path_cond := sym_bexp.

Record sym_state : Type := mkSymState {
  sym_store : s_store;
  sym_cond : path_cond;
  sym_used : nat 
}.

Definition sym_store_add (s: sym_state) (x: string) (a: sym_aexp) : sym_state := {|
  sym_store := (x |-> a; (sym_store s));
  sym_cond := sym_cond s;
  sym_used := sym_used s
|}.

Definition sym_cond_add (s: sym_state) (b: sym_bexp) : sym_state := {| 
  sym_store := sym_store s;
  sym_cond := SBinop b (sym_cond s) (andb);
  sym_used := sym_used s
|}.

Definition sym_gen_fresh (s: sym_state) (Q: sym_state -> sym_val -> Prop) : Prop := 
  Q {| sym_store := sym_store s;
    sym_cond := sym_cond s;
    sym_used := S (sym_used s) 
  |} (sym_used s).
 
Fixpoint saeval (s: sym_state) (a: aexp) (K: sym_state -> sym_aexp -> Prop) : Prop :=   
  match a with 
  | ANum n => K s (fun V => Some n)
  | AId x => 
    match sym_store s x with 
    | Some t => K s t 
    | None => False
    end
  | APlus a1 a2 => 
    saeval s (a1) ( fun s1 t1 => 
      saeval s1 (a2) ( fun s2 t2 =>   
        K s2 (SBinop t1 t2 Nat.add)
      )
    )
  | AMult a1 a2 => 
    saeval s (a1) ( fun s1 t1 => 
      saeval s1 (a2) ( fun s2 t2 =>   
        K s2 (SBinop t1 t2 Nat.mul)
      )
    ) 
  end
. 

Fixpoint sbeval (s: sym_state) (b: bexp) (K: sym_state -> sym_bexp -> Prop) : Prop := 
  match b with
  | BTrue => K s (fun V => Some true)
  | BFalse => K s (fun V => Some false)
  | BEq a1 a2 => 
    saeval s a1 (fun s1 t1 => 
      saeval s1 a2 ( fun s2 t2 =>   
        K s2 (SBinop t1 t2 Nat.eqb)
      )
    )
  | BLe a1 a2 => 
    saeval s a1 (fun s1 t1 => 
      saeval s1 a2 ( fun s2 t2 =>   
        K s2 (SBinop t1 t2 Nat.leb)
      )
    )
  | BNot b => 
    sbeval s b (fun s1 t => 
      K s1 (SUop t negb)
    )
  | BAnd b1 b2 => 
    sbeval s b1 (fun s1 t1 => 
      sbeval s1 b2 ( fun s2 t2 =>   
        K s2 (SBinop t1 t2 andb)
      )
    )
  end 
.

Fixpoint sexec (s: sym_state) (c: com) (K: sym_state -> Prop) : Prop := 
  match c with 
  | <{ skip }> => K s 
  | <{ x := a }> => 
    saeval s a (fun s1 t => 
      K (sym_store_add s x t)
    )
  | <{ c1; c2 }> => 
    sexec s c1 (fun s1 => 
      sexec s1 c2 K
    )
  | <{ if b then c1 else c2 end }> => 
    sbeval s b (fun s1 t => 
      (sexec (sym_cond_add s1 t) c1 K) /\
      (sexec (sym_cond_add s1 (SUop t negb)) c2 K)
    )
  | <{ assert b }> => 
    sbeval s b (fun s1 t => 
      sym_implies (sym_cond s) t /\ K s1
    )
  end
.

Definition s2state (V: valuation) (s: sym_state) : state := 
  fun (x: string) => 
    do v <- (sym_store s) x; 
    v V
.

Definition sym_state_wf (V: valuation) (ss: sym_state): Prop :=
  (forall x t, (sym_store ss) x = Some t -> exists v, t V = Some v) /\ 
  ((sym_cond ss) V = Some true).

#[global] Hint Unfold SBinop : core. 
#[global] Hint Unfold SUop : core.

#[export] Hint Constructors ceval : core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.

Lemma s2state_exists : forall x t V st ss, 
  includedin (s2state V ss) (st) -> 
  (sym_store ss) x = Some t -> 
  sym_state_wf V ss -> 
  exists v, t V = Some v /\ st x = Some v.
Proof.
  intros x t V st ss HI HS HWF. 
  assert (s2state V ss (x) = t V).
  - simpl. unfold s2state. rewrite HS. reflexivity.
  - destruct (t V) eqn:Heq.
    + exists n. split; auto.
    + destruct HWF as (HWF & _). specialize (HWF x t HS).
      destruct HWF as (v & HWF). rewrite HWF in Heq. discriminate.
Qed.     

Lemma sym_store_add_wf : forall x t V ss v,
  t V = Some v -> 
  sym_state_wf V ss -> 
  sym_state_wf V (sym_store_add ss x t).
Proof.
  intros x t V ss v HT HWF. unfold sym_state_wf in *. split.
  - destruct HWF as (HWF & _). intros x0 t0. destruct (eqb_spec x0 x). 
    + subst. simpl. rewrite update_eq. intros. inversion H. subst.
      exists v. assumption.
    + simpl. rewrite update_neq; auto. intros. 
      apply HWF in H. assumption.
  - destruct HWF as (_ & HWF). assumption.
Qed. 

Lemma sym_store_add_ok : forall x t v V ss st,
  t V = Some v -> 
  includedin (s2state V ss) (st) -> 
  includedin (s2state V (sym_store_add ss x t)) (x |-> v; st).
Proof.
  unfold s2state. unfold includedin. intros x t v V ss st HT HM.
  simpl in *. intros x0 v0. destruct (eqb_spec x0 x).
  - subst. rewrite !update_eq. simpl. intros. rewrite HT in H. assumption.
  - rewrite !update_neq; auto.
Qed.

Lemma sym_cond_add_wf : forall t V ss,    
  t V = Some true -> 
  sym_state_wf V ss -> 
  sym_state_wf V (sym_cond_add ss t). 
Proof.
  unfold sym_state_wf. intros t V ss HT HWF. split.
  - destruct HWF as (HWF & _). apply HWF. 
  - destruct HWF as (_ & HWF). simpl. unfold SBinop. 
    rewrite HWF. rewrite HT. reflexivity. 
Qed.

Lemma sym_cond_add_ok : forall t V ss st, 
  includedin (s2state V ss) (st) -> 
  includedin (s2state V (sym_cond_add ss t)) st.
Proof. 
  auto. 
Qed.

Theorem saeval_sound : forall a V st ss Q,
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss -> 
  saeval ss a Q -> 
  exists t v ss', 
    (aeval st a = Some v) /\ 
    includedin (s2state V ss') st /\ 
    sym_state_wf V ss' /\ 
    t V = Some v /\ 
    Q ss' t. 
Proof.
  induction a; intros V st ss Q HM HWF HSE.  
  - simpl in *. eexists. exists n. exists ss. intuition.
  - rename x0 into x. simpl in *. 
    destruct (sym_store ss x) eqn: Heq; try contradiction.
    rename s into t. exists t. remember HM as HM2. clear HeqHM2.
    eapply s2state_exists in HM; eauto. 
    destruct HM as (v' & a & b).
    exists v', ss. intuition. 
  - simpl in *. specialize (IHa1 V st ss _ HM HWF HSE). 
    destruct IHa1 as (t1 & v1 & ss1 & HV1 & HM1 & HWF1 & HT1 & HSE2).
    clear HSE. specialize (IHa2 V st ss1 _ HM1 HWF1 HSE2).
    destruct IHa2 as (t2 & v2 & ss2 & HV2 & HM2 & HWF2 & HT2 & HQ).
    exists (SBinop t1 t2 add), (v1 + v2), (ss2). 
    rewrite HV1. rewrite HV2. unfold SBinop. rewrite HT1. rewrite HT2. intuition.
  - simpl in *. specialize (IHa1 V st ss _ HM HWF HSE). 
    destruct IHa1 as (t1 & v1 & ss1 & HV1 & HM1 & HWF1 & HT1 & HSE2).
    clear HSE. specialize (IHa2 V st ss1 _ HM1 HWF1 HSE2).
    destruct IHa2 as (t2 & v2 & ss2 & HV2 & HM2 & HWF2 & HT2 & HQ).
    exists (SBinop t1 t2 mul), (v1 * v2), (ss2). 
    rewrite HV1. rewrite HV2. unfold SBinop. rewrite HT1. rewrite HT2. intuition.
Qed.    

Theorem sbeval_sound : forall b V st ss Q, 
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss -> 
  sbeval ss b Q -> 
  exists t v ss', 
    (beval st b = Some v) /\ 
    includedin (s2state V ss') st /\ 
    sym_state_wf V ss' /\ 
    t V = Some v /\ 
    Q ss' t.
Proof.
  induction b; intros V st ss Q HM HWF HSE; simpl in *.
  - eexists. exists true, ss. intuition.
  - eexists. exists false, ss. intuition.
  - apply saeval_sound with (V := V) (st := st) in HSE; auto.
    destruct HSE as (t1 & v1 & ss1 & HV1 & HM1 & HWF1 & HT1 & HSE2).
    apply saeval_sound with (V := V) (st := st) in HSE2; auto.
    destruct HSE2 as (t2 & v2 & ss2 & HV2 & HM2 & HWF2 & HT2 & HQ).
    exists (SBinop t1 t2 Nat.eqb), (Nat.eqb v1 v2), (ss2). 
    rewrite HV1. rewrite HV2. unfold SBinop. rewrite HT1. rewrite HT2. intuition.
  - apply saeval_sound with (V := V) (st := st) in HSE; auto.
    destruct HSE as (t1 & v1 & ss1 & HV1 & HM1 & HWF1 & HT1 & HSE2).
    apply saeval_sound with (V := V) (st := st) in HSE2; auto.
    destruct HSE2 as (t2 & v2 & ss2 & HV2 & HM2 & HWF2 & HT2 & HQ).
    exists (SBinop t1 t2 Nat.leb), (Nat.leb v1 v2), (ss2). 
    rewrite HV1. rewrite HV2. unfold SBinop. rewrite HT1. rewrite HT2. intuition.
  - specialize (IHb V st ss _ HM HWF HSE). 
    destruct IHb as (t1 & v1 & ss1 & HV1 & HM1 & HWF1 & HT1 & HSE2).
    exists (SUop t1 negb), (negb v1), (ss1).
    rewrite HV1. unfold SUop. rewrite HT1. intuition.
  - specialize (IHb1 V st ss _ HM HWF HSE). 
    destruct IHb1 as (t1 & v1 & ss1 & HV1 & HM1 & HWF1 & HT1 & HSE2).
    clear HSE. specialize (IHb2 V st ss1 _ HM1 HWF1 HSE2).
    destruct IHb2 as (t2 & v2 & ss2 & HV2 & HM2 & HWF2 & HT2 & HQ).
    exists (SBinop t1 t2 andb), (v1 && v2), (ss2). 
    rewrite HV1. rewrite HV2. unfold SBinop. rewrite HT1. rewrite HT2. intuition.  
Qed.  


Theorem sexec_sound : forall C V st ss Q,
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss -> 
  sexec ss C Q -> 
  exists st' V' ss', 
    st =[ C ]=> st' /\ 
    includedin (s2state V' ss') st' /\
    sym_state_wf V' ss' /\ 
    Q ss'.
Proof.
  induction C; intros V st ss Q HM HWF HSE; simpl in *.
  - exists st, V, ss. intuition. 
  - rename x0 into x. apply saeval_sound with (V := V) (st := st) in HSE; auto.
    destruct HSE as (t & v & ss' & HV & HM' & HWF' & HT & HQ).  
    exists (x |-> v; st), V, (sym_store_add ss x t). 
    split; auto. split; auto.
    + apply sym_store_add_ok; auto.
    + split. apply sym_store_add_wf with (v := v); auto. assumption.  
  - specialize (IHC1 V st ss _ HM HWF HSE). 
    destruct IHC1 as (st1 & V1 & ss1 & HS1 & HM1 & HWF1 & HSE1).
    clear HSE. specialize (IHC2 V1 st1 ss1 _ HM1 HWF1 HSE1).
    destruct IHC2 as (st2 & V2 & ss2 & HS2 & HM2 & HWF2 & HSE2). 
    exists st2, V2, ss2. intuition. econstructor; eauto.
  - apply sbeval_sound with (V := V) (st := st) in HSE; auto.
    destruct HSE as (t & v & ss' & HV & HM' & HWF' & HT & HTRUE & HFALSE).
    clear HM HWF. destruct v.
    + clear HFALSE IHC2.  
      assert (includedin (s2state V (sym_cond_add ss' t)) st) as HM; auto. 
      clear HM'. assert (sym_state_wf V (sym_cond_add ss' t)) as HWF.
      apply sym_cond_add_wf; auto. clear HWF'.  
      specialize (IHC1 V st (sym_cond_add ss' t) Q HM HWF HTRUE). 
      destruct IHC1 as (st' & V' & ss'' & HS' & HM' & HWF' & HQ).
      exists st', V', ss''. intuition.
    + clear HTRUE IHC1. 
      assert (includedin (s2state V (sym_cond_add ss' (SUop t negb))) st) as HM; 
      auto. clear HM'. 
      assert (sym_state_wf V (sym_cond_add ss' (SUop t negb))) as HWF.
      apply sym_cond_add_wf; auto. unfold SUop. rewrite HT. reflexivity. clear HWF'.
      specialize (IHC2 V st (sym_cond_add ss' (SUop t negb)) Q HM HWF HFALSE).
      destruct IHC2 as (st' & V' & ss'' & HS' & HM' & HWF' & HQ).
      exists st', V', ss''. intuition.
  - apply sbeval_sound with (V := V) (st := st) in HSE; auto.
    destruct HSE as (t & v & ss' & HV & HM' & HWF' & HT & HIMP & HQ).
    exists st, V, ss'. intuition.
    apply E_Assert. unfold sym_implies in HIMP. destruct HWF as (_ & HWF).
    specialize (HIMP V HWF). rewrite HT in HIMP. rewrite HIMP in HV.
    assumption.
Qed.

Theorem sexec_verify : forall C V st ss Q,
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss -> 
  sexec ss C Q -> 
  exists st', st =[ C ]=> st'.
Proof.
  intros. eapply sexec_sound in H; eauto. destruct H as (st' & _ & _ & W & _).
  exists st'. apply W.
Qed.

Definition s_empty : sym_state := {|
  sym_store := empty; 
  sym_cond := (fun V => Some true); 
  sym_used := 0
|}.

Definition sverify (arg: string) (pre: bexp) (body: com) : Prop :=
  sym_gen_fresh (s_empty) (fun s t => 
    sbeval (sym_store_add s arg (fun V => V t)) (pre) (fun spre tb => 
      sexec (sym_cond_add spre tb) (body) (fun _ => True)
    )
  )
.

(*
we want to show that extending a valuation 
preserves evaluation of expressions

if we extend the valuation, then
looking up in the symbolic store 

If V' extends V and sym_store ss x = v
then v V' = v V

extending should mean
adding a new symbolic value s.t. valu_agree
*)

Definition valu_extends (V: valuation) (sv : sym_val) (v: nat) := 
  (fun va => if va =? (sv) then Some v else V va).

Lemma valu_extends_preserves : forall V sv v sv',
  sv' <> sv ->  
  (valu_extends V sv v) sv' = V sv'.
Proof.
  intros V sv v sv' HNeq. unfold valu_extends. bdestruct (sv' =? sv).
  contradiction. reflexivity.
Qed.

Definition valu_agree (v: sym_val) (V1 V2 : valuation) : Prop :=
  forall v', v' < v -> V1 v' = V2 v'.

Definition valu_indep (v: sym_val) (e: sym_aexp) : Prop := 
  forall V1 V2, valu_agree v V1 V2 -> e V1 = e V2. 

Lemma s_empty_wf_ok : forall V,
  includedin (s2state V s_empty) (empty) /\ 
  sym_state_wf V s_empty.
Proof.
  intros V. unfold s_empty. split.
  - intros x v. unfold s2state. simpl. intros. discriminate.
  - unfold sym_state_wf. simpl. split; auto. intros. discriminate.
Qed.

Lemma sym_gen_fresh_sound : forall V st ss Q v,
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss -> 
  sym_gen_fresh ss Q -> 
  exists V' ss' t, 
    includedin (s2state V' ss') (st) /\ 
    sym_state_wf V' ss' /\ 
    V' t = Some v /\ 
    Q ss' t.
Proof.
  intros V st ss Q v HM HWF HSE. 
  exists (fun va => if va =? (sym_used ss) then Some v else V va), 
  {| sym_store := sym_store ss; sym_cond := sym_cond ss; sym_used := S (sym_used ss) |},
  (sym_used ss). split; intuition. 
  - unfold s2state in *. simpl. unfold includedin in *. 
    intros x' v'. admit.
  - admit.
  - bdestruct (sym_used ss =? (sym_used ss)); auto.  
    exfalso. apply H. reflexivity.
Admitted.

Theorem sverify_sound : forall arg pre body st, 
  sverify arg pre body -> 
  beval st pre = Some true -> 
  exists st', st =[ body ]=> st'.
Proof.
  intros arg pre body st HSV HPRE.
  unfold sverify in HSV. 
  eapply sym_gen_fresh_sound in HSV.
  2, 3: apply s_empty_wf_ok.
  destruct HSV as (V' & ss' & t & HM & HWF & HV & HSB). 
  eapply sbeval_sound in HSB.
  + destruct HSB as (tb & v & ss'' & HB & HM' & HWF' & HTB & HEXEC).
    eapply sexec_sound in HEXEC. destruct HEXEC as (st' & V'' & ss''' & HBODY & 
    HM'' & HWF'' & _). exists st'. eauto.
    unfold sym_cond_add. unfold s2state. simpl. apply HM'.
    apply sym_cond_add_wf; auto. admit.
Admitted.
  (* + apply sym_store_add_ok; eauto. *)
  (* + eapply sym_store_add_wf; eauto.  *)

End SVL.
