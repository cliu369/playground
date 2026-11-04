(*
Gradual verification based on 
1. Big-step dynamic semantics 
2. Big-step symbolic execution semantics + symbolic execution will 
   insert run-time checks into the program. 
*)

From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Classes.EquivDec.

Require Import maps.
Require Import tactics.
Require Import helper.

Module GVL. 

Instance string_eqdec : EqDec string Logic.eq := string_dec.

Definition state := partial_map string nat. 

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              
  | APlus (a1 a2 : aexp)
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
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Inductive result : Type := 
  | RNormal : state -> result
  | RError : result
.

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
  | RtCheck : bexp -> com
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

(*
Judgement st =[ c ]=> r means
executing program statement c in state st yields result r. 

The result r is either
- another state
- a special runtime check error 

Semantics of assert: 
b evaluates to true 
-----------------
st  =[ assert b ]=> st

Semantics of runtime check:
b evaluates to true
-------------------
st =[ rtcheck b ]=> st

b evaluates to false
-------------------
st =[rtcheck b] => runtime check error
*)
Inductive ceval : com -> state -> result -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a n x,
      aeval st a = Some n ->
      st =[ x := a ]=> RNormal (x |-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st'  ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st  =[ c1 ]=> RError -> 
      st  =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = Some true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = Some false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end]=> r
  | E_Assert : forall st b,
      beval st b = Some true -> 
      st =[ assert b ]=> RNormal st
  | E_RtCheckTrue : forall st b, 
      beval st b = Some true -> 
      st =[ RtCheck b ]=> RNormal st
  | E_RtCheckFalse : forall st b,
      beval st b = Some false -> 
      st =[ RtCheck b ]=> RError

where "st =[ c ]=> st'" := (ceval c st st').

Fixpoint wf (c: com) : bool := 
  match c with 
  | RtCheck _  => false
  | <{ c1; c2 }> => (wf c1) && (wf c2) 
  | <{ if b then c1 else c2 end }> => (wf c1) && (wf c2)
  | _ => true
  end.

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
  sym_used : nat; 
  is_imp : bool
}.

Definition sym_store_add (s: sym_state) (x: string) (a: sym_aexp) : sym_state := {|
  sym_store := (x |-> a; (sym_store s));
  sym_cond := sym_cond s;
  sym_used := sym_used s;
  is_imp := is_imp s 
|}.

Definition sym_cond_add (s: sym_state) (b: sym_bexp) : sym_state := {| 
  sym_store := sym_store s;
  sym_cond := SBinop b (sym_cond s) (andb);
  sym_used := sym_used s;
  is_imp := is_imp s
|}.

Definition sym_gen_fresh (s: sym_state) (Q: sym_state -> sym_val -> Prop) : Prop := 
  Q {| sym_store := sym_store s;
    sym_cond := sym_cond s;
    sym_used := S (sym_used s);
    is_imp := is_imp s
  |} (sym_used s).

Fixpoint saeval (s: sym_state) (a: aexp) : option sym_aexp := 
  match a with 
  | ANum n => Some (fun V => Some n)
  | AId x => sym_store s x
  | APlus a1 a2 => 
    do t1 <- saeval s a1;
    do t2 <- saeval s a2; 
    Some (SBinop t1 t2 Nat.add)
  | AMult a1 a2 => 
    do t1 <- saeval s a1;
    do t2 <- saeval s a2; 
    Some (SBinop t1 t2 Nat.mul)
  end
.

Fixpoint sbeval (s: sym_state) (b: bexp) : option sym_bexp := 
  match b with 
  | BTrue => Some (fun V => Some true)
  | BFalse => Some (fun V => Some false)
  | BEq a1 a2 => 
    do t1 <- saeval s a1;
    do t2 <- saeval s a2;
    Some (SBinop t1 t2 Nat.eqb)
  | BLe a1 a2 => 
    do t1 <- saeval s a1;
    do t2 <- saeval s a2; 
    Some (SBinop t1 t2 Nat.leb)
  | BNot b => 
    do t <- sbeval s b;
    Some (SUop t negb)
  | BAnd b1 b2 => 
    do t1 <- sbeval s b1; 
    do t2 <- sbeval s b2;
    Some (SBinop t1 t2 andb)
  end
. 

(* Fixpoint sexec (s: sym_state) (c: com) (K: sym_state -> com -> Prop) : Prop := 
  match c with 
  | <{ skip }> => K s <{ skip }>
  | <{ x := a }> => 
    match saeval s a with 
    | Some t => K (sym_store_add s x t) <{ x := a }>
    | None => False 
    end 
  | <{ c1 ; c2 }> => 
    sexec s c1 (fun s1 c1' => 
      sexec s1 c2 (fun s2 c2' => 
        K s2 <{ c1' ; c2' }>
      )
    )
  | <{ if b then c1 else c2 end }> => 
    match sbeval s b with 
    | Some t =>   
      (sexec (sym_cond_add s t) c1 K) /\ 
      (sexec (sym_cond add s (SUop t negb)) c2 K)
    | None => False
    end 
  | RtCheck _ => False
  | _ => True
  (* 
  | <{ if b then c1 else c2 end }> => 
    sbeval s b (fun s1 t => 
      (sexec (sym_cond_add s1 t) c1 K) /\
      (sexec (sym_cond_add s1 (SUop t negb)) c2 K)
    )
  | <{ assert b }> => 
    sbeval s b (fun s1 t => 
      sym_implies (sym_cond s) t /\ K s1
    ) *)
  end 
. *)

(* ss = merge_state ss1 ss2 if 
*)

Definition s2state (V: valuation) (s: sym_state) : state := 
  fun (x: string) => 
    do v <- (sym_store s) x; 
    v V
.

Definition sym_state_wf (V: valuation) (ss: sym_state): Prop :=
  (forall x t, (sym_store ss) x = Some t -> exists v, t V = Some v) /\ 
  ((sym_cond ss) V = Some true).

Definition merge_state (s s1 s2 : sym_state) : Prop := 
  forall st V, 
  (includedin (s2state V s1) st -> 
   sym_state_wf V s1 -> 
   includedin (s2state V s) st /\
   sym_state_wf V s) /\ 
  (includedin (s2state V s2) st -> 
   sym_state_wf V s2 -> 
   includedin (s2state V s) st /\
   sym_state_wf V s)
.

(* s, c -> s', c_rt *)
Inductive sexec : sym_state -> com -> sym_state -> com -> Prop :=
  | S_Skip : forall s ,  
    sexec s <{ skip }> s <{ skip }> 
  | S_Asgn : forall s x a t, 
    saeval s a = Some t ->
    sexec s <{ x := a }> (sym_store_add s x t) <{ x := a }> 
  | S_Seq : forall s s1 s2 c1 c2 c1' c2',
    sexec s c1 s1 c1' -> 
    sexec s1 c2 s2 c2' ->
    sexec s <{ c1 ; c2 }> s2 <{ c1' ; c2' }>
  | S_If : forall s b c1 c2 t s1 c1' s2 c2' s',
    sbeval s b = Some t -> 
    sexec (sym_cond_add s t) c1 s1 c1' -> 
    sexec (sym_cond_add s (SUop t negb)) c2 s2 c2' -> 
    merge_state s' s1 s2 -> 
    sexec s <{ if b then c1 else c2 end }> s' <{ if b then c1' else c2' end }>
  | S_AssertPre : forall s b t, 
    sbeval s b = Some t -> 
    sym_implies (sym_cond s) t -> 
    sexec s <{ assert b }> s <{ assert b }> 
  | S_AssertImp : forall s b t, 
    sbeval s b = Some t -> 
    is_imp s = true -> 
    ~ (sym_implies (sym_cond s) t) -> 
    sexec s <{ assert b }> s <{ RtCheck b; assert b }>     
. 

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

Theorem saeval_sound : forall a V st ss t,
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss -> 
  saeval ss a = Some t -> 
  exists v, t V = Some v /\ aeval st a = Some v.
Proof.
  induction a; intros V st ss t HM HWF HSE; simpl in *.  
  - exists n. injection HSE as HSE. subst. auto. 
  - eapply s2state_exists; eauto.    
  - destruct (saeval ss a1) eqn: Ha1; try discriminate.
    destruct (saeval ss a2) eqn: Ha2; try discriminate.
    simpl in HSE. rename s into t1, s0 into t2. 
    destruct (IHa1 V st ss t1 HM HWF Ha1) as (v1 & HV1 & HEV1).
    destruct (IHa2 V st ss t2 HM HWF Ha2) as (v2 & HV2 & HEV2).
    exists (v1 + v2). unfold SBinop in HSE. injection HSE as HSE.
    split.
    + subst. rewrite HV1. rewrite HV2. reflexivity.
    + rewrite HEV1. rewrite HEV2. reflexivity. 
  - destruct (saeval ss a1) eqn: Ha1; try discriminate.
    destruct (saeval ss a2) eqn: Ha2; try discriminate.
    simpl in HSE. rename s into t1, s0 into t2. 
    destruct (IHa1 V st ss t1 HM HWF Ha1) as (v1 & HV1 & HEV1).
    destruct (IHa2 V st ss t2 HM HWF Ha2) as (v2 & HV2 & HEV2).
    exists (v1 * v2). unfold SBinop in HSE. injection HSE as HSE.
    split.
    + subst. rewrite HV1. rewrite HV2. reflexivity.
    + rewrite HEV1. rewrite HEV2. reflexivity. 
Qed.

Theorem sbeval_sound : forall b V st ss t,
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss -> 
  sbeval ss b = Some t -> 
  exists v, t V = Some v /\ beval st b = Some v. 
Proof.
  induction b; intros V st ss t HM HWF HSE; simpl in *.
  - exists true. injection HSE as HSE. subst. auto.
  - exists false. injection HSE as HSE. subst. auto.
  - destruct (saeval ss a1) as [t1 | ] eqn: Ha1; try discriminate.
    destruct (saeval ss a2) as [t2 | ] eqn: Ha2; try discriminate.
    unfold SBinop in *. simpl in HSE. injection HSE as HSE.
    eapply saeval_sound in Ha1; eauto. eapply saeval_sound in Ha2; eauto.
    destruct Ha1 as (v1 & HV1 & HEV1). destruct Ha2 as (v2 & HV2 & HEV2).
    exists (v1 =? v2). subst. split.
    + rewrite HV1. rewrite HV2. reflexivity.
    + rewrite HEV1. rewrite HEV2. reflexivity.
  - destruct (saeval ss a1) as [t1 | ] eqn: Ha1; try discriminate.
    destruct (saeval ss a2) as [t2 | ] eqn: Ha2; try discriminate.
    unfold SBinop in *. simpl in HSE. injection HSE as HSE.
    eapply saeval_sound in Ha1; eauto. eapply saeval_sound in Ha2; eauto.
    destruct Ha1 as (v1 & HV1 & HEV1). destruct Ha2 as (v2 & HV2 & HEV2).
    exists (v1 <=? v2). subst. split.
    + rewrite HV1. rewrite HV2. reflexivity.
    + rewrite HEV1. rewrite HEV2. reflexivity.  
  - destruct (sbeval ss b) as [t1 | ] eqn: Ha1; try discriminate.
    unfold SUop in *. simpl in HSE. injection HSE as HSE.
    destruct (IHb V st ss t1 HM HWF Ha1) as (v1 & HV1 & HEV1).
    exists (negb v1). subst. split.
    + rewrite HV1. reflexivity. 
    + rewrite HEV1. reflexivity.
  - destruct (sbeval ss b1) as [t1 | ] eqn: Ha1; try discriminate.
    destruct (sbeval ss b2) as [t2 | ] eqn: Ha2; try discriminate.
    unfold SBinop in *. simpl in HSE. injection HSE as HSE.
    destruct (IHb1 V st ss t1 HM HWF Ha1) as (v1 & HV1 & HEV1).
    destruct (IHb2 V st ss t2 HM HWF Ha2) as (v2 & HV2 & HEV2).
    exists (andb v1 v2). subst. split.
    + rewrite HV1. rewrite HV2. reflexivity.
    + rewrite HEV1. rewrite HEV2. reflexivity.
Qed.

Theorem sexec_sound : forall C V ss ss' C' st,
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss ->  
  sexec ss C ss' C' ->  
  (exists st',
     st =[ C' ]=> RNormal st' /\
     includedin (s2state V ss') st' /\
     sym_state_wf V ss' 
  ) \/
  st =[ C' ]=> RError.
Proof.
  intros C V ss ss' C' st HM HWF HSE. generalize dependent V. 
  generalize dependent st. induction HSE; intros st V HM HWF.
  - left. eexists. intuition.
  - left. rename t0 into t. eapply saeval_sound in H; eauto.
    destruct H as (v & HV & HEV). exists (x |-> v ; st). intuition.
    apply sym_store_add_ok; auto. eapply sym_store_add_wf; eauto.
  - destruct (IHHSE1 st V HM HWF) as [H1 | H1]; clear IHHSE1. 
    2: right; apply E_SeqError; auto.
    destruct H1 as (st' & HE1 & HM1 & HWF1).
    destruct (IHHSE2 st' V HM1 HWF1).
    2: right; eapply E_SeqNormal; eauto.
    destruct H as (st'' & HE2 & HM2 & HWF2). left.
    exists st''. intuition. eapply E_SeqNormal; eauto.
  - rename t0 into t. eapply sbeval_sound in H; eauto.
    destruct H as (v & HV & HEV). destruct v.
    + assert (includedin (s2state V (sym_cond_add s t)) st) as HMT; auto.
      assert (sym_state_wf V (sym_cond_add s t)) as HWFT. 
      apply sym_cond_add_wf; auto. clear IHHSE2.
      destruct (IHHSE1 st V HMT HWFT).
      2: right; eapply E_IfTrue; auto.
      destruct H as (st' & HE' & HM' & HWF'). left. 
      destruct (H0 st' V) as (H & _). exists st'; intuition. 
    + assert (includedin (s2state V (sym_cond_add s (SUop t negb))) st) as HMT; auto.
      assert (sym_state_wf V (sym_cond_add s (SUop t negb))) as HWFT.
      apply sym_cond_add_wf; auto. unfold SUop. rewrite HV. reflexivity.
      clear IHHSE1. destruct (IHHSE2 st V HMT HWFT).
      2: right; eapply E_IfFalse; auto.
      destruct H as (st' & HE' & HM' & HWF'). left. 
      destruct (H0 st' V) as (_ & H).
      exists st'; intuition. 
  - rename t0 into t. left. exists st; intuition.
    apply E_Assert. eapply sbeval_sound in H; eauto.  
    destruct H as (v & HV & HEV). unfold sym_implies in H0.
    specialize (H0 V). destruct HWF as (_ & HWF). 
    specialize (H0 HWF). rewrite H0 in HV. injection HV as HV.
    subst. apply HEV.
  - rename t0 into t. eapply sbeval_sound in H; eauto. destruct H as (v & HV & HEV).
    destruct v. 2: right; auto.
    left. exists st. intuition. eapply E_SeqNormal; eauto.
Qed.

Theorem sexec_verify : forall C V ss ss' C' st, 
  includedin (s2state V ss) (st) -> 
  sym_state_wf V ss ->  
  sexec ss C ss' C' ->  
  (exists st', st =[ C' ]=> RNormal st' ) \/ st =[ C' ]=> RError.
Proof.
  intros C V ss ss' C' st HM HWF HSE.
  eapply sexec_sound in HM; eauto. destruct HM.
  - left. destruct H as (st' & HS & _ & _). exists st'. apply HS.
  - right. apply H.
Qed.   
