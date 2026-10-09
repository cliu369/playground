(*
Canonical STLC that is:
1. curry-style
2. call-by-value
3. binding with de Bruijn indices
4. semantics given by definitional interpreter w/fuel 

Note 4 typically uses environments and returns a closure,
this significantly simplifies the proof. 

Proves
1. Normalization with classic logicla relations technique. 
2. Semantic type soundness (en passant normalization)
*)

From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.

Require Import tactics.
Require Import env.

Module STLC.

Definition id := nat.

Inductive ty : Type := 
  | TUnit : ty 
  | TFun : ty -> ty -> ty
.

Inductive tm : Type := 
  | tunit : tm 
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
.

Inductive value : tm -> Prop := 
  | vunit : value tunit
  | vabs : forall t, value (tabs t)
.

Fixpoint shift (t: tm) (c: nat) (d: nat): tm := 
  match t with 
  | tunit => tunit
  | tvar n => if (c <=? n) then tvar (n + d) else tvar n 
  | tabs t => tabs (shift t (c + 1) d)
  | tapp t1 t2 => tapp (shift t1 c d) (shift t2 c d)
  end
.

(* t[j |-> s], e.g. substituting s for j in t *)
Fixpoint subst (t: tm) (j: nat) (s: tm)  : tm := 
  match t with 
  | tunit => tunit
  | tvar n => 
      if j =? n then s 
      else if j <? n then tvar (n - 1)
      else tvar n
  | tabs t => tabs (subst (t) (j + 1) (shift s 0 1))
  | tapp t1 t2 => tapp (subst t1 j s) (subst t2 j s)
  end
.

Fixpoint eval (n : nat) (t : tm) : option (option tm) := 
  match n with 
  | 0 => None 
  | S n => 
    match t with 
    | tunit => Some (Some tunit)
    | tvar _ => Some None
    | tabs y => Some (Some (tabs y))
    | tapp ef ex => 
      match eval n ef with
      | None => None
      | Some (Some (tabs ey)) => 
        match eval n ex with 
        | None => None 
        | Some None => Some None 
        | Some (Some vx) => eval n (subst ey 0 vx)
        end
      | _ => Some None 
      end
    end 
  end
.

Definition evaln e v := 
  exists nm, forall n, n > nm -> eval n e = Some (Some v)
.

Definition tenv := list ty. 

Inductive has_type : tenv -> tm -> ty -> Prop := 
  | t_unit : forall env,
    has_type env tunit TUnit
  | t_var : forall x env T,
    indexl x env = Some T -> 
    has_type env (tvar x) T
  | t_app : forall env f t T1 T2,
    has_type env f (TFun T1 T2) -> 
    has_type env t T1 -> 
    has_type env (tapp f t) T2
  | t_abs : forall env t T1 T2,
    has_type (T1 :: env) t T2 -> 
    has_type env (tabs t) (TFun T1 T2)
.

#[global] Hint Unfold tenv : core.
#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors value: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.

Lemma eval_val : forall n e v,
  eval n e = Some (Some v) -> value v.
Proof.
  induction n; intros e v HE. inversion HE. destruct e; inversion HE; eauto.
  destruct (eval n e1) as [[f | ] |]; try discriminate.
  destruct f; try discriminate. 
  destruct (eval n e2) as [[vx | ] |]; try discriminate.
  apply IHn in H0. assumption.    
Qed. 
  
Lemma evaln_value : forall e v,
  evaln e v -> value v. 
Proof.
  intros e v (n & HE). eapply eval_val with (n := S n). 
  eapply HE. lia.
Qed.

Lemma value_evaln : forall v,
  value v -> evaln v v.
Proof.
  exists 1. intros n Hn. destruct n. lia. 
  inversion H; reflexivity.
Qed.

Lemma weakening : forall env env' t T,
  has_type env t T -> 
  has_type (env ++ env') t T.
Proof.
  intros env env' t T H. generalize dependent env'. 
  induction H; intros env'; auto.
  - apply t_var. apply indexl_extend. assumption.
  - eapply t_app; eauto.
  - apply t_abs. apply IHhas_type.
Qed.   

Lemma shift_pre_ty_gen : forall t T c d env1 env2 env env',
  env1 ++ env2 = env -> 
  c = length env1 -> 
  d = length env' -> 
  has_type env t T -> 
  has_type (env1 ++ env' ++ env2) (shift t c d) T.
Proof.  
  induction t; intros T c d env1 env2 env env' HK HC HD HT; 
  inversion HT; simpl; try (econstructor; eauto).
  - subst. bdestruct ((length env1) <=? i).
    + constructor. rewrite <- indexl_mid; eauto.
    + constructor. rewrite <- indexl_left; eauto.
  - subst. replace (T1 :: env1 ++ env' ++ env2)
     with ((T1 :: env1) ++ env' ++ env2) by auto.  
    eapply IHt; eauto. simpl. lia.
Qed.

Lemma shift_pre_ty : forall env t T pre,
  has_type env t T -> 
  has_type (pre ++ env) (shift t 0 (length pre)) T.
Proof.  
  intros env t T pre HT.
  replace (pre ++ env) with ([] ++ pre ++ env) by auto.
  apply shift_pre_ty_gen with (env := env); eauto.
Qed.

Lemma substitution : forall env env' U t v T,
  has_type (env' ++ [U] ++ env) t T -> 
  has_type (env' ++ env) v U -> 
  has_type (env' ++ env) (subst t (length env') v) T.
Proof. 
  intros env env' U t. generalize dependent U. generalize
  dependent env'. generalize dependent env. induction t; 
  intros env env' U v T HT HU.
  - simpl. inversion HT. constructor.
  - inversion HT; subst. simpl. bdestruct (length env' =? i).
    + rewrite <- H in H1. 
      replace (env' ++ [U] ++ env) with (env' ++ U :: env) in H1 by reflexivity.
      rewrite indexl_insert in H1. inversion H1. subst. assumption.
    + bdestruct (length env' <? i).
      * clear H. rename H0 into H. apply t_var. 
        assert (length env' <= i - 1) by lia. 
        apply indexl_mid with (l2 := [U]) (l3 := env) in H0.
        rewrite H0. simpl. replace (i - 1 + 1) with (i) by lia.
        apply H1.  
      * assert (length env' > i) by lia. clear H H0. 
        apply indexl_left with (l2 := [U]) (l3 := env) in H2. 
        apply t_var. rewrite H2. apply H1. 
  - simpl. inversion HT; subst. econstructor; eauto. 
  - simpl. inversion HT; subst. apply t_abs. 
    replace (length env' + 1) with (length (T1 :: env')) by (simpl; lia).
    replace (T1 :: env' ++ env) with ((T1 :: env') ++ env) by auto.
    apply IHt with (U := U); auto. 
    replace ((T1 :: env') ++ env) with ([T1] ++ env' ++ env) by auto.
    apply shift_pre_ty. assumption.
Qed.  

Lemma substitution' : forall env U t v T, 
  has_type (U :: env) t T -> 
  has_type [] v U -> 
  has_type env (subst t 0 v) T.
Proof.
  intros env U t v T.
  replace (U :: env) with ([] ++ [U] ++ env) by auto. 
  intros H1 H2. replace env with ([] ++ env) by auto.
  eapply substitution. eauto. apply weakening.
  assumption.
Qed.

Theorem preservation : forall n t v T,
  has_type [] t T -> 
  eval n t = Some (Some v) -> 
  has_type [] v T.
Proof.
  induction n; intros t v T HT HE. simpl in *. discriminate. destruct t. 
  - inversion HT; subst. simpl in HE. inversion HE. constructor.
  - inversion HT; subst. destruct i; discriminate.
  - inversion HT; subst. simpl in HE. destruct (eval n t1) as [[fv |] |] eqn: HF; 
    try discriminate. destruct fv; try discriminate. 
    destruct (eval n t2) as [[av |] |] eqn: HV; try discriminate. 
    apply IHn with (v := (tabs fv)) in H2; auto.
    apply IHn with (v := av) in H4; auto. inversion H2. subst.
    apply substitution' with (v := av) in H3; eauto.
  - simpl in HE. inversion HE. assumption.
Qed.  

(* 
A multi-substitution is a list of terms, where 
the term at index i gets substituted for variable i.
*)
Definition msubs : Type := list tm.

(* 
Note: okay to subst t j v, since subst will decrement other indices 
      appropriately. 
*)
Fixpoint msubst (t : tm) (j : nat) (msub : msubs) : tm := 
  match msub with 
  | [] => t 
  | v :: rest => msubst (subst t j v) j rest
  end 
. 

(* 
t is closed under n binders. Top-level closed term is n = 0.
*)
Fixpoint closed (t : tm) (n : nat) : Prop :=
  match t with 
  | tunit => True 
  | tvar x => x < n 
  | tapp t1 t2 => closed t1 n /\ closed t2 n
  | tabs t => closed t (n + 1)
  end
.

Lemma closed_ext : forall t n1 n2,
  n1 <= n2 -> closed t n1 -> closed t n2.
Proof.
  induction t; intros n1 n2 HN HC; try reflexivity; simpl in *.
  - lia. 
  - destruct HC. split; eauto.
  - apply IHt with (n1 := (n1 + 1)). lia. assumption.
Qed.  

Lemma typing_closed : forall env t T, 
  has_type env t T -> closed t (length env).
Proof.
  intros env t T HT. induction HT.
  - exact I.
  - bdestruct (x <? length env). assumption. 
    apply indexl_var_none in H0. rewrite H in H0.
    discriminate.
  - simpl. split; assumption.
  - simpl. simpl in *. replace (length env + 1) with (S (length env)) by lia.    
    assumption.
Qed.

Lemma shift_closed : forall t c d,
  closed t c -> shift t c d = t.
Proof.
  induction t; intros c d HC; simpl in *; auto.
  - bdestruct (c <=? i); try lia. reflexivity.
  - destruct HC. f_equal; auto.
  - f_equal; auto.
Qed.

Lemma subst_closed : forall t n v,
  closed t n -> subst t n v = t.
Proof.
  induction t; intros n v HC.
  - reflexivity.
  - simpl in HC. simpl. 
    bdestruct (n =? i); try lia.
    bdestruct (n <? i); [lia | reflexivity].
  - simpl in *. destruct HC. f_equal; auto.
  - simpl in *. f_equal. auto.
Qed.  

Definition closed_msub (msub : msubs) : Prop := 
  Forall (fun v => closed v 0) msub.

Definition shift_msub (msub : msubs) (c : nat) (d : nat) : msubs := 
  map (fun v => shift v c d) msub.

Lemma shift_msub_closed : forall msub d,
  closed_msub msub -> 
  shift_msub msub 0 d = msub.
Proof.
  intros msub d HC. induction HC. reflexivity. simpl. rewrite IHHC.
  rewrite shift_closed; auto.
Qed.

Lemma subst_commute : forall t i j v w,
  i <= j -> 
  closed v 0 -> 
  closed w 0 -> 
  subst (subst t (S j) w) i v = subst (subst t i v) j w.
Proof.
  induction t; try rename i into k; intros i j v w HIJ HCV HCW; try reflexivity.
  - simpl. destruct k.
    + bdestruct (S j <? 0). try lia. simpl. bdestruct (i =? 0); subst.
      rewrite subst_closed. reflexivity. apply closed_ext with (n1 := 0); auto.
      simpl. bdestruct (j =? 0). subst. lia. reflexivity.
    + bdestruct (j =? k). 
      * bdestruct (i =? S k). lia. bdestruct (i <? S k). 
        simpl. replace (k - 0) with k by lia. bdestruct (j =? k).
        apply subst_closed. apply closed_ext with (n1 := 0); auto. lia.
        bdestruct (j <? k). lia. lia. simpl. 
        bdestruct (j =? S k). apply subst_closed. 
        apply closed_ext with (n1 := 0); auto. lia. lia.
      * simpl. replace (k - 0) with k by lia.  bdestruct (S j <? S k).
        bdestruct (i =? S k). lia. simpl. bdestruct (i =? k). lia.
        bdestruct (i <? k). bdestruct (i <? S k). simpl. 
        bdestruct (j =? k). lia. bdestruct (j <? k). reflexivity. lia.
        lia. lia. bdestruct (i =? S k). simpl. bdestruct (i =? S k). 
        symmetry. apply subst_closed. apply closed_ext with (n1 := 0). lia. auto.
        lia. simpl. bdestruct (i =? S k). lia. bdestruct (i <? S k). 
        replace (k - 0) with k by lia. simpl. bdestruct (j =? k). lia. 
        bdestruct (j <? k). lia. reflexivity. simpl.
        bdestruct (j =? S k). lia. bdestruct (j <? S k). lia. reflexivity.
  - simpl. rewrite IHt1; eauto. rewrite IHt2; eauto.
  - simpl. rewrite IHt. reflexivity. lia. rewrite shift_closed; auto.
    rewrite shift_closed; auto.
Qed.      

Lemma msubst_closed : forall t msub n,
  closed t n -> msubst t n msub = t.
Proof.
  intros t msub. generalize dependent t. induction msub; intros t n HC.
  - simpl. reflexivity.
  - simpl. rewrite subst_closed; auto. 
Qed.  

Lemma msubst_var: forall msub x v, 
  closed v 0 -> 
  indexl x msub = Some v -> 
  msubst (tvar x) 0 msub = v.
Proof.
  induction msub; intros x v HC HX. destruct x; discriminate.
  simpl in *. destruct x.
  - simpl in *. inversion HX. subst. apply msubst_closed. assumption.
  - bdestruct (0 <? S x). 2: lia. clear H. simpl. simpl in HX.
    replace (x - 0) with x by lia. eauto.
Qed.  

Lemma msubst_app : forall msub t1 t2 j,
  msubst (tapp t1 t2) j msub = tapp (msubst t1 j msub) (msubst t2 j msub).
Proof.
  induction msub; eauto.
Qed.

Lemma msubst_abs : forall msub t j,
  msubst (tabs t) j msub = tabs (msubst t (j + 1) (shift_msub msub 0 1)).
Proof.
  induction msub; eauto.
Qed.        

Lemma msubst_subst : forall msub t i v,
  closed v 0 -> 
  closed_msub msub -> 
  subst (msubst t (S i) msub) i v = msubst (subst t i v) i msub.
Proof.
  intros msub t i v HC HCM. revert t i v HC. induction HCM; intros t i v HC. 
  - simpl. reflexivity. 
  - simpl. rewrite IHHCM. rewrite subst_commute; eauto. apply HC. 
Qed.

Lemma closed_subst : forall t n j v,
  closed t (S n) ->
  j <= n ->
  closed v 0 ->
  closed (subst t j v) n.
Proof. 
  induction t; intros n j v HC HJN HV.
  - exact I.
  - simpl in *. bdestruct (j =? i). eapply closed_ext with (n1 := 0); try lia. 
    eassumption. bdestruct (j <? i); simpl; lia. 
  - destruct HC. split. apply IHt1; eauto. apply IHt2; eauto.
  - simpl. apply IHt; eauto. lia. rewrite shift_closed; assumption.
Qed.    

Lemma closed_msubs : forall t msub n,  
  closed_msub msub -> 
  closed t (length msub + n) -> 
  closed (msubst t n msub) n.
Proof.
  intros t msub n HM. revert t n. induction HM; intros t n HC.
  - simpl in *. apply HC.
  - simpl in *. apply IHHM. apply closed_subst; eauto. lia.
Qed.

(* Logical Relations for SN *)

Fixpoint SN (T : ty) (e : tm) : Prop := 
  match T with 
  | TUnit => has_type [] e T /\ exists v, evaln e v 
  | TFun T1 T2 =>
     has_type [] e (TFun T1 T2) /\ 
     (exists v, evaln e v) /\ 
     (forall e', SN T1 e' -> SN T2 (tapp e e'))
  end 
.

Lemma SN_evaln : forall T e, 
  SN T e -> exists v, evaln e v.
Proof.
  intros T e HS. destruct T; inversion HS; tauto.
Qed.

Lemma SN_closed : forall T v,
  SN T v -> closed v 0.
Proof.
  intros T v HS. destruct T; inversion HS;
  eapply typing_closed with (env := []); eassumption.
Qed.

Lemma SN_typing : forall T v,
  SN T v -> has_type [] v T.
Proof.
  intros T v HS. destruct T; inversion HS; eauto.
Qed.

Lemma SN_eval : forall T e1 e2,
  SN T e1 -> 
  has_type [] e2 T -> 
  (exists n, forall nm, nm > n -> eval nm e1 = eval nm e2) -> 
  SN T e2. 
Proof.
  induction T; intros e1 e2 HS1 HT2 HEQ;
  assert (exists v, evaln e2 v) by
  (destruct (SN_evaln _ _ HS1) as (v & n & HE1); destruct HEQ as (n' & HEQ);
    exists v, (n + n'); intros n'' HN''; specialize (HEQ n''); assert 
    (n'' > n') by lia; apply HEQ in H; rewrite <- H; 
    specialize (HE1 n''); assert (n'' > n) by lia; apply HE1 in H0; assumption).
  - split; assumption.
  - split; try split; try assumption. intros e' HE'. 
    destruct HS1 as (H1 & H2 & H3). pose proof (SN_typing _ _ HE'). 
    apply H3 in HE'. apply IHT2 with (e1 := tapp e1 e'). assumption. 
    econstructor; eauto. destruct HEQ as (n & HEQ). exists (S n).
    intros nm HNM. destruct nm; try lia. simpl.
    assert (nm > n) by lia. apply HEQ in H4. rewrite H4. reflexivity.
Qed.

Lemma SN_preservation : forall T e v,
  SN T e -> 
  evaln e v -> 
  SN T v.
Proof.
  intros T e v HS (n & HE). apply SN_eval with (e1 := e); eauto. 
  - apply SN_typing in HS. specialize (HE (S n)). assert (S n > n) by lia. 
    eapply preservation; eauto.
  - exists n. intros nm HNM. specialize (HE _ HNM). 
    pose proof (eval_val _ _ _ HE). destruct nm; try lia. rewrite HE.
    inversion H; reflexivity.
Qed.

(* 
This is equivalent to env_type in the semantic type soundness
proof of stlc with a definitional interpreter that uses environments.
There, msub = run-time environment instead of a multi-substitution.
*)
Definition models (msub : msubs) (env : tenv) : Prop := 
  length msub = length env /\ 
  forall x T, indexl x env = Some T -> 
    exists v, 
      indexl x msub = Some v /\ SN T v
. 

Lemma models_shrink : forall msub env v T,
  models (v :: msub) (T :: env) -> 
  models msub env.
Proof.
  intros msub env v T (HL & HM). split.
  - simpl in HL. lia.
  - intros x U HX. specialize (HM (S x) U).
    simpl in *. auto.
Qed.  

Lemma models_ext : forall msub env v T,
  models msub env -> 
  SN T v -> 
  models (v :: msub) (T :: env).
Proof.
  intros msub env v T (HL & HM) HS. split. simpl. lia.
  intros x T' HX. destruct x; simpl in *.
  + inversion HX. subst. exists v. split; eauto.
  + apply HM in HX. destruct HX as (v' & HV'). exists v'. assumption.
Qed.  

Lemma models_closed : forall msub env, 
  models msub env -> 
  closed_msub msub.
Proof.
  induction msub; intros env HM. constructor. destruct env. 
  inversion HM. inversion H. constructor. 
  + destruct HM. destruct (H0 0 t Logic.eq_refl) as (v & HV1 & HVS).
    simpl in HV1. inversion HV1. subst. eapply SN_closed. eassumption. 
  + eapply IHmsub; eapply models_shrink; eassumption.
Qed.  

Lemma msubstitution : forall pre env t T msub,
  has_type (pre ++ env) t T -> 
  models msub env -> 
  has_type pre (msubst t (length pre) (shift_msub msub 0 (length pre))) T.
Proof.
  intros pre env. revert pre. induction env; intros pre t T msub HT HM.
  - simpl in *. destruct HM as (HL & HM). apply length_zero_iff_nil in HL.
    subst. simpl. rewrite app_nil_r in HT. assumption.
  - rename a into U. assert (models msub (U :: env)) as D. { assumption. }
    destruct D as (HL & HH). destruct msub; try discriminate.
    destruct (HH 0 U Logic.eq_refl) as (v & HV' & HV). simpl in HV'. 
    inversion HV'. subst. simpl. clear HH HV' HL.
    pose proof (SN_typing _ _ HV) as HVT. 
    pose proof (shift_pre_ty _ _ _ pre HVT). rewrite app_nil_r in H.
    apply IHenv. 2: apply models_shrink in HM; auto. 
    apply substitution with (U := U). 
    replace ([U] ++ env) with (U :: env) by auto. assumption.
    apply weakening. auto. 
Qed.

Theorem typing_SN : forall env t T msub, 
  has_type env t T -> 
  models msub env -> 
  SN T (msubst t 0 msub).
Proof.
  intros env t T msub HT. generalize dependent msub. induction HT; intros msub HM.
  - destruct HM as (HL & HM). rewrite msubst_closed. 2: exact I. split. auto. 
    exists tunit. apply value_evaln; eauto.
  - destruct HM as (HL & HM). destruct (HM _ _ H) as (t & Ht & Hst).
    rewrite msubst_var with (v := t). assumption. 
    apply SN_closed in Hst. assumption. assumption.
  - rewrite msubst_app. specialize (IHHT1 _ HM). destruct IHHT1 as (HFT & HFV & HFF).
    specialize (IHHT2 _ HM). apply HFF in IHHT2. assumption.
  - rewrite msubst_abs. simpl. split. 2: split.
    + constructor. replace (T1 :: env) with ([T1] ++ env) in HT by auto.
      eapply msubstitution in HT; eauto.
    + exists (tabs (msubst t 1 (shift_msub msub 0 1))). 
      apply value_evaln; auto. 
    + intros e' HSE'. destruct (SN_evaln _ _ HSE') as (v & HV). 
      pose proof (SN_preservation _ _ _ HSE' HV). 
      assert (models (v :: msub) (T1 :: env)) by (eapply models_ext; eauto). 
      specialize (IHHT (v :: msub) H0). eapply SN_eval. eapply IHHT.
      pose proof (SN_typing _ _ HSE'). econstructor. 2: apply H1.   
      constructor. eapply msubstitution. apply HT. assumption.
      destruct (SN_evaln _ _ IHHT) as (v' & n' & HV'). 
      destruct HV as (n & HV). exists (S (n + n')). 
      intros nm HNM. remember (eval nm (msubst t 0 (v :: msub))) as K.
      destruct nm. lia. simpl.    
      assert (eval nm (tabs (msubst t 1 (shift_msub msub 0 1))) = 
        Some (Some (tabs (msubst t 1 (shift_msub msub 0 1))))).
      { destruct nm. lia. simpl. reflexivity. }
      rewrite H1. assert (nm > n) by lia. specialize (HV nm H2).
      rewrite HV. rewrite HeqK. apply models_closed in H0. inversion H0. subst.
      rewrite shift_msub_closed; auto. rewrite msubst_subst; auto.
      rewrite (HV' (S nm)) by lia. symmetry. apply HV'. lia.
Qed.

Theorem normalization : forall t T,
  has_type [] t T -> 
  exists v, evaln t v /\ value v.
Proof.
  intros t T HT. apply typing_SN with (msub := []) in HT. simpl in HT.
  - apply SN_evaln in HT. destruct HT as (v & HV). exists v. split. assumption.
    eapply evaln_value. eassumption.
  - split. reflexivity. intros x T' HX. destruct x; discriminate.
Qed.  
    
(* Semantic Type Soundness *)

(* 
Note that val_type is meant to be the set of closed semantic values. 
Since tunit is already closed, to enforce this we can just put a closedness
condition in the tabs case.
*)
Fixpoint val_type (v : tm) (T : ty) : Prop := 
  match v, T with 
  | tunit, TUnit => True 
  | tabs t, TFun T1 T2 => 
    closed t 1 /\
    forall vx, val_type vx T1 -> 
      exists vy, 
        evaln (subst t 0 vx) vy /\ val_type vy T2
  | _,_ => False
  end
.

Definition exp_type t T := 
  exists v, 
    evaln t v /\ val_type v T.

(*
This is the same as models, except we now use 
val_type instead of SN. 
*)
Definition env_type (msub : msubs) (env : tenv) := 
  length msub = length env /\ 
    forall x T,
      indexl x env = Some T -> 
      exists v,
        indexl x msub = Some v /\
        val_type v T.
      
Definition sem_type env t T :=
  closed t (length env) -> 
  forall msub,
    env_type msub env -> 
    exp_type (msubst t 0 msub) T.

Lemma val_type_value : forall t T,
  val_type t T -> value t. 
Proof.
  induction t; intros T HT; try (destruct T; contradiction); eauto.
Qed.

Lemma val_type_closed : forall t T,
  val_type t T -> closed t 0.
Proof.
  intros t T HVT. destruct t; destruct T; try contradiction. exact I.
  simpl in *. destruct HVT. assumption.
Qed. 

Lemma env_type_empty : env_type [] [].
Proof.
  split. reflexivity. intros x T HX. destruct x; discriminate.
Qed.

Lemma env_type_shrink : forall msub env v T,
  env_type (v :: msub) (T :: env) -> env_type msub env. 
Proof. 
  intros msub env v T (HL & HE). split. 
  - simpl in *. lia.
  - intros x U HX. specialize (HE (S x) U HX). auto.  
Qed.

Lemma env_type_ext : forall msub env v T,
  env_type msub env -> 
  val_type v T -> 
  env_type (v :: msub) (T :: env).
Proof.
  intros msub env v T (HL & HE). split. simpl in *. lia.
  intros x U HX. destruct x. 
  - simpl in *. inversion HX. subst. exists v. split; auto.
  - simpl in HX. apply HE in HX. destruct HX as (v' & HXV' & HV').
    exists v'. split; auto.
Qed.

Lemma env_type_closed : forall msub env,
  env_type msub env -> closed_msub msub.
Proof.
  induction msub; intros env HE.
  - destruct env; constructor.
  - destruct env. inversion HE. inversion H. rename t into U. 
    constructor. 
    + destruct HE as (_ & HE). destruct (HE 0 U Logic.eq_refl) as (v & HV & HVT).
      inversion HV. eapply val_type_closed. eassumption.
    + eapply IHmsub. apply env_type_shrink in HE. eassumption.
Qed.  

Lemma sem_unit : forall env,  
  sem_type env tunit TUnit.
Proof.
  intros env msub HET. rewrite msubst_closed. 2: exact I. exists tunit. split.
  - apply value_evaln. constructor.
  - exact I.
Qed.

Lemma sem_var : forall env x T,
  indexl x env = Some T -> 
  sem_type env (tvar x) T.
Proof.
  intros env x T HX HC msub HET. destruct HET as (_ & HET). apply HET in HX.
  destruct HX as (v & HV & HVT). rewrite msubst_var with (v := v). 3: assumption.
  exists v. split. apply val_type_value in HVT. apply value_evaln. assumption.
  assumption. eapply val_type_closed. eassumption.
Qed.

Lemma sem_app : forall env f t T1 T2,
  sem_type env f (TFun T1 T2) -> 
  sem_type env t T1 -> 
  sem_type env (tapp f t) T2.
Proof.
  intros env f t T1 T2 HSF HST HC msub HE. destruct HC as (HCF & HCT).
  destruct (HSF HCF _ HE) as (vf & (nf & HEF) & HVF).
  destruct (HST HCT _ HE) as (vt & (nt & HET) & HVT). rewrite msubst_app.
  destruct vf; try contradiction. destruct HVF as (HVFC & HEVF). 
  apply HEVF in HVT. destruct HVT as (vy & (ny & HEVY) & HTVY). exists vy. split.
  2: assumption. exists (S (nf + nt + ny)). intros n Hn. destruct n; try lia.
  simpl. rewrite HEF by lia. rewrite HET by lia. rewrite HEVY by lia. reflexivity. 
Qed.

Lemma sem_abs : forall env t T1 T2, 
  sem_type (T1 :: env) t T2 -> 
  sem_type env (tabs t) (TFun T1 T2).
Proof.
  intros env t T1 T2 HS HC msub HE. rewrite msubst_abs. simpl in *. 
  rewrite shift_msub_closed.  2: eapply env_type_closed; eassumption.
  exists (tabs ((msubst t 1 msub))). split; try split. 
  - exists 0. intros n Hn. destruct n; try lia. reflexivity.
  - apply closed_msubs. eapply env_type_closed. eassumption.  
    destruct HE as (HL & _). rewrite HL. assumption.
  - intros vx HVX. replace (length env + 1) with (S (length env)) in HC by lia.
    apply HS in HC. assert (env_type (vx :: msub) (T1 :: env)).
    { apply env_type_ext; auto. } apply HC in H. destruct H as (vy & HEVY & HVEY).
    exists vy. split. 2: assumption. rewrite msubst_subst. apply HEVY. 
    eapply val_type_closed. eassumption. eapply env_type_closed. apply HE.
Qed.

Theorem fundamental : forall env t T,
  has_type env t T -> 
  sem_type env t T. 
Proof.
  intros env t T HT. induction HT.
  - eapply sem_unit.
  - eapply sem_var. assumption.
  - eapply sem_app; eauto.
  - eapply sem_abs; eauto.
Qed.

Corollary safety : forall t T,
  has_type [] t T -> 
  exp_type t T.
Proof.
  intros t T HT. pose proof (typing_closed _ _ _ HT). apply fundamental in HT.
  specialize (HT H [] env_type_empty). assumption.
Qed.

Corollary normalization' : forall t T,
  has_type [] t T -> 
  exists v, evaln t v /\ value v.
Proof.
  intros t T HT. apply safety in HT. destruct HT as (v & HE & HV).
  exists v. split; auto. eapply val_type_value. eassumption.
Qed. 

End STLC.