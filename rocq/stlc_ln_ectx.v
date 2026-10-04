From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.

Require Import tactics.
Require Import env.

Module STLC_LN_ECTX.

Definition atom := nat.

Inductive ty : Type := 
  | TNat : ty
  | TFun : ty -> ty -> ty
.

Inductive tm : Type := 
  | tnum : nat -> tm
  | tvarF : atom -> tm
  | tvarB : nat -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
  | tplus : tm -> tm -> tm
.

Fixpoint open' (k : nat) (u : tm) (t: tm) : tm := 
  match t with 
  | tnum n => tnum n
  | tvarF y => tvarF y
  | tvarB i => if i =? k then u else (tvarB i)
  | tapp t1 t2 => tapp (open' k u t1) (open' k u t2)
  | tabs t => tabs (open' (k + 1) u t)
  | tplus t1 t2 => tplus (open' k u t1) (open' k u t2)
  end 
.

Definition open t u := open' 0 u t. 

Fixpoint close' (k: nat) (x: atom) (t: tm) : tm := 
  match t with 
  | tnum n => tnum n 
  | tvarF y => if x =? y then (tvarB k) else (tvarF y) 
  | tvarB i => tvarB i
  | tapp t1 t2 => tapp (close' k x t1) (close' k x t2)
  | tabs t => tabs (close' (k + 1) x t) 
  | tplus t1 t2 => tplus (close' k x t1) (close' k x t2)
  end 
.

Definition close t x := close' 0 x t. 

Inductive lc : tm -> Prop := 
  | lc_num : forall n, 
    lc (tnum n)

  | lc_var : forall x, 
    lc (tvarF x)

  | lc_app : forall t1 t2, 
    lc t1 -> 
    lc t2 -> 
    lc (tapp t1 t2) 

  | lc_abs : forall (L : list nat) t, 
    (forall x, ~In x L -> lc (open t (tvarF x))) -> 
    lc (tabs t) 
  
  | lc_plus : forall t1 t2,
    lc t1 -> 
    lc t2 -> 
    lc (tplus t1 t2)
.

Fixpoint lc_at (k : nat) (t : tm) : Prop := 
  match t with 
  | tnum n => True
  | tvarF x => True
  | tvarB i => i < k
  | tapp t1 t2 => lc_at k t1 /\ lc_at k t2
  | tabs t => lc_at (k + 1) t
  | tplus t1 t2 => lc_at k t1 /\ lc_at k t2 
  end 
.

#[global] Hint Constructors lc: core.

Lemma bound : forall (l : list nat),
  exists n, (forall x, In x l -> x < n).
Proof.
  induction l.
  - exists 0. intros. destruct H.
  - destruct IHl as (n & IHl). exists (S (a + n)). intros x H.  
    destruct H; subst. lia. specialize (IHl x H). lia.
Qed. 

Lemma exists_not_in : forall (l : list nat), 
  exists v, ~ In v l. 
Proof.
  intros l. destruct (bound l) as (n & H). 
  exists n. intros HIn. specialize (H n HIn). lia.
Qed.

Lemma lc_at_open : forall k x t,
  lc_at k (open' k (tvarF x) t) <-> lc_at (k + 1) t.
Proof.
  intros k x t. split; generalize dependent k; 
  generalize dependent x; induction t; 
  intros x k H; simpl in *; eauto;
  try (destruct H; split; eauto).
  - destruct (n =? k) eqn:E; simpl in *.
    + apply Nat.eqb_eq in E. lia.
    + lia.
  - destruct (n =? k) eqn:E; simpl in *.
    + exact I.
    + apply Nat.eqb_neq in E. lia.    
Qed.

Fixpoint tm_size (t : tm) : nat :=  
  match t with 
  | tapp t1 t2 | tplus t1 t2 => 
    S (tm_size t1 + tm_size t2) 
  | tabs t => S (tm_size t)
  | _ => 1
  end 
.

Lemma tm_size_open : forall k x t,
  tm_size (open' k (tvarF x) t) = tm_size t.
Proof.
  intros k x t. generalize dependent x. generalize dependent k.
  induction t; intros k x; simpl in *; try reflexivity.
  - destruct (n =? k); reflexivity.
  - rewrite IHt1. rewrite IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1. rewrite IHt2. reflexivity.
Qed.   

Theorem lc_from_lc_at : forall t, lc t <-> lc_at 0 t.
Proof.
  intros t. split; intros H.
  - induction H; try exact I; try (split; assumption).
    destruct (exists_not_in L) as (n, HF). 
    specialize (H0 n HF). apply lc_at_open in H0. 
    assumption.
  - induction t using
    (well_founded_induction (well_founded_ltof tm tm_size)).
    rename H0 into IH. destruct t; simpl in *; try lia; eauto. 
    + destruct H. constructor; apply IH; unfold ltof; 
      simpl; try lia; assumption. 
    + apply lc_abs with (L := []). intros x HF. apply IH. 
      * unfold ltof, open. rewrite tm_size_open. simpl. lia.
      * unfold open. apply lc_at_open. assumption.
    + destruct H. constructor; apply IH; unfold ltof; 
      simpl; try lia; assumption. 
Qed.

Inductive value : tm -> Prop := 
  | v_num : forall n, 
    value (tnum n)

  | v_abs : forall t, 
    value (tabs t)
.

Inductive ectx : (tm -> tm) -> Prop := 
  | ctx_appl : forall t2,
    ectx (fun t1 => tapp t1 t2) 

  | ctx_appr : forall v, 
    value v -> 
    ectx (fun t2 => tapp v t2) 

  | ctx_addl : forall t2,  
    ectx (fun t1 => tplus t1 t2)

  | ctx_addr : forall v, 
    value v -> 
    ectx (fun t2 => tplus v t2) 
.

Inductive step : tm -> tm -> Prop := 
  | step_beta : forall t v,
    value v -> 
    step (tapp (tabs t) v) (open t v)

  | step_add : forall n1 n2,
    step (tplus (tnum n1) (tnum n2)) (tnum (n1 + n2))

  | step_ectx : forall t t' K, 
    ectx K -> 
    step t t' -> 
    step (K t) (K t') 
.

Definition tenv := list ty.

Fixpoint closed t x :=
  match t with
  | tnum _ => True
  | tvarF y => y < x
  | tvarB i => True
  | tapp t1 t2 => closed t1 x /\ closed t2 x
  | tabs t => closed t x
  | tplus t1 t2 => closed t1 x /\ closed t2 x
  end.

Inductive has_type : tenv -> tm -> ty -> Prop := 
  | t_num : forall env n, 
    has_type env (tnum n) TNat

  | t_varF : forall x env T,
    indexl x env = Some T -> 
    has_type env (tvarF x) T

  | t_app : forall env f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2

  | t_abs : forall env t T1 T2,
    has_type (env ++ [T1]) (open t (tvarF (length env))) T2 -> 
    closed t (length env) -> 
    has_type env (tabs t) (TFun T1 T2)
    
  | t_plus : forall env t1 t2, 
    has_type env t1 (TNat) -> 
    has_type env t2 (TNat) -> 
    has_type env (tplus t1 t2) TNat
.

#[global] Hint Unfold tenv : core. 
#[export] Hint Constructors ectx: core.
#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors value: core.
#[export] Hint Unfold open : core.

#[export] Hint Constructors has_type: core.
#[export] Hint Constructors step: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.

Lemma canonical_forms_nat : forall env v, 
  value v -> 
  has_type env v TNat -> 
  exists n, v = tnum n.
Proof.
  intros env v HV HT. inversion HV. exists n. reflexivity.   
  subst. inversion HT.
Qed.

Lemma canonical_forms_fun : forall env v T1 T2,
  value v -> 
  has_type env v (TFun T1 T2) -> 
  exists t, v = tabs t. 
Proof.
  intros env v T1 T2 HV HT. inversion HV; subst. 
  inversion HT. exists t. reflexivity.
Qed.

Theorem progress : forall t T, 
  has_type [] t T -> 
  value t \/ exists t', step t t'.
Proof.
  intros t T H. remember [] as env. induction H; auto.
  - subst. destruct x; simpl in *; inversion H.
  - right. destruct (IHhas_type1 Heqenv); 
    destruct (IHhas_type2 Heqenv).
    + pose proof (canonical_forms_fun _ _ _ _ H1 H).  
      destruct H3 as (t' & HV). subst. exists (open t' t). 
      auto.
    + destruct H2 as (t' & HS). exists (tapp f t'). auto.
    + destruct H1 as (f' & HF). exists (tapp f' t). 
      apply (step_ectx f f' (fun t1 => tapp t1 t)); auto.  
    + destruct H1 as (f' & HF). exists (tapp f' t).
      apply (step_ectx f f' (fun t1 => tapp t1 t)); auto.
  - right. destruct (IHhas_type1 Heqenv); 
    destruct (IHhas_type2 Heqenv).
    + pose proof (canonical_forms_nat _ _ H1 H).
      pose proof (canonical_forms_nat _ _ H2 H0).
      destruct H3. destruct H4. subst. 
      exists (tnum (x + x0)). auto.
    + destruct H2 as (t' & HS). exists (tplus t1 t'). auto.
    + destruct H1 as (t' & HS). exists (tplus t' t2).
      apply (step_ectx t1 t' (fun t1 => tplus t1 t2)); auto.
    + destruct H1 as (t' & HS). exists (tplus t' t2).
      apply (step_ectx t1 t' (fun t1 => tplus t1 t2)); auto.
Qed.

Fixpoint subst (x : atom) (u : tm) (t : tm) : tm := 
  match t with 
  | tnum n => tnum n
  | tvarF y => if (x =? y) then u else (tvarF y)
  | tvarB i => tvarB i 
  | tapp t1 t2 => tapp (subst x u t1) (subst x u t2)
  | tabs t => tabs (subst x u t)
  | tplus t1 t2 => tplus (subst x u t1) (subst x u t2)
  end 
.

Lemma subst_intro : forall x k u t, 
  closed t x -> 
  open' k u t = subst x u (open' k (tvarF x) t). 
Proof.
  intros x k u t. generalize dependent u. generalize dependent k.
  generalize dependent x. induction t; intros x k u HC; unfold open;
  simpl in *; try reflexivity.
  - assert (x <> a) by lia. apply Nat.eqb_neq in H.
    rewrite H. reflexivity.
  - destruct (eqb_spec n k); subst; simpl in *. 
    rewrite Nat.eqb_refl. 1, 2: reflexivity.
  - destruct HC. f_equal; eauto.
  - f_equal; eauto.
  - destruct HC. f_equal; eauto.
Qed.    

Lemma closed_extends : forall n1 n2 t,
  n1 <= n2 -> 
  closed t n1 -> 
  closed t n2. 
Proof.
  intros n1 n2 t HN HC. induction t; simpl in *; eauto;
  try (destruct HC; split; eauto). lia.
Qed. 

Lemma typing_closed : forall env t T,
  has_type env t T -> closed t (length env).
Proof.
  intros env t T H. induction H; simpl in *; try auto.
  eapply indexl_var_some'. eassumption.
Qed.

Lemma typing_lc : forall env t T, 
  has_type env t T -> lc t.
Proof.
  intros env t T H. induction H; eauto.
  apply lc_from_lc_at. simpl.
  apply (lc_at_open 0 (length env) t). 
  apply lc_from_lc_at. assumption.   
Qed.

Fixpoint rename (rho : nat -> nat) (t : tm) : tm :=
  match t with
  | tnum n => tnum n
  | tvarF x => tvarF (rho x)
  | tvarB i => tvarB i
  | tapp t1 t2 => tapp (rename rho t1) (rename rho t2)
  | tabs t => tabs (rename rho t)
  | tplus t1 t2 => tplus (rename rho t1) (rename rho t2)
  end.

Lemma rename_closed : forall t n m rho,
  closed t n ->
  (forall x, x < n -> rho x < m) ->
  closed (rename rho t) m.
Proof.
  induction t; intros n0 m rho HC HR; simpl in *; eauto;
  destruct HC; split; eauto.
Qed.

Lemma rename_open : forall t k n m rho,
  closed t n ->
  rename (fun x => if x =? n then m else rho x) (open' k (tvarF n) t) =
  open' k (tvarF m) (rename rho t).
Proof.
  induction t; intros k n0 m rho HC; simpl in *; try reflexivity.
  - assert ((a =? n0) = false). apply Nat.eqb_neq. lia. rewrite H.
    reflexivity.
  - destruct (n =? k); simpl; auto. rewrite Nat.eqb_refl. reflexivity.
  - destruct HC. f_equal; eauto.
  - f_equal; eauto.
  - destruct HC. f_equal; eauto.
Qed.

Lemma typing_rename : forall env1 env2 t T rho, 
  has_type env1 t T -> 
  (forall x U, indexl x env1 = Some U -> indexl (rho x) env2 = Some U) -> 
  has_type env2 (rename rho t) T.
Proof.
  intros env1 env2 t T rho HT. generalize dependent rho.
  generalize dependent env2. induction HT; intros env2 rho HR; 
  simpl; eauto. constructor.
  - unfold open. rewrite <- (rename_open t 0 (length env) (length env2) rho H).
    apply IHHT. intros x U HX. bdestruct (x =? length env).
    + subst. rewrite indexl_insert in HX. inversion HX; subst U.
      apply indexl_insert.
    + assert (x < length (env ++ [T1])) by (eapply indexl_var_some'; eassumption).
      rewrite length_app in H1. simpl in H1.
      rewrite indexl_skips in HX by lia. apply indexl_extend. auto.
  - eapply rename_closed; eauto. intros x HX.
    destruct (proj2 (indexl_var_some) HX). eapply indexl_var_some'. eauto.
Qed.

Lemma rename_id : forall t, rename (fun x => x) t = t.
Proof. 
  induction t; simpl; congruence. 
Qed.

Lemma weakening_append : forall G extra t T,
  has_type G t T -> has_type (G ++ extra) t T.
Proof.
  intros G extra t T HT. rewrite <- (rename_id t).
  eapply typing_rename; eauto. intros x U HX. 
  apply indexl_extend. exact HX.
Qed.

Fixpoint subst_remove (x : nat) (u t : tm) : tm :=
  match t with
  | tnum n => tnum n
  | tvarF y =>
      if y =? x then u
      else tvarF (if y <? x then y else pred y)
  | tvarB i => tvarB i
  | tapp t1 t2 => tapp (subst_remove x u t1) (subst_remove x u t2)
  | tabs t => tabs (subst_remove x u t)
  | tplus t1 t2 => tplus (subst_remove x u t1) (subst_remove x u t2)
  end.

Lemma open_above : forall t n k u,
  lc_at n t -> n <= k -> open' k u t = t.
Proof.
  induction t; intros n0 k u H Hle; simpl in *; try reflexivity.
  - bdestruct (n =? k); auto. lia.
  - destruct H. f_equal; eauto.
  - f_equal. eapply IHt; eauto. lia.
  - destruct H. f_equal; eauto.
Qed.

Lemma subst_remove_closed : forall t n m u,
  closed t (S m) -> n <= m -> closed u m ->
  closed (subst_remove n u t) m.
Proof.
  induction t; intros n0 m u HC Hnm HU; simpl in *; eauto.
  - bdestruct (a =? n0); auto.
    bdestruct (a <? n0); simpl; lia.
  - destruct HC. split; eauto.
  - destruct HC. split; eauto.
Qed.

Lemma subst_remove_open : forall t k n m u,
  lc u -> n <= m ->
  subst_remove n u (open' k (tvarF (S m)) t) =
  open' k (tvarF m) (subst_remove n u t).
Proof.
  induction t; intros k n0 m u HU Hnm; simpl; try reflexivity;
  try f_equal; eauto.
  - bdestruct (a =? n0); simpl.
    + symmetry. eapply open_above with (n := 0); try lia.
      apply lc_from_lc_at. assumption.
    + reflexivity.
  - bdestruct (n =? k); simpl; auto. 
    change ((if S m =? n0 then u
      else tvarF (if S m <? n0 then S m else m)) = tvarF m).
    assert ((S m =? n0) = false) by (apply Nat.eqb_neq; lia).
    assert ((S m <? n0) = false) by (apply Nat.ltb_ge; lia).
    rewrite H0, H1. reflexivity.
Qed.

Lemma substitution_remove : forall env1 env2 t u T U,
  has_type (env1 ++ [U] ++ env2) t T -> 
  has_type env1 u U -> 
  has_type (env1 ++ env2) (subst_remove (length env1) u t) T. 
Proof.
  intros env1 env2 t u T U HT. remember (env1 ++ [U] ++ env2) as G.
  generalize dependent U. generalize dependent u. generalize dependent env2.
  generalize dependent env1. induction HT; intros env1 env2 u U HG HU; subst; 
  simpl in *; eauto.
  - bdestruct (x =? length env1). 
    + subst. rewrite indexl_insert in H. inversion H. 
      subst. apply weakening_append. assumption.
    + constructor. bdestruct (x <? length env1).
      * rewrite indexl_left with (l2 := [U]); assumption.
      * rewrite indexl_remove_above with (y := U). assumption. lia.
  - constructor. 
    + unfold open. rewrite <- subst_remove_open.
      2: eapply typing_lc; exact HU. 2: rewrite length_app; lia.
      replace (S (length (env1 ++ env2))) with 
      (length (env1 ++ [U] ++ env2)) by (repeat rewrite length_app; simpl; lia).
      replace ((env1 ++ env2) ++ [T1]) with (env1 ++ (env2 ++ [T1])) 
      by (rewrite app_assoc; auto). eapply IHHT; eauto.
      repeat rewrite <- app_assoc. reflexivity.
    + eapply subst_remove_closed. 
      * replace (S (length (env1 ++ env2))) with (length (env1 ++ [U] ++ env2)) 
        by (repeat rewrite length_app; simpl; lia). assumption.
      * rewrite length_app. lia.
      * eapply closed_extends. 2: eapply typing_closed; eassumption.
        rewrite length_app. lia.
Qed.

Lemma subst_remove_zero : forall t u,
  closed t 1 -> subst_remove 0 u t = subst 0 u t.
Proof.
  induction t; intros u HC; simpl in *; try reflexivity.
  - assert (a = 0) by lia. subst a. reflexivity.
  - destruct HC. f_equal; eauto.
  - f_equal; eauto.
  - destruct HC. f_equal; eauto.
Qed.

Lemma substitution' : forall t u T U,
  has_type [U] t T -> 
  has_type [] u U -> 
  has_type [] (subst 0 u t) T. 
Proof.
  intros t u T U HT HU.
  pose proof (typing_closed _ _ _ HT) as HC.
  rewrite <- (subst_remove_zero t u HC).
  eapply (substitution_remove [] []); eauto.
Qed.

Lemma substitution : forall t u T U,
  closed t 0 -> 
  has_type [U] (open t (tvarF 0)) T -> 
  has_type [] u U -> 
  has_type [] (open t u) T.
Proof.
  intros t u T U HC HT HU. 
  apply subst_intro with (k := 0) (u := u) in HC.
  unfold open in *. rewrite HC. eapply substitution'; eauto.
Qed.

Theorem preservation : forall t t' T, 
  has_type [] t T -> 
  step t t' -> 
  has_type [] t' T.
Proof.
  intros t t' T HT. generalize dependent t'. remember [] as env. 
  induction HT; intros t' HS.
  - inversion HS. subst. inversion H0; subst; inversion H.
  - subst. destruct x; inversion H.
  - specialize (IHHT1 Heqenv). specialize (IHHT2 Heqenv). 
    inversion HS; subst. 
    + rename t0 into t'. inversion HT1; subst. simpl in *.  
      eapply substitution; eauto.
    + inversion H0; subst; try (injection H as H; subst; eauto); 
      inversion H.
  - inversion HS; subst. inversion H1; subst; inversion H0.
  - inversion HS; subst. eauto. inversion H0; subst; inversion H;
    subst; eauto.
Qed.           

End STLC_LN_ECTX.
