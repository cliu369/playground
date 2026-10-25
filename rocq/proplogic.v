From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.

Require Import tactics.

Module PropositionalLogic. 

Definition id := nat.

Inductive formula : Type := 
  | bot : formula 
  | var : id -> formula
  | imp : formula -> formula -> formula
  | lor : formula -> formula -> formula 
  | land : formula -> formula -> formula 
.

Definition lnot : formula -> formula := 
  fun phi => imp phi bot. 

Definition ctx := list formula.

(* Natural Deduction for Classical Propositional Logic *)
Inductive deduction : ctx -> formula -> Prop := 
  | Ax : forall G phi,  
    In phi G -> 
    deduction G phi
    
  | AndI : forall G phi phi',
    deduction G phi -> 
    deduction G phi' -> 
    deduction G (land phi phi') 
  | AndEL : forall G phi phi',
    deduction G (land phi phi') -> 
    deduction G phi 
  | AndER : forall G phi phi', 
    deduction G (land phi phi') -> 
    deduction G phi'
    
  | OrIL : forall G phi phi',
    deduction G phi -> 
    deduction G (lor phi phi')
  | OrIR : forall G phi phi',
    deduction G phi' -> 
    deduction G (lor phi phi')
  | OrE : forall G phi phi' rho,
    deduction (phi :: G) rho -> 
    deduction (phi' :: G) rho -> 
    deduction G (lor phi phi') -> 
    deduction G rho

  | ImpI : forall G phi phi', 
    deduction (phi :: G) phi' -> 
    deduction G (imp phi phi')
  | ImpE : forall G phi phi', 
    deduction G (imp phi phi') -> 
    deduction G phi -> 
    deduction G phi'

  | BotE : forall G phi,
    deduction G bot -> 
    deduction G phi
  | DNE : forall G phi,
    deduction G (imp (lnot (lnot phi)) phi)
.

Hint Constructors deduction : core.
Hint Resolve in_eq in_cons : core.

(* Semantics of Classical Propositional Logic *)
Notation "[ e ]" := (exist _ e _).

Definition domain : Type := { n : nat | n <= 1 }. 

Definition dmin : domain -> domain -> domain. 
Proof.
  refine (fun a b => 
    [ min (proj1_sig a) (proj1_sig b) ] 
  ). destruct a, b. destruct x, x0; simpl; lia.
Defined.
Arguments dmin /.

Definition dmax : domain -> domain -> domain.
Proof.
  refine (fun a b => 
    [ max (proj1_sig a) (proj1_sig b) ]
  ). destruct a, b. destruct x, x0; simpl; lia.
Defined. 
Arguments dmax /.

Definition dminus : domain -> domain -> domain. 
Proof.
  refine (fun a b => 
    [ (proj1_sig a) - (proj1_sig b) ]
  ). destruct a, b. destruct x, x0; simpl; lia. 
Defined.
Arguments dminus /.

Definition dtop : domain.
Proof.
   refine ([ 1 ]). lia.
Defined.
Arguments dtop /.

Definition dbot : domain.
Proof.
   refine ([ 0 ]). lia.
Defined. 
Arguments dbot /.

Definition valuation : Type := id -> domain.

Definition denotation : valuation -> formula -> domain. 
Proof.
  refine (fix f V phi : domain :=  
    match phi with 
    | var x => V x
    | bot => [ 0 ]
    | lor phi phi' => dmax (f V phi) (f V phi')
    | land phi phi' => dmin (f V phi) (f V phi')
    | imp phi phi' => dmax (dminus dtop (f V phi)) (f V phi')
    end
  ). lia.
Defined.

Definition satisfies (V : valuation) (phi : formula) := 
  proj1_sig (denotation V phi) = 1.
Arguments satisfies /.

Definition valid (phi : formula) := 
  forall (V : valuation), satisfies V phi. 

(** Soundness of Natural Deduction **)

Ltac desD t := 
  let n := fresh "n" in 
  let HN := fresh "HN" in 
  destruct t as [n HN]; 
  destruct n; simpl in *; subst; try lia.

Lemma dmin_top : forall (a b : domain),  
  min (proj1_sig a) (proj1_sig b) = 1 -> 
  proj1_sig a = 1 /\ proj1_sig b = 1.
Proof.
  intros a b H. desD a; desD b.
Qed.   

Lemma dmax_top : forall (a b : domain),
  max (proj1_sig a) (proj1_sig b) = 1 -> 
  proj1_sig a = 1 \/ proj1_sig b = 1. 
Proof.
  intros a b H. desD a; desD b.
Qed. 

Theorem soundness : forall G phi,
  deduction G phi -> 
  forall (V : valuation),
  (forall phi', In phi' G -> satisfies V phi') -> 
  satisfies V phi.
Proof.
  intros G phi H V HI. induction H; simpl in *.
  - auto.
  - rewrite (IHdeduction1 HI). rewrite (IHdeduction2 HI).
    reflexivity.
  - specialize (IHdeduction HI). 
    destruct (dmin_top _ _ IHdeduction). assumption.
  - specialize (IHdeduction HI). 
    destruct (dmin_top _ _ IHdeduction). assumption.
  - rewrite (IHdeduction HI). destruct (denotation V phi').
    destruct x; simpl; lia.
  - rewrite (IHdeduction HI). destruct (denotation V phi).
    destruct x; simpl; lia.
  - specialize (IHdeduction3 HI). 
    destruct (dmax_top _ _ IHdeduction3).
    + apply IHdeduction1. intros phi'' HP.
      destruct HP; subst; auto.
    + apply IHdeduction2. intros phi'' HP.
      destruct HP; subst; auto.
  - destruct (denotation V phi) eqn:E; 
    destruct (proj1_sig [x]) eqn:E2. rewrite <- E in E2. 
    + destruct (denotation V phi'). destruct x0; simpl; lia.
    + assert (proj1_sig (denotation V phi) = 1). { simpl in *.
      rewrite E. clear E. subst. inversion l; simpl; lia. }
      simpl. apply IHdeduction. intros phi'' HP. destruct HP;
      subst; auto. 
  - specialize (IHdeduction2 HI). specialize (IHdeduction1 HI).
    rewrite IHdeduction2 in IHdeduction1. simpl in IHdeduction1.
    assumption.
  - specialize (IHdeduction HI). discriminate.
  - destruct (denotation V phi). destruct x. reflexivity.
    inversion l; simpl; lia.
Qed. 

Theorem soundness' : forall phi, 
  deduction [] phi -> valid phi.
Proof.
  intros phi H V. apply soundness with (V := V) in H.
  assumption. intros. inversion H0.
Qed.

(** Completeness of Natural Deduction **)

Lemma dmax_bot : forall (a b : domain),
  max (proj1_sig a) (proj1_sig b) = 0 -> 
  proj1_sig a = 0 /\ proj1_sig b = 0.
Proof.
  intros a b. desD a. desD b.
Qed.

Lemma dmin_bot : forall (a b : domain),
  min (proj1_sig a) (proj1_sig b) = 0 -> 
  proj1_sig a = 0 \/ proj1_sig b = 0.
Proof.
  intros a b. desD a. desD b.
Qed. 

Fixpoint vars (phi : formula) : list id := 
  match phi with 
  | var x => [x]
  | bot => [] 
  | lor phi phi' => (vars phi) ++ (vars phi')
  | land phi phi' => (vars phi) ++ (vars phi')
  | imp phi phi' => (vars phi) ++ (vars phi')
  end 
.

Definition assign_ctx (V : valuation) (pvars : list id) : ctx :=
  map (fun x => 
    if proj1_sig (V x) =? 1 then var x else lnot (var x)
  ) pvars.

Ltac permuted := 
  let phi := fresh "phi" in 
  let HP := fresh "HP" in 
  let HP' := fresh "HP'" in
  intros phi HP; destruct (in_inv HP) as [? | HP'];
  subst; auto; destruct (in_inv HP'); subst; auto. 

Lemma permutation : forall G D phi,  
  deduction G phi -> 
  (forall phi', In phi' G -> In phi' D) -> 
  deduction D phi.
Proof.
  intros G D phi H. revert D. induction H; intros D HP; eauto 4.
  - eapply OrE. 3: eauto. 
    + eapply IHdeduction1. permuted. 
    + eapply IHdeduction2. permuted.
  - apply ImpI. apply IHdeduction. permuted.
Qed. 

Lemma weakening : forall G phi phi', 
  deduction G phi -> 
  deduction (phi' :: G) phi. 
Proof.
  intros G phi phi' H. induction H; eauto.
  - eapply OrE. 3: eassumption. 
    + apply (permutation _ _ _ IHdeduction1). permuted.
    + apply (permutation _ _ _ IHdeduction2). permuted.
  - eapply ImpI. apply (permutation _ _ _ IHdeduction).
    permuted.
Qed.  

Lemma incl_assign_ctx : forall A B l1 l2 (f : A -> B) G,
  incl (map f (l1 ++ l2)) G -> 
  incl (map f l1) G /\ incl (map f l2) G.
Proof.
  intros. induction l1.
  - simpl in *. split. apply incl_nil_l. assumption.
  - simpl in *. destruct (incl_cons_inv H). destruct (IHl1 H1). split.
    + apply incl_cons; tauto.
    + assumption.
Qed.

Lemma assign_ctx_truth : forall phi V G, 
  incl (assign_ctx V (vars phi)) G -> 
  (satisfies V phi -> deduction G phi) /\
  (proj1_sig (denotation V phi) = 0 -> deduction G (lnot phi)).
Proof.
  intros phi V. induction phi; intros G HG; split; intros HV.
  - inversion HV.
  - apply ImpI. auto.
  - simpl in *. desD (V i). inversion HV. subst. simpl. auto.
  - simpl in *. desD (V i). auto.
  - simpl in *. destruct (denotation V phi2) eqn:E. destruct x.
    + simpl in *. desD (denotation V phi1). 
      specialize (IHphi1 G). specialize (IHphi2 G).
      destruct (incl_assign_ctx _ _ _ _ _ _ HG).
      destruct (IHphi1 H). destruct (IHphi2 H0). 
      clear H1 H3. specialize (H2 Logic.eq_refl).
      specialize (H4 Logic.eq_refl). apply ImpI. 
      apply BotE. apply weakening with (phi' := phi1) in H2.
      assert (deduction (phi1 :: G) phi1) by auto.
      eapply ImpE; eauto.
    + assert (x = 0) by lia. subst. simpl in *.  
      destruct (incl_assign_ctx _ _ _ _ _ _ HG). 
      destruct (IHphi2 G H0). specialize (H1 Logic.eq_refl).
      apply ImpI. apply weakening. assumption.
  - simpl in *. destruct (incl_assign_ctx _ _ _ _ _ _ HG). 
    destruct (denotation V phi1) eqn:E. destruct x;
    try desD (denotation V phi2).
    assert (x = 0) by lia. subst. simpl in *.
    destruct (IHphi1 G H). destruct (IHphi2 G H0).
    clear HV H H0 H2 H3. specialize (H1 Logic.eq_refl).
    specialize (H4 Logic.eq_refl). apply ImpI. 
    assert (deduction (imp phi1 phi2 :: G) (imp phi1 phi2)) by auto.
    eapply weakening in H1. pose proof (ImpE _ _ _ H H1).
    eapply weakening in H4. eauto.
  - simpl in *. destruct (incl_assign_ctx _ _ _ _ _ _ HG).
    destruct (IHphi1 G H). destruct (IHphi2 G H0).
    destruct (dmax_top _ _ HV); rewrite H5 in *; auto.
  - simpl in *. destruct (incl_assign_ctx _ _ _ _ _ _ HG).
    destruct (dmax_bot _ _ HV). rewrite H1 in *.
    rewrite H2 in *. destruct (IHphi1 G H). destruct (IHphi2 G H0). specialize (H4 Logic.eq_refl). specialize (H6 Logic.eq_refl). assert (deduction (lor phi1 phi2 :: G) (lor phi1 phi2)) by auto. apply OrE with (rho := bot) in H7.
    apply ImpI. assumption. 
    + apply permutation with (G := ((lor phi1 phi2 :: phi1 :: G))). apply weakening. assert (deduction (phi1 :: G) phi1) by auto. apply weakening with (phi' := phi1) in H4. 
    apply (ImpE _ _ _ H4 H8). permuted.
    + apply permutation with (G := ((lor phi1 phi2 :: phi2 :: G))).
    2: permuted. apply weakening. assert (deduction (phi2 :: G) phi2) by auto. apply weakening with (phi' := phi2) in H6.
    apply (ImpE _ _ _ H6 H8).
  - simpl in *. destruct (dmin_top _ _ HV). 
    rewrite H in *. rewrite H0 in *. 
    destruct (incl_assign_ctx _ _ _ _ _ _ HG). 
    destruct (IHphi1 G H1). destruct (IHphi2 G H2).
    auto.
  - simpl in *. destruct (incl_assign_ctx _ _ _ _ _ _ HG).
    assert (deduction (land phi1 phi2 :: G) (land phi1 phi2)) by auto. destruct (dmin_bot _ _ HV); rewrite H2 in *.
    + destruct (IHphi1 G H). specialize (H4 Logic.eq_refl). 
      apply ImpI. apply AndEL in H1. eapply weakening in H4. 
      eapply (ImpE _ _ _ H4 H1).
    + destruct (IHphi2 G H0). specialize (H4 Logic.eq_refl).
      apply ImpI. apply AndER in H1. eapply weakening in H4.
      eapply (ImpE _ _ _ H4 H1).
Qed.

Lemma lem : forall G phi,
  deduction G (lor phi (lnot phi)).
Proof.
  intros G phi. eapply ImpE. apply DNE. 
  apply ImpI. eapply ImpE with (phi := (lor phi (lnot phi))).
  auto. apply OrIR. apply ImpI. 
  eapply ImpE with (phi := lor phi (lnot phi)); auto.
Qed.

Lemma lemE : forall G phi phi',
  deduction (phi :: G) phi' -> 
  deduction ((lnot phi) :: G) phi' -> 
  deduction G phi'.
Proof.
  intros G phi phi' HT HF. eapply OrE. eapply HT.
  eapply HF. apply lem.
Qed.  

Lemma elim_ctx : forall G phi,
  (forall V, deduction (assign_ctx V G) phi) -> 
  deduction [] phi.
Proof.
  induction G; intros phi H.
  - specialize (H (fun _ => dtop)). assumption.
  - apply IHG. intros V. assert (forall (b : domain),
      deduction ((if proj1_sig b =? 1 then var a else lnot (var a))
      :: assign_ctx V G) phi) as HC.
    + intros b. set (V' := fun x => if x =? a then b else V x).
      eapply permutation with (G := assign_ctx V' (a :: G)). 
      apply H. intros phi' HP. apply in_map_iff in HP.
      destruct HP as (x & HE & HIn). subst. unfold V'. 
      bdestruct (x =? a).
      * subst. destruct (proj1_sig b =? 1); auto.
      * apply in_cons. unfold assign_ctx. apply in_map_iff. 
        exists x. split; auto. destruct HIn; intuition. 
        symmetry in H1. apply H0 in H1. contradiction.
    + apply lemE with (phi := var a). 
      * apply (HC dtop).
      * apply (HC dbot).
Qed.  

Theorem completeness : forall phi,
  valid phi -> deduction [] phi.
Proof.
  intros phi H. apply elim_ctx with (G := vars phi).
  intros V. eapply (proj1 (assign_ctx_truth phi V _ _)).
  apply H. Unshelve. apply incl_refl. 
Qed.

End PropositionalLogic.