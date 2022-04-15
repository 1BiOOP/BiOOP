From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import Coq.Lists.List.ListNotations.
From OOREF Require Export Maps.
From Coq Require Import Arith.
From Coq Require Import Lia.

(* Syntax *)
Inductive term : Type :=
  | var : nat -> term
  | field : term -> nat -> term
  | invk : nat ->term -> string -> term -> term
  | newt : nat -> term -> term
  | cast : nat -> nat -> term -> term
  | tnil : term
  | tcons : term -> term -> term.

Inductive val : Type :=
  | vnil : val
  | vcons : val -> val -> val
  | newv : nat -> val -> val.

Definition methods : Type := partial_map term.
Definition classTable : Type := list (nat * methods).





(* Auxiliary Function *)
Fixpoint lookup {A:Type} (n:nat) (l:list A) : option A :=
  match l with
  | nil => None
  | x :: xs =>
    match n with
    | 0 => Some x
    | _ => lookup (n-1) xs
    end
  end.

Inductive vlookup : nat -> val -> val -> Prop :=
  | VL1 : forall v vs,
          vlookup 0 (vcons v vs) v
  | VL2 : forall n v vs v',
          lt 0 n ->
          vlookup n vs v ->
          vlookup (n+1) (vcons v' vs) v.

Fixpoint replace (n:nat) (v':val) (l:list val) : list val:=
  match l with
  | nil => nil
  | x :: xs =>
    match n with
    | 0 => v':: xs
    | _ => x :: (replace (n-1) v' xs)
    end
  end.

Inductive vreplace: val -> nat -> val -> val -> Prop:=
  | VR1 : forall v vs v',
              vreplace (vcons v vs) 0 v' (vcons v' vs)
  | VR2 : forall vs n v' vs' v,
             vreplace vs n v' vs' ->
             vreplace (vcons v vs) (n+1) v' (vcons v vs').

Inductive sub : classTable -> nat -> nat -> Prop :=
  | SSelf : forall ct c1,
            sub ct c1 c1
  | STrans : forall ct c1 c2 c3,
            sub ct c1 c2 ->
            sub ct c2 c3 ->
            sub ct c1 c3
  | SDef : forall c2 ms c1 ct,
           Some (c2,ms) = lookup c1 ct ->
           sub ct c1 c2.

Fixpoint mbody (idx:nat) (ct:classTable) (cn:nat) (m:string) : option term :=
  match idx with
  | 0 => None
  | S n => match lookup cn ct with
           | Some (cf, ms) =>
              match ms m with
              | Some tr => Some tr
              | None =>
                if n =? cf 
                then
                  mbody n ct cf m
                else
                  mbody n ct cn m
              end
           | None => None
           end
  end.

(* Inductive mbody : classTable -> nat -> string -> term -> Prop :=
  | MSelf : forall ct cn m ms tr cf,
            Some (cf, ms) = lookup cn ct ->
            Some tr = ms m ->
            mbody ct cn m tr
  | MFath : forall ct cn m ms tr cf,
            Some (cf, ms) = lookup cn ct ->
            None = ms m ->
            mbody ct cf m tr ->
            mbody ct cn m tr. *)




(* Forward Evaluation *)
Inductive eval : (classTable * list val) -> term -> val -> Prop :=
  | EVar : forall v n env ct,
           Some v = lookup n env ->
           eval (ct,env) (var n) v
  | EProj : forall ct env t cn vs v f,
            eval (ct,env) t (newv cn vs) ->
            vlookup f vs v ->
            eval (ct,env) (field t f) v
  | EInvk : forall ct env t cn us ts vs tr m v,
            eval (ct,env) t (newv cn us) ->
            eval (ct,env) ts vs ->
            Some tr = mbody cn ct cn m ->
            eval (ct,(newv cn us)::vs::nil) tr v ->
            eval (ct,env) (invk cn t m ts) v
  | ENewt : forall ct env cn ts vs,
            eval (ct,env) ts vs ->
            eval (ct,env) (newt cn ts) (newv cn vs)
  | ECast : forall ct env t cn vs cf,
            eval (ct,env) t (newv cn vs) ->
            sub ct cn cf ->
            eval (ct,env) (cast cn cf t) (newv cn vs)
  | ENIl : forall ct env,
            eval (ct,env) tnil vnil
  | ECons : forall ct env t v ts vs,
            eval (ct,env) t v ->
            eval (ct,env) ts vs ->
            eval (ct,env) (tcons t ts) (vcons v vs).

Inductive freeEq : list val -> list val -> term -> Prop :=
  | FVar : forall (l1 l2:list val) n,
           List.length l1 = List.length l2 ->
           lookup n l1 = lookup n l2 ->
           freeEq l1 l2 (var n)
  | FField : forall l1 l2 t f,
           freeEq l1 l2 t ->
           freeEq l1 l2 (field t f)
  | FInvk : forall l1 l2 cn t m ts,
            freeEq l1 l2 t ->
            freeEq l1 l2 ts ->
            freeEq l1 l2 (invk cn t m ts)
  | FNewt : forall l1 l2 c ts,
              freeEq l1 l2 ts ->
              freeEq l1 l2 (newt c ts)
  | FCast : forall l1 l2 cf t cn,
              freeEq l1 l2 t ->
              freeEq l1 l2 (cast cn cf t)
  | FNil : forall l1 l2,
              freeEq l1 l2 tnil
  | FCons : forall l1 l2 t ts,
              freeEq l1 l2 t ->
              freeEq l1 l2 ts ->
              freeEq l1 l2 (tcons t ts).

Inductive retEq : classTable -> classTable -> term -> Prop :=
  | RVar : forall ct1 ct2 n,
           retEq ct1 ct2 (var n)
  | RField : forall ct1 ct2 t f,
             retEq  ct1 ct2 t ->
             retEq ct1 ct2 (field t f)
  | RInvk : forall (ct1 ct2:classTable) (cn:nat) t ts m cn tr,
            retEq ct1 ct2 t ->
            retEq ct1 ct2 ts ->
            Some tr = mbody cn ct1 cn m ->
            Some tr = mbody cn ct2 cn m ->
            retEq ct1 ct2 tr ->
            retEq ct1 ct2 (invk cn t m ts)
  | RNewt : forall ct1 ct2 cn ts,
            retEq ct1 ct2 ts ->
            retEq ct1 ct2 (newt cn ts)
  | RCast : forall ct1 ct2 t cf cn,
            retEq ct1 ct2 t ->
            sub ct1 cn cf ->
            sub ct2 cn cf -> 
            retEq ct1 ct2 (cast cn cf t)
  | RNil : forall ct1 ct2,
            retEq ct1 ct2 tnil
  | RCons : forall ct1 ct2 t ts,
            retEq ct1 ct2 t ->
            retEq ct1 ct2 ts ->
            retEq ct1 ct2 (tcons t ts).

(* Backward Evaluation *)
Inductive beval : (classTable * list val * term) -> val ->(classTable * list val * term) -> Prop :=
  | BVar : forall env' n v' env ct,
           env' = replace n v' env ->
           beval (ct,env,var n) v' (ct,env',var n)
  | BField : forall ct env t cn vs vs' f v' ct' env' t',
             eval (ct,env) t (newv cn vs) ->
             vreplace vs f v' vs' ->
             beval (ct,env,t) (newv cn vs') (ct',env',t') ->
             beval (ct,env,field t f) v' (ct',env',field t' f)
  | BInvk : forall ct env t cn us ts vs m tr vs' v' ct' us' tr' ct1 env1 t' ct2 env2 ts' ct'' env'',
            eval (ct,env) t (newv cn us) ->
            eval (ct,env) ts vs ->
            Some tr = mbody cn ct cn m ->
            beval (ct,[newv cn us;vs],tr) v' (ct',[newv cn us';vs'],tr') ->
            beval (ct,env,t) (newv cn us') (ct1,env1,t') ->
            beval (ct,env,ts) vs' (ct2,env2,ts') ->
            Some tr' = mbody cn ct'' cn m ->
            retEq ct' ct'' tr' ->
            retEq ct1 ct'' t' ->
            retEq ct2 ct'' ts' ->
            freeEq env1 env'' t' ->
            freeEq env2 env'' ts' ->
            beval (ct,env,invk cn t m ts) v' (ct'', env'', invk cn t' m ts')
  | BNewt : forall ct env ts vs' ct' env' ts' cn,
            beval (ct,env,ts) vs' (ct',env',ts') ->
            beval (ct,env,newt cn ts) (newv cn vs') (ct',env',newt cn ts')
  | BCast : forall ct env t v' ct' env' t' cf cn,
            beval (ct,env,t) v' (ct',env',t') ->
            beval (ct,env,cast cn cf t) v' (ct',env',cast cn cf t')
  | BNil : forall ct env,
            beval (ct,env,tnil) vnil (ct,env,tnil)
  | BCons : forall ct env ct1 env1 t' ct2 env2 ts' v' vs' ct' env' t ts,
            beval (ct,env,t) v' (ct1,env1,t') ->
            beval (ct,env,ts) vs' (ct2,env2,ts') ->
            retEq ct1 ct' t' ->
            retEq ct2 ct' ts' ->
            freeEq env1 env' t' ->
            freeEq env2 env' ts' ->
            beval (ct,env,tcons t ts) (vcons v' vs') (ct',env',tcons t' ts').





(* Auxiliary Lemma *)
Lemma del_head : forall (v:val) l1 l2,
  l1 = l2 ->
  v::l1 = v::l2.
Proof.
  intros. rewrite<-H. reflexivity.
Qed.

Lemma rep_look : forall v n l,
  Some v = lookup n l->
  l = replace n v l.
Proof with auto.
  intros. unfold replace. generalize dependent n.
  induction l as [|v' l'];intros n Hlen.
  - reflexivity.
  - destruct n;simpl...
    + simpl in Hlen. inversion Hlen. reflexivity.
    + apply del_head. apply IHl'. simpl in Hlen. 
      rewrite Hlen. reflexivity.
Qed.

Lemma vrep_look : forall v n vs,
  vlookup n vs v ->
  vreplace vs n v vs.
Proof with auto.
  intros. generalize dependent n. 
  induction vs;intros;inversion H;subst.
  - apply (VR1 v vs2 v).
  - apply (VR2 vs2 n0 v vs2 vs1).
    apply IHvs2 in H5. apply H5.
Qed.

(* Lemma mbody_deterministic : forall ct cn m tr1 tr2,
  mbody ct cn m tr1 ->
  mbody ct cn m tr2 ->
  tr1 = tr2.
Proof.
  intros. generalize dependent tr2. induction H;intros.
  - inversion H1;subst;rewrite<-H in H2;inversion H2;subst.
    + rewrite<-H0 in H3. inversion H3. reflexivity.
    + rewrite<-H0 in H3. discriminate H3.
  - inversion H2;subst;rewrite<-H in H3;inversion H3;subst.
    + rewrite<-H0 in H4. discriminate H4.
    + apply IHmbody in H5. assumption.
Qed. *)

Lemma lookup_deterministic : forall n vs v1 v2,
  vlookup n vs v1 ->
  vlookup n vs v2 ->
  v1 = v2.
Proof.
  intros. generalize dependent v2.
  induction H;intros.
  - inversion H0;subst. reflexivity. lia.
  - inversion H1;subst.
    + lia.
    + apply Nat.add_cancel_r in H2. rewrite->H2 in H7. 
      apply IHvlookup in H7. assumption.
Qed.

(* Lemma eval_deterministic : forall ct env t v1 v2,
  eval (ct,env) t v1 ->
  eval (ct,env) t v2 ->
  v1 = v2.
Proof.
  intros. generalize dependent v2.
  induction H;intros.
  + inversion H0;subst. rewrite<-H in H5. inversion H5. reflexivity.
  + inversion H1;subst. apply IHeval in H7. inversion H7;subst.
    apply lookup_deterministic with (v2:=v2) in H0. assumption.
    assumption.
  + inversion H3;subst.
    apply IHeval1 in H9. inversion H9;subst.
    apply IHeval2 in H11. inversion H11;subst.
    apply mbody_deterministic with (tr1:=tr) (tr2:=tr0) in H1.
    rewrite<-H1 in H13. apply IHeval3 in H13. assumption. assumption.
  + inversion H0;subst. apply IHeval with (v2:=vs0) in H6.
    rewrite->H6. reflexivity.
  + inversion H1;subst. apply IHeval with (v2:=newv cn0 vs0) in H7.
    assumption.
  + inversion H0;subst. reflexivity.
  + inversion H1;subst. apply IHeval1 with (v2:=v0) in H7. rewrite->H7.
                        apply IHeval2 with (v2:=vs0) in H8. rewrite->H8.
                        reflexivity.
Qed. *)

Lemma freeEq_eval_same : forall env1 env2 ct t v,
  freeEq env1 env2 t ->
  eval (ct,env1) t v ->
  eval (ct,env2) t v.
Proof.
  intros. generalize dependent v.
  induction t;intros;inversion H0;subst;inversion H;subst.
  + constructor. rewrite->H5. assumption.
  + apply (EProj ct env2 t cn vs v n).
    {apply IHt with (v:=newv cn vs) in H4;assumption. }
    {assumption. }
  + apply (EInvk ct env2 t1 n us t2 vs tr s v).
    {apply IHt1 with (v:=newv n us) in H5;assumption. }
    {apply IHt2 with (v:=vs) in H12;assumption. }
    {assumption. }
    {assumption. }
  + apply (ENewt ct env2 n t vs).
    apply IHt with (v:=vs) in H4;assumption.
  + apply (ECast ct env2 t n vs n0).
    {apply IHt with (v:=newv n vs) in H4;assumption. }
    {assumption. }
  + constructor.
  + apply (ECons ct env2 t1 v0 t2 vs).
    {apply IHt1 with (v:=v0) in H5;assumption. }
    {apply IHt2 with (v:=vs) in H8;assumption. }
Qed.

(* Lemma retEq_eval_same : forall ct1 ct2 t env v,
  retEq ct1 ct2 t ->
  eval (ct1,env) t v ->
  eval (ct2,env) t v.
Proof.
  intros. generalize dependent v.
  induction H;intros.
  + inversion H0;subst. constructor. assumption.
  + inversion H0;subst. apply (EProj ct2 env t cn vs v f).
    {apply IHretEq with (v:=newv cn vs) in H6;assumption. }
    {assumption. }
  + inversion H5;subst. apply (EInvk ct2 env t cn0 us ts vs tr0 m v).
    {apply IHretEq1 with (v:=newv cn0 us) in H11;assumption. }
    {apply IHretEq2 with (v:=vs) in H13;assumption. }
    {apply eval_deterministic with (v2:=newv cn us) in H12. inversion H12;subst.
      - apply mbody_deterministic with (tr2:=tr) in H15. 
        rewrite->H15. apply H4. apply H3.
      - apply H1. }
    { apply eval_deterministic with (v2:=newv cn us) in H12. inversion H12;subst.
      apply mbody_deterministic with (tr2:=tr) in H15. rewrite->H15 in H16. rewrite->H15.
      apply eval_deterministic with (v2:=vs) in H14.
      rewrite->H14 in H16. rewrite->H14.
      apply IHretEq3 with (v:=v) in H16. 
      assumption. assumption. assumption. assumption. }
  + inversion H0;subst. apply (ENewt ct2 env cn ts vs).
    apply IHretEq in H6. assumption.
  + inversion H3;subst. apply (ECast ct2 env t cn0 vs cf).
    {apply IHretEq with (v:=newv cn0 vs). assumption. }
    {apply eval_deterministic with (v1:=newv cn us) in H9.
     inversion H9;subst. assumption. assumption. }
  + inversion H0;subst. constructor.
  + inversion H1;subst. apply (ECons ct2 env t v0 ts vs).
    - apply IHretEq1 with (v:=v0) in H7. assumption.
    - apply IHretEq2 with (v:=vs) in H8. assumption.
Qed. *)

(* Lemma retEq_freeEq_eval_same : forall ct1 ct2 env1 env2 t v,
  retEq ct1 ct2 t ->
  freeEq env1 env2 t ->
  eval (ct1,env1) t v ->
  eval (ct2,env2) t v.
Proof.
  intros.
  apply freeEq_eval_same with (ct:=ct1) (v:=v) in H0.
  - apply retEq_eval_same  with (env:=env2) (v:=v) in H;assumption...
  - assumption.
Qed. *)

Lemma freeEq_same_env : forall env t,
  freeEq env env t.
Proof.
  intros. induction t;constructor;try reflexivity;try assumption.
Qed.


Lemma retEq_same_ct : forall ct t,
  retEq ct ct t.
Proof.
  intros. induction t.
  - constructor.
  - constructor. assumption.
  -

(* Theorem getput : forall ct env t v,
  eval (ct,env) t v ->
  beval (ct,env,t) v (ct,env,t).
Proof.
  intros. induction H.
  - apply (BVar env0 n v env0 ct0). apply rep_look. apply H.
  - apply (BField ct0 env0 t cn vs vs f v ct0 env0 t).
    + apply H.
    + apply vrep_look in H0. apply H0.
    + apply IHeval.
  - apply (BInvk ct0 env0 t cn us ts vs m tr vs v ct0 us tr ct0 env0 t ct0 env0 ts ct0 env0)
    ;try assumption.
    4:{ apply freeEq_same_env. }
    4:{ apply freeEq_same_env. }
Qed. *)

Theorem putget : forall ct env t v' ct' env' t',
  beval (ct,env,t) v' (ct',env',t') ->
  eval (ct',env') t' v'.
Proof.
  intros.
Qed.




