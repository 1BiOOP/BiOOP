From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.
From Coq Require Import Arith.
From Coq Require Import Lia.
Require Import Coq.Lists.List Coq.Bool.Bool.
Import Coq.Lists.List.ListNotations.
Scheme Equality for list.

(* Syntax *)
Inductive exp : Type :=
  | eConst : nat -> exp
  | eVar : nat -> exp
  | eAbs : string -> exp -> exp
  | eApp : exp -> exp -> exp
  | eRef : exp -> exp
  | eDeRef : exp -> exp
  | eAssign : exp -> exp -> exp.

Inductive val : Type :=
  | vConst : nat -> val
  | vUnit : val
  | vLoc : nat -> val
  | vClosure : (list val) -> exp -> val
  | vError : val.

Definition env := list val.
Definition memory := list val.




(* Auxiliary Function *)
Fixpoint lookup (n:nat) (l:list val) : val :=
  match l with
  | nil => vError
  | x :: xs =>
    match n with
    | 0 => x
    | _ => lookup (n-1) xs
    end
  end.

Fixpoint replace (n:nat) (v':val) (l:list val) : list val:=
  match l with
  | nil => nil
  | x :: xs =>
    match n with
    | 0 => v':: xs
    | _ => x :: (replace (n-1) v' xs)
    end
  end.

Inductive deleteTail: list val -> list val -> Prop :=
  | Del : forall l l' v,
          l = l'++[v] ->
          deleteTail l l'.

Inductive freeEq : list val -> list val -> exp -> Prop :=
  | FConst : forall l1 l2 n,
             freeEq l1 l2 (eConst n)
  | FAbs : forall l1 l2 e s,
             freeEq l1 l2 e ->
             freeEq l1 l2 (eAbs s e)
  | FVar : forall l1 l2 n,
           length l1 = length l2 ->
           lookup n l1 = lookup n l2 ->
           freeEq l1 l2 (eVar n)
  | FApp : forall l1 l2 e1 e2,
           freeEq l1 l2 e1 ->
           freeEq l1 l2 e2 ->
           freeEq l1 l2 (eApp e1 e2)
  | FRef : forall l1 l2 e,
            freeEq l1 l2 e ->
            freeEq l1 l2 (eRef e)
  | FDeRef : forall l1 l2 e,
              freeEq l1 l2 e ->
              freeEq l1 l2 (eDeRef e)
  | FAssign : forall l1 l2 e1 e2,
              freeEq l1 l2 e1 ->
              freeEq l1 l2 e2 ->
              freeEq l1 l2 (eAssign e1 e2).

Definition merge (E1 E2 E:list val) (e1 e2:exp) : Prop :=
  freeEq E1 E e1 /\ freeEq E2 E e2.



(* Forward Evaluation *)
Inductive eval : (env * memory * exp) -> (val * memory) -> Prop :=
  | EConst : forall E M n,
              eval (E,M,eConst n) (vConst n,M)

  | EAbs : forall E M (s:string) e,
            eval (E,M,eAbs s e) (vClosure E e,M)

  | EVar : forall E M (n:nat) (v:val),
            n < length E ->
            v = lookup n E ->
            eval (E,M,eVar n) (v,M)

  | EApp : forall E M e1 e2 Ef ef M1 v2 M2 Ef1 M3 v,
            eval (E,M,e1) (vClosure Ef ef,M1) ->
            eval (E,M1,e2) (v2,M2) ->
            Ef1 = v2 :: Ef ->
            eval (Ef1,M2,ef) (v,M3) ->
            eval (E,M,eApp e1 e2) (v,M3)

  | ERef : forall E M e v M1,
            eval (E,M,e) (v,M1) ->
            eval (E,M,eRef e) (vLoc (length M1),M1++v::nil)

  | EDeRef : forall E M e M1 v n,
              eval (E,M,e) (vLoc n,M1) ->
              n < length M1 ->
              v = lookup n M1 ->
              eval (E,M,eDeRef e) (v,M1)

  | EAssign : forall E M e1 e2 M1 M2 v n M2',
              eval (E,M,e1) (vLoc n,M1) ->
              eval (E,M1,e2) (v,M2) ->
              n < length M2 ->
              M2' = replace n v M2 ->
              eval (E,M,eAssign e1 e2) (vUnit,M2').




(* Backward Evaluation *)
Inductive beval : (env * memory * exp) -> (val * memory) 
                    -> (env * memory * exp) -> Prop :=
  | BConst : forall E M n n' M',
             beval (E,M,eConst n) (vConst n',M') (E,M',eConst n')

  | BAbs : forall E M s e E' e' M',
            beval (E,M,eAbs s e) (vClosure E' e',M') (E',M',eAbs s e')

  | BVar : forall E M n v' M' E',
            n < length E ->
            E' = replace n v' E ->
            beval (E,M,eVar n) (v',M') (E',M',eVar n)

  | BApp : forall E M e1 Ef ef M1 e2 v2 M2 v' M3' v2' Ef' M2' ef' E2 M1' e2' E1 M' e1' E',
          eval (E,M,e1) (vClosure Ef ef,M1) ->
          eval (E,M1,e2) (v2,M2) ->
          beval (v2::Ef,M2,ef) (v',M3') (v2'::Ef',M2',ef') ->
          beval (E,M1,e2) (v2',M2') (E2,M1',e2') ->
          beval (E,M,e1) (vClosure Ef' ef',M1') (E1,M',e1') ->
          merge E1 E2 E' e1' e2' ->
          beval (E,M,eApp e1 e2) (v',M3') (E',M',eApp e1' e2')

  | BRef : forall v' n M2' E M e M1' E' M' e',
            n = length M1' ->
            v' = lookup n M2' ->
            deleteTail M2' M1' ->
            beval (E,M,e) (v',M1') (E',M',e') ->
            beval (E,M,eRef e) (vLoc n,M2') (E',M',eRef e')

  | BDeRef : forall E M e n M1 M1' v' E' M' e',
              eval (E,M,e) (vLoc n,M1) ->
              n < length M1' ->
              v' = lookup n M1' ->
              beval (E,M,e) (vLoc n,M1') (E',M',e') ->
              beval (E,M,eDeRef e) (v',M1') (E',M',eDeRef e')

  | BAssign : forall E M e1 n M1 e2 v M2 v' M2' M2'' E2 M1' e2' E1 M' e1' E',
              eval (E,M,e1) (vLoc n,M1) ->
              eval (E,M1,e2) (v,M2) ->
              n < length M2' ->
              v' = lookup n M2' ->
              M2'' = replace n (lookup n M2) M2' ->
              beval (E,M1,e2) (v',M2'') (E2,M1',e2') ->
              beval (E,M,e1) (vLoc n,M1') (E1,M',e1') ->
              merge E1 E2 E' e1' e2' ->
              beval (E,M,eAssign e1 e2) (vUnit,M2') (E',M',eAssign e1' e2').




(* Premise *)
Lemma del_head : forall (v:val) l1 l2,
  l1 = l2 ->
  v::l1 = v::l2.
Proof.
  intros. rewrite<-H. reflexivity.
Qed.

Lemma rep_look : forall n E,
  n < length E ->
  replace n (lookup n E) E = E.
Proof with auto.
  intros. unfold replace. generalize dependent n.
  induction E as [|v E'];intros n Hlen.
  - reflexivity.
  - destruct n;simpl... apply del_head. apply IHE'. simpl in Hlen. 
    apply lt_S_n in Hlen. rewrite Nat.sub_0_r. apply Hlen.
Qed.

Lemma look_rep : forall v n E,
  n < length E ->
  lookup n (replace n v E) = v.
Proof with auto.
  intros. unfold lookup. generalize dependent n.
  induction E as [| v' E']; intros n Hlen.
  - inversion Hlen.
  - destruct n;simpl...
    apply IHE'. simpl in Hlen. lia.
Qed.

Lemma merge_same_env : forall E e1 e2,
  merge E E E e1 e2.
Proof with auto.
  intros. unfold merge. split.
  - induction e1;constructor;try reflexivity...
  - induction e2;constructor;try reflexivity...
Qed.

Lemma len_plus_one : forall (l:list val) v,
  S (length l) = length (v::l).
Proof.
  intros. reflexivity.
Qed.

Lemma gethead : forall x (l:list val) v,
  (x::l)++v::nil=x::(l++v::nil).
Proof.
  intros. reflexivity.
Qed.

Lemma look_len : forall l v,
  lookup (length l) (l++v::nil) = v.
Proof.
  intros. induction l as [|x l'].
  - unfold lookup. simpl. reflexivity.
  - rewrite<-len_plus_one.
    rewrite->gethead with (l:=l'). simpl. 
    assert (H1:length l'-0=length l').
    {destruct l'. reflexivity. reflexivity. }
    rewrite->H1.
    apply IHl'.
Qed.

Lemma rep_look_rep : forall E n v,
  E = replace n (lookup n E) (replace n v E).
Proof with auto.
  intros. unfold replace. generalize dependent n.
  induction E as [|v' E'].
  - intros. reflexivity.
  - intros. destruct n;simpl...
    assert (H:n-0=n).
    {destruct n. reflexivity. reflexivity. }
    rewrite->H. apply del_head. apply IHE'.
Qed.

Lemma rep_same_len : forall n v E,
  length (replace n v E) = length E.
Proof with auto.
  intros. generalize dependent n.
  induction E;intros n.
  - destruct n...
  - destruct n... simpl. rewrite IHE...
Qed.

Lemma closure_eq : forall E1 E2 e,
  freeEq E1 E2 e ->
  vClosure E1 e = vClosure E2 e.
Proof. Admitted.

Lemma eq_on_free_eval_same : forall E1 E2 e M v M',
  freeEq E1 E2 e ->
  eval (E1,M,e) (v,M') ->
  eval (E2,M,e) (v,M').
Proof.
  intros. 
  generalize dependent v. 
  generalize dependent M'.
  generalize dependent M.
  induction e. 
  - intros. inversion H0;subst. apply (EConst E2 M' n).
  - intros. inversion H0;subst. inversion H;subst. rewrite->H6. constructor.
    rewrite->H2 in H3. apply H3. reflexivity.
  - intros. inversion H0;subst. inversion H;subst.
    apply closure_eq in H4. rewrite->H4. constructor.
  - intros. inversion H0;subst. inversion H;subst. 
    apply (EApp E2 M e1 e2 Ef ef M1 v2 M2 (v2::Ef) M' v).
    + apply IHe1 with (v:= vClosure Ef ef) (M':=M1) (M:=M) in H5. assumption. assumption.
    + apply IHe2 with (v:=v2) (M':=M2) (M:=M1) in H7. assumption. assumption.
    + reflexivity.
    + assumption.
  - intros. inversion H0;subst. inversion H;subst.
    apply (ERef E2 M e v0 M1).
    apply IHe with (v:=v0) (M':=M1) (M:=M) in H5. assumption. assumption.
  - intros. inversion H0;subst. inversion H;subst.
    apply (EDeRef E2 M e M' (lookup n M') n).
    + apply IHe with (v:=vLoc n) (M:=M) (M':=M') in H4. assumption. assumption.
    + assumption.
    + reflexivity.
  - intros. inversion H0;subst. inversion H;subst.
    apply (EAssign E2 M e1 e2 M1 M2 v0 n (replace n v0 M2)).
    + apply IHe1 with (v:=vLoc n) (M:=M) (M':=M1) in H6. assumption. assumption.
    + apply IHe2 with (v:=v0) (M:=M1) (M':=M2) in H7. assumption. assumption.
    + assumption.
    + reflexivity.
Qed.

Lemma merge_eval_same : forall E1 E2 E e1 e2 M1 v1 M1' M2 v2 M2',
  merge E1 E2 E e1 e2 ->
  (eval (E1,M1,e1) (v1,M1')->eval (E,M1,e1) (v1,M1')) /\
  (eval (E2,M2,e2) (v2,M2')->eval (E,M2,e2) (v2,M2')).
Proof.
  intros. unfold merge in H. split.
  - destruct H as [H1 H2]. 
    apply eq_on_free_eval_same.
    assumption.
  - destruct H as [H1 H2].
    apply eq_on_free_eval_same.
    assumption.
Qed.

Lemma del_pre : forall (l1 l2 l:list val),
  l1 = l2 ->
  l++l1 = l++l2.
Proof.
  intros. induction l.
  - simpl. apply H.
  - simpl. apply del_head. apply IHl.
Qed.

Lemma del_tail_con : forall v (l1 l2:list val) n,
  n = length l1 ->
  v = lookup n l2 ->
  deleteTail l2 l1 ->
  l2 = l1 ++ v::nil.
Proof.
  intros. destruct l1.
  - destruct l2.
    + inversion H1;subst. simpl in H2. discriminate.
    + inversion H1;subst. simpl in H2. inversion H2;subst. simpl. reflexivity.
  - destruct l2.
    + inversion H1;subst. discriminate.
    + inversion H1;subst. rewrite->H2. apply del_pre with (l:=(v0::l1)).
      rewrite->look_len with (l:=(v0::l1)) (v:=v2). reflexivity.
Qed.




(* GETPUT *)
Theorem getput : forall E M e v M1,
  eval (E,M,e) (v,M1) ->
  beval (E,M,e) (v,M1) (E,M,e).
Proof. 
  intros. induction H.
  - apply (BConst E0 M0 n n M0).
  - apply (BAbs E0 M0 s e0 E0 e0 M0).
  - apply (BVar E0 M0 n v0 M0). apply H. rewrite->H0. rewrite->rep_look.
    reflexivity. apply H.
  - apply (BApp E0 M0 e1 Ef ef M2 e2 v2 M3 v0 M4 v2 Ef M3 ef E0 M2 e2 E0 M0 e1 E0).
    + apply H.
    + apply H0.
    + rewrite->H1 in IHeval3. apply IHeval3.
    + apply IHeval2.
    + apply IHeval1.
    + apply merge_same_env.
  - apply (BRef v0 (length M2) (M2++[v0]) E0 M0 e0 M2 E0 M0 e0).
    + reflexivity.
    + rewrite->look_len with (l:=M2) (v:=v0). reflexivity.
    + apply (Del (M2++[v0]) M2) with (v:=v0). reflexivity.
    + apply IHeval.
  - apply (BDeRef E0 M0 e0 n M2 M2 v0 E0 M0 e0).
    + apply H.
    + apply H0.
    + rewrite->H1. reflexivity.
    + apply IHeval.
  - apply (BAssign  E0 M0 e1 n M2 e2 v0 M3 v0 M2' M3 E0 M2 e2 E0 M0 e1 E0).
    + apply H.
    + apply H0.
    + rewrite->H2. rewrite->rep_same_len. apply H1.
    + rewrite->H2. rewrite->look_rep. reflexivity. apply H1.
    + rewrite->H2. apply rep_look_rep.
    + apply IHeval2.
    + apply IHeval1.
    + apply merge_same_env.
Qed.




(* PUTGET *)
Theorem putget : forall E M e v' M1' E' M' e',
  beval (E,M,e) (v',M1') (E',M',e') ->
  eval (E',M',e') (v',M1').
Proof.
  intros. induction H.
  - apply (EConst E0 M'0 n').
  - apply (EAbs E'0 M'0 s e'0).
  - apply (EVar E'0 M'0 n v'0). 
    + rewrite<-rep_same_len with (n:=n) (v:=v'0) (E:=E0) in H.
      rewrite<-H0 in H. apply H.
    + rewrite->H0. rewrite->look_rep. reflexivity. apply H.
  - apply (EApp E'0 M'0 e1' e2' Ef' ef' M1'0 v2' M2' (v2'::Ef') M3' v'0);
    apply merge_eval_same with (M1:=M'0) (v1:=vClosure Ef' ef') (M1':=M1'0)
                               (M2:=M1'0) (v2:=v2') (M2':=M2') in H4;
    destruct H4 as [H5 H6].
    + apply H5. apply IHbeval3.
    + apply H6. apply IHbeval2.
    + reflexivity.
    + assumption.
  - apply del_tail_con with (v:=v'0) (n:=n) in H1.
    rewrite->H1. rewrite->H. apply (ERef E'0 M'0 e'0 v'0 M1'0).
    + assumption.
    + assumption.
    + assumption.
  - apply (EDeRef E'0 M'0 e'0 M1'0 v'0 n).
    + apply IHbeval.
    + apply H0.
    + apply H1.
  - apply (EAssign E'0 M'0 e1' e2' M1'0 M2'' v'0 n M2');
    apply merge_eval_same with (M1:=M'0) (v1:=vLoc n) (M1':=M1'0)
                               (M2:=M1'0) (v2:=v'0) (M2':=M2'') in H6;
    destruct H6 as [H7 H8].
    + apply H7. apply IHbeval2.
    + apply H8. apply IHbeval1.
    + rewrite->H3. rewrite->rep_same_len. apply H1.
    + rewrite->H2. rewrite->H3. apply rep_look_rep.
Qed.
