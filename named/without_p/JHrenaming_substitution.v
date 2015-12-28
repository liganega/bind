(** Renaming of Constants *)

Set Implicit Arguments.

Require Import decidable_IN.
Require Import associations.
Require Import sublist.
Require Import language_syntax.
Require Import fresh_cst.

(** [McKinna & Pollak] and [Leroy] made useful applications of
   swapping technique. Here we use simultaneous substitution and
   renaming instead of swapping. Indeed, they together work more
   general than swapping. *) 

Notation substitution := (assoc trm).

(* Definition cst_substitution := assoc name. *)
Notation renaming := (assoc name).

(** Renaming will be considered to be a special substitution. *)

(* Fixpoint subst_emb (rho: cst_substitution) : substitution := *)
Fixpoint renaming_emb (rho: renaming) : substitution :=
  match rho with
  | nil            => nil
  | (x, a) :: rho' => (x, Cst a) :: renaming_emb rho'
  end.

(** ** Simultaneous renaming *)

Fixpoint rename_t (eta : renaming) (t : trm) : trm := 
  match t with
    | BVar y      => BVar y
    | Cst c       => match eta ^^ c with
                       | Some d => Cst d
                       | None   => Cst c
                     end
    | App f t1 t2 => App f (rename_t eta t1)  (rename_t eta t2)
  end.

(* Fixpoint rename_f (eta : renaming) (A : fml) : fml :=  *)
Fixpoint rename (eta : renaming) (A : fml) : fml := 
  match A with
    | Atom (p, t) => Atom (p, rename_t eta t)
    | B --> C     => (rename eta B) --> (rename eta C)
    | Forall y B  => Forall y (rename eta B)
  end.

Fixpoint rename_c (eta : renaming) (Ga : context) : context := 
  match Ga with
    | nil => nil
    | A :: Ga0 => rename eta A :: rename_c eta Ga0
  end.

(** We need to rename associations, too. *)

Fixpoint rename_a (eta : renaming) (rho : assoc trm) :=
  match rho with
    | nil           => nil
    | (x,t) :: rho0 => (x, rename_t eta t) :: rename_a eta rho0
  end.

(** Properties of renaming and substitution *)

Lemma rename_t_nil : forall (t:trm),
  rename_t nil t = t.
Proof.
  induction t; simpl; f_equal; auto.
Defined.

Lemma rename_nil : forall (A:fml),
  rename nil A = A.
Proof.
  induction A as [(p, t)| |]; simpl; f_equal; auto.
  f_equal; auto using rename_t_nil.
Defined.

Lemma rename_c_nil : forall (Ga:context),
  rename_c nil Ga = Ga.
Proof.
  induction Ga; simpl; f_equal; auto using rename_nil.
Defined.

Lemma rename_a_nil : forall rho,
  rename_a nil rho = rho.
Proof.
 induction rho; simpl; intros; auto.
 destruct a; rewrite IHrho; rewrite rename_t_nil; auto.
Defined.

Hint Resolve rename_t_nil rename_nil : datatypes.
Hint Resolve rename_c_nil rename_a_nil : datatypes.

Hint Rewrite rename_t_nil rename_nil : datatypes.
Hint Rewrite rename_c_nil rename_a_nil : datatypes.

Lemma rename_IN_ctx : forall A Ga eta,
    IN_ctx A Ga ->
    IN_ctx (rename eta A) (rename_c eta Ga).
Proof.
  induction Ga; simpl; intros;
  repeat case_lang; auto; congruence.
Defined.

Lemma IN_dom_sig_rename : 
  forall (x: name) (rho: assoc trm)(eta:renaming) t,
    rho ^^ x = Some t ->
    (rename_a eta rho) ^^ x = Some (rename_t eta t).
Proof.
  induction rho as [ | [y b] ]; simpl; intros;
    [ discriminate
      | case_var; inversion H; subst; auto
    ].
Defined.

Hint Resolve rename_IN_ctx IN_dom_sig_rename : datatypes.
Hint Rewrite rename_IN_ctx IN_dom_sig_rename : datatypes.

Lemma nil_subst_t : forall t,
 t = (t [[nil]]).
Proof.
induction t; simpl; auto.
f_equal; auto.
Defined. 

Lemma nil_subst : forall A,
 A = (A [nil]).
Proof.
- induction A as [ [p t] | |]; simpl; intros.
  + rewrite <- nil_subst_t; auto.
  + f_equal; auto.
  + rewrite <- IHA; auto.
Defined.

Hint Resolve nil_subst_t nil_subst : datatypes.
Hint Rewrite nil_subst_t nil_subst : datatypes.

Lemma subst_t_rm : forall t n rho,
 (t [[rho^-n]]) = (t [[(n,BVar n) ::rho]]).
Proof.
- induction t; simpl; intros; auto with datatypes.
  + destruct (n==n0); subst.
    rewrite assoc_rm_self; auto.
    (* rewrite <- (assoc_rm_neq rho n1); auto. *)
    rewrite <- (lookup_assoc_rm_neq rho n1); auto.
  + rewrite <- IHt1, <- IHt2; auto.
Defined.

Lemma subst_rm : forall A n rho,
 (A [rho^-n]) = (A [(n,BVar n) ::rho]).
Proof.
- induction A; try destruct a; simpl; intros.
  + do 2 f_equal.
    rewrite subst_t_rm; auto.
  + rewrite <- IHA1, <- IHA2; auto.
  + destruct (n==n0); subst.
    (* rewrite <- rm_rm; auto. *)
    rewrite <- assoc_rm_rm; auto.
    rewrite <- IHA.
    (* rewrite rm_neq_rm; auto. *)
    rewrite assoc_rm_neq_rm; auto.
Defined.

Hint Resolve subst_t_rm subst_rm : datatypes.
Hint Rewrite subst_t_rm subst_rm : datatypes.

Lemma rename_subst_t : forall (t:trm) (rho:assoc trm)(eta:renaming),
  sub_name (bv_t t) (dom rho) ->
  rename_t eta (t[[rho]]) =
  ((rename_t eta t)[[rename_a eta rho]]).
Proof.
- induction t; simpl; intros.
  + assert (I1 : n @ dom rho); auto with datatypes. 
    destruct (@IN_dom_sig trm n rho I1).
    pose proof (@IN_dom_sig_rename n rho eta x e) as I2.
    rewrite e, I2; auto.
  + destruct (eta ^^ n); auto.
  + f_equal. 
    rewrite IHt1; auto with datatypes.
    rewrite IHt2; auto with datatypes.
Defined.

Hint Resolve rename_subst_t : datatypes.
Hint Rewrite rename_subst_t : datatypes.

Lemma re_sub_0 : forall eta rho n,
 rename_a eta (rho ^- n) = (rename_a eta rho) ^- n.
Proof.
  induction rho; try destruct a; auto; intros; simpl.
  destruct (n0==n); subst; auto; simpl.
  rewrite IHrho; auto.
Defined.

Lemma re_sub_1 : forall eta rho n,
(rename_a eta rho ^- n) ^^ n = None.
Proof.
  induction rho; try destruct a; simpl; intros; auto.
  destruct (n0==n); subst; auto; simpl.
  destruct (n0==n); subst; try tauto; apply IHrho.  
Defined.

Hint Resolve re_sub_0 re_sub_1 : datatypes. 
Hint Rewrite re_sub_0 re_sub_1 : datatypes.

Lemma re_sub_2 : forall eta rho n m,
 n <> m -> (rename_a eta (rho ^- m)) ^^ n = (rename_a eta rho) ^^ n. 
Proof.
  induction rho; intros;  try destruct a; simpl;
  repeat case_var; try apply IHrho; simpl;
  repeat case_var; try apply IHrho; tauto.
Defined.

Hint Resolve re_sub_2 : datatypes. 
Hint Rewrite re_sub_2 : datatypes.

Lemma IN_dom_none_rename : forall x rho eta,
  rho ^^ x = None -> rename_a eta rho ^^ x = None.
Proof.
  induction rho; try destruct a; simpl; intros; auto.
  destruct (x==n); try tauto.
  inversion H. auto.
Defined.

Hint Resolve IN_dom_none_rename IN_dom_sig_rename : datatypes.
Hint Rewrite IN_dom_none_rename IN_dom_sig_rename : datatypes.

Lemma re_sub_3 : forall t eta rho n,
   rename_t eta (t [[(n, BVar n) :: rho]]) =
   ((rename_t eta t) [[rename_a eta rho ^- n]]).
Proof.
induction t; intros.
- destruct (n==n0).
  + rewrite <- e in *; clear e; simpl.
    destruct (n==n); try tauto; try clear e.
    rewrite re_sub_1; auto.
  + simpl.
    destruct (n==n0); try tauto.
    clear n2.
    rewrite <-re_sub_0.
    rewrite re_sub_2; auto.
    pose proof IN_dom_sig_rename n rho eta.
    pose proof IN_dom_none_rename n rho eta.
    destruct (rho ^^ n); auto.
    * rewrite H with t; auto.
    * simpl. rewrite H0; auto.
- simpl; destruct(eta ^^ n); auto.
- simpl; rewrite <- IHt1, <- IHt2; auto.
Defined.

(* Hint Resolve re_sub_3 rm_rm : datatypes. *)
Hint Resolve re_sub_3 assoc_rm_rm : datatypes.
(* Hint Rewrite re_sub_3 rm_rm : datatypes. *)
Hint Rewrite re_sub_3 assoc_rm_rm : datatypes.

Lemma re_sub_4 : forall A eta rho n,
  rename eta (A [(n, BVar n) :: rho]) =
  (rename eta A [rename_a eta rho ^- n]).
Proof.
induction A; intros; try destruct a.
- simpl; rewrite re_sub_3; auto.
- simpl; rewrite <- IHA1, <- IHA2; auto.
- simpl; destruct (n==n0).
  * rewrite <- e in *; clear e.
    (* rewrite <- rm_rm. *)
    rewrite <- assoc_rm_rm.
    rewrite <- IHA.
    do 2 f_equal; auto with datatypes.
  * simpl; pose proof (IHA eta (rho ^- n0) n); f_equal.
    rewrite <- re_sub_0.
    rewrite <- H.
    rewrite <- subst_rm with (rho:=(rho ^- n0)).
    rewrite <- subst_rm with (rho:=(rho ^- n)).
    (* rewrite rm_neq_rm with (x:=n)(y:=n0); try tauto. *)
    rewrite assoc_rm_neq_rm with (x:=n)(y:=n0); try tauto.
Defined.

Hint Resolve re_sub_4 : datatypes.
Hint Rewrite re_sub_4 : datatypes.

Lemma rename_subst : forall (A:fml) (rho:assoc trm)(eta:renaming),
  sub_name (bv A) (dom rho) ->
  rename eta (A [rho]) =
  ((rename eta A)[rename_a eta rho]).
Proof.
- induction A as [(p, t) | |]; simpl; intros.
  + do 2 f_equal; apply rename_subst_t; auto.
  + f_equal; try rewrite <- IHA1; try rewrite <- IHA2; auto with datatypes.
  + assert (sub_name (bv A) (dom ((n, BVar n) :: rho))); 
    simpl; auto with datatypes.
    pose proof IHA ((n,BVar n) ::rho) eta H0; f_equal.
    rewrite subst_rm; f_equal.
    auto with datatypes.
Defined.

Hint Resolve rename_subst : datatypes.
Hint Rewrite rename_subst : datatypes.

(** ** Renaming and freshness *)

Lemma rename_t_fresh : forall (t:trm) eta a a0,
  a # oc_t t ->
  rename_t ((a,a0) :: eta) t = rename_t eta t.
Proof.
- induction t; simpl; intros.
  + reflexivity.
  + repeat case_var; try congruence; elim H; auto.
  + destruct_notin; f_equal; auto.  
Defined.

Lemma rename_fresh : forall (A:fml) eta a a0,
  a # oc A ->
  rename ((a, a0) :: eta) A = rename eta A.
Proof.
- induction A as [(p, t) | | ]; simpl; intros.
  + do 2 f_equal; apply rename_t_fresh; auto.
  + destruct_notin; f_equal; auto.
  + f_equal; auto.
Defined.

Lemma rename_c_fresh : forall Ga eta a a0,
  a # oc_c Ga ->
  rename_c ((a, a0) :: eta) Ga = rename_c eta Ga.
Proof.
  induction Ga as [ | A Ga0]; simpl; intros; auto.
  destruct_notin; f_equal; auto using rename_fresh.
Defined.

Hint Resolve rename_t_fresh rename_fresh rename_c_fresh : datatypes.
Hint Rewrite rename_t_fresh rename_fresh rename_c_fresh : datatypes.

Definition fun_value (eta : renaming) (a:name) : name :=
  match eta ^^ a with
    | Some a0 => a0
    | None   => a
  end.

Notation " eta ** a " := (fun_value eta a) (at level 60).

Lemma notIN_img : forall (eta:renaming) a a0 a1,
  a # img eta ->
  eta ^^ a0 = Some a1 ->
  a <> a1.
Proof.
  induction eta as [ |[x] ]; simpl; intros;
  repeat case_var; intuition try congruence; eauto.
Defined.

Lemma trm_rename_fresh : forall (t:trm) eta a a0,
  a0 # oc_t t ->
  a0 # dom eta ->
  a0 # img eta ->
  rename_t ((a0, eta ** a) :: eta) (rename_t ((a, a0) :: nil) t) = 
  rename_t eta t.
Proof.
- induction t; simpl; intros; destruct_notin.
  + reflexivity.
  + repeat case_var; simpl; firstorder.
    rewrite (notIN_dom_None _ _ H0); simpl. 
    case_var; intuition; unfold fun_value.
    destruct (eta ^^ a); auto.
    case_eq (eta ^^ a); intros.
    assert (n <> a0); firstorder. 
    repeat case_var; try tauto.
    repeat case_var; try tauto.
  + f_equal; auto.
Defined.

Lemma fml_rename_fresh : forall (A:fml) eta a a0,
  a0 # oc A ->
  a0 # dom eta ->
  a0 # img eta ->
  rename ((a0, eta ** a) :: eta) (rename ((a, a0) :: nil) A) = 
  rename eta A.
Proof.
- induction A as [ [p t]| |]; simpl; intros.
  + do 2 f_equal; auto using trm_rename_fresh.
  + destruct_notin; f_equal; auto.
  + f_equal; auto.
Defined.

Hint Resolve notIN_img trm_rename_fresh fml_rename_fresh : datatypes.
Hint Rewrite trm_rename_fresh fml_rename_fresh : datatypes.

Lemma context_rename_fresh : forall De eta a a0,
  a0 # oc_c De ->
  a0 # dom eta ->
  a0 # img eta ->
  rename_c ((a0, eta ** a) :: eta) (rename_c ((a, a0) :: nil) De) =
  rename_c eta De.
Proof.
- induction De as [ | A]; simpl; intros.
  + reflexivity.
  + destruct_notin; f_equal; auto using fml_rename_fresh.
Defined.

Hint Resolve context_rename_fresh : datatypes.
Hint Rewrite context_rename_fresh : datatypes.

Lemma notIN_oc_rename_t : forall (t : trm) eta a a0,
  a0 # img eta ->
  a <> a0 ->
  a0 # oc_t (rename_t ((a0, eta ** a) :: eta) t).
Proof.
- induction t; simpl; intros.
  + auto.
  + case_var; simpl.
    * unfold fun_value. 
      case_eq (eta ^^ a); intros; auto;
      case_var; auto; elim (notIN_img eta a H H1); auto.
    * case_eq (eta ^^ n); simpl; intros;
      case_var; auto; elim (notIN_img eta n H H1); auto.
  + solve_notin.
Defined.

Lemma notIN_oc_rename : forall (A : fml) eta a a0,
  a0 # img eta ->
  a <> a0 ->
  a0 # oc (rename ((a0, eta ** a) :: eta) A).
Proof.
- induction A as [(p,t) | |]; simpl; intros.
  + auto using notIN_oc_rename_t.
  + solve_notin.
  + auto.
Defined.

Lemma notIN_oc_rename_c : forall (Ga : context) eta a a0,
  a0 # img eta ->
  a <> a0 ->
  a0 # oc_c (rename_c ((a0, eta ** a) :: eta) Ga).
Proof.
  induction Ga as [ | A Ga0]; simpl; intros;
  auto using notIN_app_2, notIN_oc_rename.
Defined.

Hint Resolve notIN_oc_rename_t notIN_oc_rename notIN_oc_rename_c : datatypes.

Lemma sub_ctx_fresh_cst : forall Ga Ga0 a a0,
  sub_ctx_pre Ga Ga0 ->
  a # oc_c Ga ->
  sub_ctx_pre Ga (rename_c ((a, a0) :: nil) Ga0).
Proof.
  unfold sublist; intros.
  assert (a1 = rename ((a, a0):: nil) a1).
  - rewrite rename_fresh.
    + symmetry; apply rename_nil.
    + contradict H0; exact (IN_oc_sub H1 a H0).  
  - rewrite H2; apply rename_IN_ctx; auto.  
Defined.

Hint Resolve sub_ctx_fresh_cst : datatypes.
Hint Rewrite sub_ctx_fresh_cst : datatypes.

(** ** Renaming and well-formedness *)

(** Before we defined inductively well-formed expressions. It will be
  shown that they are exactly the expressions without any free
  occurrence of bound variables. *)

Lemma empty_bv_wf_t : forall t, bv_t t = nil -> wf_t t.
Proof.
- induction t; simpl; intros.
  + discriminate.
  + apply wCst.
  + apply wApp; simpl; try apply IHt1;
    apply app_eq_nil in H; firstorder.
Qed.

Hint Resolve empty_bv_wf_t : datatypes.

Lemma cst_sub_cst : forall rho m u,
 renaming_emb rho ^^ m = Some u -> exists c, u = Cst c.
Proof. 
- induction rho; try destruct a; simpl in *; intros.
  + discriminate.
  + destruct (m==n); subst.
    exists n0; inversion H; auto.
    apply IHrho with (m:=m); auto.
Defined.

Lemma open_subst_t : forall u (rho : renaming) n t, 
    open_t (u [[renaming_emb rho ^- n]]) n t =
    (u [[(n, t) :: renaming_emb rho]]).
Proof.
  unfold open_t; induction u as [ m | m | ]; simpl; intros.
  - case_var.
    + rewrite assoc_rm_self; simpl; destruct (n==n); tauto. 
    (* + rewrite <- assoc_rm_neq; auto. *)
    + rewrite <- lookup_assoc_rm_neq; auto.
      pose proof (cst_sub_cst rho m).
      destruct (renaming_emb rho ^^ m); simpl. 
      * pose proof (H t0).
        assert (exists c, t0 = Cst c); try apply H0; auto.
        destruct H1; rewrite H1; auto.
      * destruct (m==n); tauto. 
  - reflexivity.
  - f_equal; auto.
Defined.

Hint Resolve open_subst_t cst_sub_cst empty_bv_wf_t rename_IN_ctx : datatypes.
Hint Rewrite open_subst_t cst_sub_cst rename_IN_ctx : datatypes.

Lemma emb_rm : forall rho m,
 renaming_emb (rho ^- m) = renaming_emb rho ^- m.
Proof.
  induction rho; try destruct a; simpl; intros; auto.
  destruct (m==n); subst; simpl; try tauto; try rewrite IHrho; auto.
Defined.

Lemma open_subst : forall A rho n t, 
    open (A [renaming_emb rho ^- n]) n t = (A [(n, t) :: renaming_emb rho]).
Proof.
  unfold open; induction A as [ [P u]| | m ]; simpl; intros.
  - do 2 f_equal; apply open_subst_t.
  - f_equal; auto.
  - case_var.
    (* * rewrite <- rm_rm; rewrite nil_subst; auto. *)
    * rewrite <- assoc_rm_rm; rewrite nil_subst; auto.
    (* * f_equal; rewrite rm_neq_rm; auto.     *)
    * f_equal; rewrite assoc_rm_neq_rm; auto.    
      pose proof (IHA (rho ^- m) n t).
      rewrite <- emb_rm; auto.
Defined.

Lemma IN_ren_sub : forall n rho,
 n @ dom rho -> n @ dom (renaming_emb rho).
Proof.
  induction rho; try destruct a; simpl; intros;
  try destruct (n==n0); auto.
Defined.

Lemma bv_wf_subst_t : forall t rho,
    sub_name (bv_t t) (dom rho) ->
    wf_t (t [[renaming_emb rho]]).
Proof.
  induction t; simpl in *; intros; auto with datatypes.
  - assert (n @ dom rho); try apply H; simpl; try case_var; try tauto.
    apply IN_ren_sub in H0.
    destruct (@IN_dom_sig trm n (renaming_emb rho) H0).
    destruct (@cst_sub_cst rho n x e).
    subst; rewrite e; apply wCst.
  - apply wApp; try apply IHt1; try apply IHt2; auto with datatypes.
Defined.

Hint Resolve bv_wf_subst_t IN_ren_sub open_subst emb_rm : datatypes.
Hint Rewrite IN_ren_sub open_subst emb_rm : datatypes.

Lemma bv_wf_subst : forall A (rho : renaming), 
    sub_name (bv A) (dom rho) ->
    wf (A [renaming_emb rho]).
Proof.      
  induction A; simpl; intros rho Hsub.
  - destruct a.
    apply wAtom; auto with datatypes.
  - apply wImply; auto with datatypes.
  - set (a := new (oc (A [renaming_emb rho ^- n]))).
    apply wForall with (c := a);
    assert (a = new(oc (A [renaming_emb rho ^- n]))); auto.
    + rewrite H.
      apply (new_fresh (oc (A [renaming_emb rho ^- n]))).
    + rewrite (open_subst). 
      cut ((n,Cst a) :: renaming_emb rho = renaming_emb ((n,a) :: rho)).
      * intro Hsubst. rewrite Hsubst.
        apply IHA; simpl; auto with datatypes.
      * auto with datatypes.
Defined.

Lemma empty_bv_wf : forall A, bv A = nil -> wf A.
Proof.
  intros A Hbv.
  cut (A = (A [renaming_emb nil])).
  - intro H. rewrite H.
    apply bv_wf_subst.
    rewrite Hbv; auto with datatypes.
  - simpl; auto with datatypes.
Defined. 

Lemma wf_t_bv_empty : forall t, wf_t t -> bv_t t = nil.
Proof.
  induction t; simpl; intros; inversion H; auto.
  rewrite IHt1, IHt2; auto.
Defined.

Hint Resolve bv_wf_subst empty_bv_wf wf_t_bv_empty : datatypes.
Hint Rewrite wf_t_bv_empty : datatypes.




Lemma rm_cons_eq : forall (A:Type) (decA:decidable A) (a:A) l m,
remove decA a (l ++ m) = (remove decA a l) ++ (remove decA a m).
Proof.
  induction l; simpl; intros; auto with datatypes.
  destruct (decA a a0); subst; simpl; try apply IHl; try rewrite <- IHl; auto.
Defined.

Hint Resolve rm_cons_eq : datatypes.
Hint Rewrite rm_cons_eq : datatypes.

Lemma rm_bv_t_eq : forall t c x,
remove eqdec x (bv_t t) = bv_t (t [[(x, Cst c) :: nil]]).
Proof.
  induction t; simpl; intros; auto with datatypes.
  - destruct (x==n); destruct (n==x); try subst; simpl; try tauto.
  - rewrite <- (IHt1 c x); rewrite <- (IHt2 c x); auto with datatypes.
Defined.

Hint Resolve rm_bv_t_eq : datatypes.
Hint Rewrite rm_bv_t_eq : datatypes.

Lemma rm_rm_eq_rm : forall (A:Type) (decA: decidable A) a l,
remove decA a (remove decA a l) = remove decA a l.
Proof.
  induction l; simpl; auto.
  destruct (decA a a0); subst; try tauto; simpl.
  destruct (decA a a0); subst; try tauto; simpl.
  rewrite IHl; auto.
Defined.

Hint Resolve rm_rm_eq_rm : datatypes. 
Hint Rewrite rm_rm_eq_rm : datatypes.

Lemma rm_eq_1 : forall (A:Type) (decA: decidable A) a b l,
remove decA a (remove decA b l) = remove decA b (remove decA a l).
Proof.
  induction l; simpl; intros; auto with datatypes.
  - destruct (decA b a0); subst; simpl; try tauto.
    + destruct (decA a a0); subst; simpl; try tauto.
      destruct (decA a0 a0); subst; simpl; try tauto.
    + destruct (decA a a0); subst; simpl; try tauto.
      destruct (decA b a0); subst; simpl; try tauto.
      rewrite IHl; auto.
Defined.

Hint Resolve rm_eq_1 : datatypes. 
Hint Rewrite rm_eq_1 : datatypes.

Lemma rm_bv_eq : forall A c x,
remove eqdec x (bv A) = bv (A [(x, Cst c) :: nil]).
Proof.
  induction A; try destruct a; simpl; intros; auto with datatypes.
  - rewrite <- IHA1, <- IHA2; auto with datatypes.
  - destruct (n==x); subst; simpl.
    + rewrite <- nil_subst; auto with datatypes.
    + rewrite <- IHA; auto with datatypes.
Defined.

Hint Resolve rm_bv_eq. Hint Rewrite rm_bv_eq.

Lemma wf_bv_empty : forall A, wf A -> bv A = nil.
Proof.
  induction 1; simpl; intros; auto with datatypes.
  - rewrite IHwf1, IHwf2; auto.
  - rewrite <- IHwf.
    unfold open in *; auto.
Defined.

Hint Resolve wf_bv_empty. Hint Rewrite wf_bv_empty.

Lemma sub_q_open : forall A x u,
 sub_name (bv (Forall x A)) (bv (open A x u)).
Proof.
  induction A as [ [P t]| | m ]; simpl; intros.
  - induction t; simpl; intros; auto.
    + repeat case_var; simpl; try tauto; auto with datatypes.
    + rewrite rm_cons_eq; apply app_sub_2; auto.
  - rewrite rm_cons_eq.
    unfold open in *; simpl in *.
    apply app_sub_2; auto.
  - unfold open in *; simpl in *.
    case_var; subst; simpl; try tauto; auto with datatypes.
    + rewrite rm_rm_eq_rm; rewrite <- nil_subst; auto.
    + rewrite rm_eq_1; apply sub_rm_1; auto.
Defined.

Lemma open_forall_wf : forall A x u, wf (open A x u) -> wf (Forall x A).
Proof.
  intros A x u Hwf.
  apply empty_bv_wf.
  apply wf_bv_empty in Hwf.
  apply sub_nil with eqdec.
  rewrite <- Hwf.
  apply sub_q_open; auto.
Defined.

Hint Resolve sub_q_open open_forall_wf.
Hint Rewrite sub_q_open.

Lemma open_rename_t_eq : forall t eta y a,
 (rename_t eta t [[(y, Cst (eta ** a)) :: nil]]) = rename_t eta (t [[(y, Cst a) :: nil]]).
Proof.
  induction t; simpl; intros; auto.
  - destruct (n==y); simpl; unfold fun_value; destruct (eta ^^ a); auto.
  - destruct (eta ^^ n); simpl; auto.
  - rewrite IHt1, IHt2; auto.
Defined.

Hint Resolve open_rename_t_eq. Hint Rewrite open_rename_t_eq.

Lemma open_rename_eq : forall A eta y a,
 open (rename eta A) y (Cst (eta ** a)) = rename eta (open A y (Cst a)).
Proof.
  induction A as [ [P t]| | m ]; unfold open in *; simpl; intros. 
  - do 2 f_equal; apply open_rename_t_eq; auto.
  - rewrite IHA1, IHA2; auto.
  - f_equal; case_var; auto; do 2 rewrite <- nil_subst; auto.
Defined.

Hint Resolve open_rename_eq. Hint Rewrite open_rename_eq.

Lemma rename_wf_t_eq : forall t eta,
 bv_t (rename_t eta t) = bv_t t.
Proof.
  induction t; simpl; intros; auto.
  - destruct (eta ^^ n); simpl; auto.
  - rewrite IHt1, IHt2; auto.
Defined.

Hint Resolve rename_wf_t_eq. Hint Rewrite rename_wf_t_eq.
 
Lemma rename_wf_t : forall t eta,
 wf_t t -> wf_t (rename_t eta t).
Proof.
  intros; apply empty_bv_wf_t; apply wf_t_bv_empty in H; rewrite <- H; auto.
Defined. 

Hint Resolve rename_wf_t. 

Lemma rename_wf_eq : forall A eta,
 bv (rename eta A) = bv A.
Proof.
  induction A as [ [P t]| | m ]; simpl; intros; auto.
  - rewrite IHA1, IHA2; auto.
  - rewrite IHA; auto.
Defined.

Hint Resolve rename_wf_eq. Hint Rewrite rename_wf_eq.

Lemma rename_wf_f : forall A eta,
 wf A -> wf (rename eta A).
Proof.
  intros; apply wf_bv_empty in H; apply empty_bv_wf; rewrite <- H; auto.
Defined.

Hint Resolve rename_wf_f.

Lemma rename_wf_c : forall De eta,
 wf_c De -> wf_c (rename_c eta De).
Proof.
  induction De; simpl; auto; intros.
  apply wCons; inversion H; try apply IHDe; auto.
Defined.

Lemma wf_c_wf : forall Ga A,
 IN_ctx A Ga -> (wf_c Ga) -> wf A.
Proof.
  induction Ga; simpl; intros; try tauto. 
  destruct (fml_dec A a); subst; inversion H0; subst; auto.
Defined.

Lemma wf_sub_ctx : forall Ga De,
 sub_ctx_pre Ga De -> wf_c De -> wf_c Ga.
Proof.
  induction Ga; simpl; intros; auto.
  - apply wNil.
  - apply wCons.
    + apply IHGa with De; try apply sub_cons_1 with a; auto.
    + apply wf_c_wf with De; auto.
      unfold sublist in H; apply H; simpl; destruct (fml_dec a a); try tauto.
Defined.

Hint Resolve rename_wf_c wf_c_wf wf_sub_ctx.

Lemma forall_wf_sub : forall A x,
 wf (Forall x A) -> sub_name (bv A) (x::nil).
Proof.
  intros. 
  assert (bv (Forall x A) = nil); try apply wf_bv_empty; try assumption; simpl in H0.
  apply sub_rm_2; rewrite H0; intro; tauto.
Defined.

Hint Resolve forall_wf_sub. Hint Rewrite forall_wf_sub.

