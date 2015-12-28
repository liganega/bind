(** Renaming of Constants *)

Set Implicit Arguments.

Require Import associations.
Require Import associations_extra.
Require Import language_syntax.
Require Import variable_sets.
Require Import substitution_wellformedness.
Require Import sublist.
Require Import fresh_name.


(** [McKinna & Pollak] and [Leroy] used [simultaneous] parameter swapping
   in order to show the equivalence between different styles of quantification.

   We will use simultaneous [renaming] of constants.
   Note that [renaming] is easier to deal with. *)

(** [renaming] is an arbitrary funtion from [Cst] to [Cst]. *)

(* par_substitution is already defined. *)
Notation renaming := (assoc name).

Fixpoint rename_t (eta : renaming) (t : trm) : trm := 
  match t with
    | Ltr y    => Ltr y
    | Par x   => match eta ^^ x with 
                     | Some y => Par y
                     | None => Par x
                 end
    | Cst c   => Cst c                
    | App f t1 t2 => App f (rename_t eta t1)  (rename_t eta t2)
  end.

Fixpoint rename (eta : renaming) (A : fml) : fml := 
  match A with
    | Atom (p,t) => Atom (p, rename_t eta t )
    | B --> C    => (rename eta B) --> (rename eta C)
    | Forall y B => Forall y (rename eta B)
  end.

Fixpoint rename_c (eta : renaming) (Ga : context) : context := 
  match Ga with
    | nil => nil
    | A :: Ga0 => rename eta A :: rename_c eta Ga0
  end.

(** Renaming associations *)

Fixpoint rename_a (eta : renaming) (rho : assoc trm) :=
  match rho with
    | nil           => nil
    | (x,t) :: rho0 => (x, rename_t eta t) :: rename_a eta rho0
  end.

(* ***************** *)
(* ***************** *)

(** Renaming is a special case of substitution *)

Lemma renaming_Some_subst : 
  forall rho m a,
    rho ^^ m = Some a -> subst_emb rho ^^ m = Some (Par a).
Proof.
  induction rho as [| [n t] rho]; auto; simpl; intros. 
  - discriminate.
  - case_var; solve[auto | congruence].
Defined.

Lemma renaming_None_subst : 
  forall rho m,
    rho ^^ m = None -> subst_emb rho ^^ m = None.
Proof.
  induction rho as [| [n t] rho]; auto; simpl; intros. 
  - case_var; solve[auto | congruence].
Defined.

Implicit Arguments renaming_Some_subst [rho m a].
Implicit Arguments renaming_None_subst [rho m].

Lemma rename_as_subst_t : forall t eta,
    rename_t eta t = t [[subst_emb eta, nil]].
Proof.
  induction t; simpl; intros; auto.
  - case_eq (eta ^^ n).
    + intros a Heq; rewrite (renaming_Some_subst Heq); reflexivity.
    + intros Heq; rewrite (renaming_None_subst Heq); reflexivity.
  - congruence.
Defined. 

Lemma rename_as_subst : forall A eta,
    rename eta A = A [subst_emb eta, nil].
Proof.
  induction A as [ [p t] | |]; simpl; intros;
  try rewrite rename_as_subst_t; congruence.
Defined. 

Lemma rename_as_subst_c : forall Ga eta,
    rename_c eta Ga = Ga [! subst_emb eta, nil !].
Proof.
  induction Ga; simpl; intros.
  - reflexivity.
  - rewrite rename_as_subst; congruence.
Defined.

Hint Resolve rename_as_subst_t rename_as_subst rename_as_subst_c : datatypes.
Hint Rewrite rename_as_subst_t rename_as_subst rename_as_subst_c : datatypes.

(* ***************** *)
(* ***************** *)



(** No renaming means no change  *)

Lemma rename_t_nil : forall (t : trm),
  rename_t nil t = t.
Proof.
  induction t; simpl; f_equal; auto.
Qed.

Lemma rename_nil : forall (A:fml),
  rename nil A = A.
Proof.
  induction A ; [destruct a| |]; simpl; 
  try f_equal; try rewrite rename_t_nil; auto.
Qed.

Lemma rename_c_nil : forall (Ga:context),
  rename_c nil Ga = Ga.
Proof.
  induction Ga; simpl; f_equal; auto using rename_nil.
Qed.

(** Compatibility of renaming with predicates and operators. *)

Lemma rename_IN_ctx : 
  forall A Ga eta,
    IN_ctx A Ga ->
    IN_ctx (rename eta A) (rename_c eta Ga).
Proof.
  induction Ga; simpl; intros;
  repeat case_lang; auto; congruence.
Qed.

Lemma rename_sub_ctx :
  forall Ga De eta,
    sub_ctx_pre Ga De ->
    sub_ctx_pre (rename_c eta Ga) (rename_c eta De).
Proof.
  unfold sublist; induction Ga as [| A Ga]. 
  - simpl; intuition. 
  - intros De eta H B H0. 
    change (rename_c eta (A :: Ga)) 
      with ((rename eta A) :: (rename_c eta Ga)) in H0. 
    case (fml_dec B (rename eta A)); intro; subst; auto. 
    + apply rename_IN_ctx, H; auto with datatypes. 
    + apply IHGa; auto with datatypes.
      apply neq_IN_cons with (rename eta A); auto. 
Qed.                         

Lemma IN_dom_sig_rename : 
  forall (x: name) (rho: assoc trm)(eta:renaming) t,
    rho ^^ x = Some t ->
    (rename_a eta rho) ^^ x = Some (rename_t eta t).
Proof.
  induction rho as [ | [y b] ]; simpl; intros;
    [ discriminate
      | case_var; inversion H; subst; auto
    ].
Qed.

Lemma IN_dom_sig_none_rename :
  forall x rho eta,
    rho ^^ x = None ->
    rename_a eta rho ^^ x = None.
Proof.
  induction rho as [| [y b] rho ]; auto; simpl; intros.
  destruct (x == y); try tauto ;
  [discriminate
  | rewrite IHrho; auto].
Qed.

Hint Resolve rename_IN_ctx IN_dom_sig_rename.
Hint Rewrite rename_IN_ctx IN_dom_sig_rename.

(** Renaming and substitution *)

Lemma subst_t_rm : 
  forall t n eta,
    (t [[nil, eta^-n]]) = (t [[nil, (n,Ltr n) :: eta]]).
Proof.
  induction t; auto; simpl; intros.
  - case_var;
    [ rewrite assoc_rm_self 
    | rewrite <- assoc_rm_neq with (y:=n0) (rho:=eta)]
    ; auto.
   - f_equal; auto. 
Qed.

Lemma subst_rm :
  forall (A : fml) (n : name) (eta : assoc trm),
    (A [nil, eta ^- n]) = (A [nil, (n, Ltr n) :: eta]).
Proof.
  induction A as [ [p t] | |]; auto; simpl; intros.
  - rewrite subst_t_rm; auto.
  - rewrite <- IHA1, IHA2; auto.
  - destruct (n == n0); subst; auto.
    + rewrite <- rm_rm; auto.
    + rewrite <- IHA; rewrite rm_neq_rm; auto. 
Qed.


Lemma rename_comm_assoc_rm :
  forall zeta eta n,
 rename_a zeta (eta ^- n) = (rename_a zeta eta) ^- n.
Proof.
  induction eta as [| [m t]  eta]; auto; simpl; intros. 
  case_var; auto. 
  rewrite <- IHeta; auto.  
Qed.

Lemma rename_notIN : 
  forall zeta eta n,
    (rename_a zeta eta ^- n) ^^ n = None.
Proof.
  induction eta as [| [m t] eta]; auto; simpl; intros.
  repeat (case_var; auto; simpl; auto; try tauto).
Qed.

Lemma rename_neq_rm : 
  forall zeta eta n m,
    n <> m -> 
    (rename_a zeta (eta ^- m)) ^^ n = (rename_a zeta eta) ^^ n. 
Proof.
  induction eta as [| [m t] eta]; auto; simpl; intros.
  do 2 case_var; subst; auto; try tauto.
  - rewrite <- rm_change; auto; rewrite rename_comm_assoc_rm.
    rewrite <-assoc_rm_neq; auto;simpl; case_var; tauto. 
  - simpl; case_var; subst; auto; tauto.
Qed.

Lemma rename_sub_t :
  forall (t : trm) (rho : assoc trm) (zeta : renaming) (n : name),
    rename_t zeta (t [[nil, (n, Ltr n) :: rho]]) =
    ((rename_t zeta t) [[nil, rename_a zeta rho ^- n]]).
Proof. 
  induction t; auto; intros; rewrite <- rename_comm_assoc_rm; simpl.
  - case_var; subst; auto. 
    + rewrite rename_comm_assoc_rm, assoc_rm_self; auto.
    + rewrite rename_neq_rm; auto.
      pose proof (IN_dom_sig_rename n rho zeta);
      pose proof (IN_dom_sig_none_rename n rho zeta).
      case_assoc;
      [ rewrite H with t
      | rewrite H0] ; auto. 
  - case_assoc; auto.
  - rewrite IHt1, IHt2, rename_comm_assoc_rm; auto.
Qed.

Lemma  rename_sub :
  forall (A : fml) (zeta : renaming) (eta : assoc trm) (n : name),
    rename zeta (A [nil, (n, Ltr n) :: eta]) =
    (rename zeta A [nil, rename_a zeta eta ^- n]).
Proof.
  induction A as [ [p t] | |]; auto; simpl; intros.
  - do 2 f_equal; rewrite <- rename_sub_t; auto.
  - rewrite <- IHA1, IHA2; auto.
  - f_equal; case_var; auto. 
    * rewrite <- rm_rm; rewrite <- IHA, subst_rm; auto.
    * rewrite <- rm_neq_rm; auto; rewrite <- rename_comm_assoc_rm; rewrite IHA; auto.
Qed.


Lemma rename_subst_t_r :
  forall (t : trm) (eta : assoc trm) (zeta : renaming),
    sub_name (ol_t t) (dom eta) ->
    rename_t zeta (t [[nil , eta]]) = (rename_t zeta t [[nil , rename_a zeta eta]]).
Proof.
  induction t; auto; simpl; intros. 
  - apply sub_cons_0 in H.  
    destruct (IN_dom_sig n eta H) as [x H0]. 
    rewrite H0. rewrite IN_dom_sig_rename with (t:=x); auto.
  - case_assoc; auto. 
  - f_equal; [rewrite IHt1 | rewrite IHt2]; auto with datatypes. 
Qed.

Lemma rename_subst :
  forall (A : fml) (eta : assoc trm) (zeta : renaming),
    sub_name (ol A) (dom eta) ->
    rename zeta (A [nil, eta]) = (rename zeta A [nil, rename_a zeta eta]).
Proof.
induction A as [ [p t] | |] ; simpl; intros.
 - rewrite rename_subst_t_r; auto.
 - rewrite IHA1, IHA2; auto with datatypes.
 - f_equal; rewrite subst_rm, rename_sub; auto. 
Qed.

(** ** Renaming and freshness *)

Lemma rename_t_fresh : forall (t:trm) eta a a0,
  a # op_t t ->
  rename_t ((a,a0) :: eta) t = rename_t eta t.
Proof.
  induction t; simpl; intros; auto;
  [ repeat case_var; try congruence; elim H 
  | f_equal; [apply IHt1 | apply IHt2] ]; auto with datatypes.
Qed.

Lemma rename_fresh : forall (A:fml) eta a a0,
  a # op A ->
  rename ((a, a0) :: eta) A = rename eta A.
Proof.
  induction A as [ [p t] | | ]; simpl; intros. 
  - do 2 f_equal; apply rename_t_fresh; auto.
  - rewrite IHA1, IHA2; auto with datatypes.
  - f_equal; auto.
Qed.

Lemma rename_c_fresh : forall Ga eta a a0,
  a # op_c Ga ->
  rename_c ((a, a0) :: eta) Ga = rename_c eta Ga.
Proof.
  induction Ga as [ | A Ga0]; simpl; intros; auto.
  destruct_notin; f_equal; auto using rename_fresh.
Qed.

(** Function values *)

Definition fun_value (eta : renaming) (a:name) : name :=
  match eta ^^ a with
    | Some a0 => a0
    | None   => a
  end.

Fixpoint image (A: Type) (rho: assoc A) {struct rho} : list A :=
  match rho with
    | nil           => nil
    | (x,a) :: rho0 => a :: image rho0
  end.

Notation " eta ** a " := (fun_value eta a) (at level 60).

Lemma notIN_image : forall (eta:renaming) a a0 a1,
  a # image eta ->
  eta ^^ a0 = Some a1 ->
  a <> a1.
Proof.
  induction eta as [ |[x] ]; simpl; intros;
  repeat case_var; intuition try congruence; eauto.
Qed.

Lemma trm_rename_fresh : forall (t:trm) eta a a0,
  a0 # op_t t ->
  a0 # dom eta ->
  a0 # image eta ->
  rename_t ((a0, eta ** a) :: eta) (rename_t ((a, a0) :: nil) t) = 
  rename_t eta t.
Proof.
  induction t; simpl; intros; destruct_notin;
    [ reflexivity
      | repeat case_var; simpl; firstorder;
        [ rewrite (notIN_dom_None _ _ H0); simpl; 
          case_var; intuition; unfold fun_value;
            destruct (eta ^^ a); auto
          | case_eq (eta ^^ n); intros;
            [ assert (n2 <> a0);
              [ apply sym_not_eq; eauto using notIN_image
                | simpl; case_var; congruence
              ]
              | simpl; case_var; congruence
            ]
        ]
      | reflexivity
      | f_equal; auto].
Qed.

Lemma fml_rename_fresh : forall (A:fml) eta a a0,
  a0 # op A -> 
  a0 # dom eta ->
  a0 # image eta ->
  rename ((a0, eta ** a) :: eta) (rename ((a, a0) :: nil) A) = 
  rename eta A.
Proof.
   induction A as [ [p t] | |]; simpl; intros;
   [ do 2 f_equal; auto using trm_rename_fresh
   | destruct_notin; f_equal; auto 
   | f_equal; auto].
Qed.

Lemma context_rename_fresh : forall De eta a a0,
  a0 # op_c De ->
  a0 # dom eta ->
  a0 # image eta ->
  rename_c ((a0, eta ** a) :: eta) (rename_c ((a, a0) :: nil) De) =
  rename_c eta De.
Proof.
  induction De as [ | A]; simpl; intros; auto;
    [ destruct_notin; f_equal; auto using fml_rename_fresh
    ].
Qed.

Lemma notIN_op_rename_t : forall (t : trm) eta a a0,
  a0 # image eta ->
  a <> a0 ->
  a0 # op_t (rename_t ((a0, eta ** a) :: eta) t).
Proof.
  induction t; simpl; intros;
    [ auto
      | case_var; simpl;
        [ unfold fun_value; case_eq (eta ^^ a); intros;
          [ case_var; auto; elim (notIN_image eta a H H1); auto
            | case_var; auto
          ]
          | case_eq (eta ^^ n); simpl; intros;
            [ case_var; auto; elim (notIN_image eta n H H1); auto
              | case_var; auto
            ]
        ]
      | auto
      | solve_notin
    ].
Qed.

Lemma notIN_op_rename : forall (A : fml ) eta a a0,
  a0 # image eta ->
  a <> a0 ->
  a0 # op (rename ((a0, eta ** a) :: eta) A).
Proof.
  induction A as [ [p t] | |]; simpl; intros;
    [ auto using notIN_op_rename_t
      | solve_notin
      | auto
    ].
Qed.

Lemma notIN_op_rename_c : forall (Ga : context) eta a a0,
  a0 # image eta ->
  a <> a0 ->
  a0 # op_c (rename_c ((a0, eta ** a) :: eta) Ga).
Proof.
  induction Ga as [ | A Ga0]; simpl; intros;
    auto using notIN_app_2, notIN_op_rename.
Qed.

Lemma sub_ctx_fresh_cst :
  forall Ga Ga0 a a0,
    sub_ctx_pre Ga Ga0 ->
    a # op_c Ga ->
    sub_ctx_pre Ga (rename_c ((a, a0) :: nil) Ga0).
Proof.
  unfold sublist; intros.
  assert (a1 = rename ((a, a0):: nil) a1); 
  [ rewrite rename_fresh ; 
    [ symmetry; apply rename_nil 
    | contradict H0; 
      cut (sub_name (op a1) (op_c Ga)); auto with datatypes]
  | rewrite H2; apply rename_IN_ctx; auto].
 Defined.


(** Well-formedness of provable formulas *)

Lemma empty_ol_wf_t : forall t, ol_t t = nil -> wf_t t.
Proof.
  induction t; simpl; intros.
  - discriminate.
  - apply wPar.
  - apply wCst.
  - apply wApp;
    simpl;
     try apply IHt1;
      apply app_eq_nil in H; firstorder.
Qed.

(* Hint Resolve  open_subst emb_rm. *)
(* Hint Rewrite IN_ren_sub open_subst emb_rm. *)

Lemma empty_ol_t_subst : 
  forall t eta, 
    ol_t t = nil -> 
    t [[nil, subst_emb eta]] = t. 
Proof.
  induction t; intros; try simpl; auto.
  - discriminate.
  - f_equal; simpl in H; 
    [ rewrite IHt1 with eta
     | rewrite IHt2 with eta]; 
    destruct (app_eq_nil (ol_t t1) (ol_t t2) H); auto with datatypes.
Qed.

Lemma wf_t_ol_empty : forall t, wf_t t -> ol_t t = nil.
Proof.
  induction t; simpl; intros; inversion H; auto;
  rewrite IHt1, IHt2; auto.
Defined.

Lemma ol_wf_subst_t : 
  forall t (rho : par_substitution),
    sub_name (ol_t t) (dom rho) ->
    wf_t (t [[nil, subst_emb rho]]).
Proof. 
  induction t; auto; intros; simpl.
  - apply IN_sublist in H. 
    assert (n @ dom (subst_emb rho)).
    + induction rho as [ | [x b] rho]; auto; simpl.
      change (dom ((x, b) :: rho)) with (x :: dom rho) in H;
    change (dom ((x, Par b) :: subst_emb rho)) 
    with ( x :: dom (subst_emb rho)).
    simpl; case_var; 
    [ auto with datatypes 
    | apply IHrho; apply neq_IN_cons with x; auto]. 
    + destruct (IN_dom_sig n (subst_emb rho) H0);
      destruct (par_sub_par rho n e). 
      case_assoc; [inversion e; subst; auto using wPar | discriminate]. 
  - apply wPar. 
  - apply wCst. 
  - simpl in *; apply wApp;auto with datatypes. 
Qed. 

Lemma ol_wf_subst : forall A (rho : par_substitution), 
  sub_name (ol A) (dom rho) ->
  wf (A [nil, subst_emb rho]).
Proof.      
  induction A as [ [p t] | |]; simpl; intros rho Hsub.
  - apply wAtom; apply ol_wf_subst_t; auto. 
  - apply wImply; auto with datatypes.
  - set (a := new (op (A [nil, subst_emb rho ^- n]))).
    apply wForall with (c := a). 
    apply new_fresh.
    + rewrite open_subst; 
        change ((n, Par a) :: subst_emb rho) 
              with (subst_emb ((n, a) :: rho)); 
        apply IHA; simpl; auto with datatypes. 
Defined.

Lemma empty_ol_wf : forall A, ol A = nil -> wf A.
Proof.
  intros A Hol. 
  cut (A = (A [nil, subst_emb nil])).
  - intro H; rewrite H.
    apply ol_wf_subst; rewrite Hol; auto with datatypes.
  - simpl; auto using nil_subst with datatypes. 
Defined. 

Hint Resolve ol_wf_subst empty_ol_wf wf_t_ol_empty.
Hint Rewrite wf_t_ol_empty.


Lemma rm_ol_t_eq : forall t c x,
rm_name x (ol_t t) = ol_t (t [[nil, (x, Par c) :: nil]]).
Proof.
  induction t; simpl; intros; auto with datatypes.
  - repeat case_var; intuition. 
  - rewrite <- IHt1; rewrite<- IHt2; auto with datatypes. 
Defined.

Hint Resolve rm_ol_t_eq.
Hint Rewrite rm_ol_t_eq.

Lemma rm_ol_eq : forall A c x,
  rm_name x (ol A) = ol (A [nil, (x, Par c) :: nil]).
Proof.
  induction A as [ [p t] | | ]; intros; simpl; auto with datatypes.
  - rewrite <- IHA1, <- IHA2; auto with datatypes.
  - case_var; [rewrite <- nil_subst | rewrite <- IHA]; auto with datatypes.
Defined.

Hint Resolve rm_ol_eq.
Hint Rewrite rm_ol_eq.

Lemma wf_ol_empty : forall A, wf A -> ol A = nil.
Proof.
  induction 1; simpl; auto with datatypes. 
  - rewrite IHwf1, IHwf2; auto.
  - rewrite <- IHwf;
    rewrite rm_ol_eq with (c:=c); auto. 
Defined. 

Hint Resolve wf_ol_empty.
Hint Rewrite wf_ol_empty.

Lemma sub_q_open : 
  forall A x u,
    sub_name (ol (Forall x A)) (ol (open A x u)).
Proof. 
  induction A as [ [ p t ] | |] ; simpl; intros.
  - induction t ; auto; simpl.
    + do 2 case_var; auto with datatypes;
      congruence.
    + rewrite <- rm_app; auto with datatypes. 
  - simpl in *; unfold open in * |-. 
    set (k :=  (ol (A1 [nil, (x, u) :: nil]) ++ ol (A2 [nil, (x, u) :: nil]))).
    cut (sub_name (rm_name x (ol A1)) k /\ sub_name (rm_name x (ol A2))  k).
    + intro H; destruct H; auto with datatypes. 
    + intuition; subst k; eauto with datatypes.
  - case_var; 
    [ rewrite <- nil_subst, rm_rm_eq_rm; auto with datatypes 
    | rewrite rm_neq_eq; apply sub_rm_1; apply IHA].
Defined.

Lemma open_forall_wf : forall A x u, wf (open A x u) -> wf (Forall x A).
Proof.
  intros A x u Hwf. 
  apply empty_ol_wf; apply wf_ol_empty in Hwf.
  apply sub_nil with eqdec; rewrite <- Hwf; auto using sub_q_open.
Defined.

Hint Resolve sub_q_open open_forall_wf.
Hint Rewrite sub_q_open.


(** Well-Formedness and Renaming *)

Lemma rename_wf_t_eq : forall t eta,
  ol_t (rename_t eta t) = ol_t t.
Proof.
  induction t; auto; simpl; intros;
  [ case_assoc
  | rewrite IHt1, IHt2]; auto.
Defined.

Hint Resolve rename_wf_t_eq. Hint Rewrite rename_wf_t_eq.
 
Lemma rename_wf_t : forall t eta,
  wf_t t -> wf_t (rename_t eta t).
Proof.
  intros; 
  apply empty_ol_wf_t.
  apply wf_t_ol_empty in H.
  rewrite <- H; auto.
Defined. 

Hint Resolve rename_wf_t. 

Lemma rename_wf_eq : forall A eta,
  ol (rename eta A) = ol A.
Proof.
  induction A; try destruct a; simpl; auto; intros;
  [ rewrite IHA1, IHA2| rewrite IHA] ; auto.
Defined.

Hint Resolve rename_wf_eq. Hint Rewrite rename_wf_eq.

Lemma rename_wf_f : forall A eta,
  wf A -> wf (rename eta A).
Proof.
  intros; apply wf_ol_empty in H; apply empty_ol_wf; rewrite <- H; auto.
Defined.

Hint Resolve rename_wf_f.

Lemma rename_wf_c : forall De eta,
  wf_c De -> wf_c (rename_c eta De).
Proof.
  induction De; simpl; auto; intros.
  inversion H; apply wCons; auto using IHDe. 
Defined.

Lemma wf_c_wf : forall Ga A,
  IN_ctx A Ga -> (wf_c Ga) -> wf A.
Proof.
  induction Ga as [| B Ga]; intros; auto. 
  - inversion H. 
  - simpl in H; destruct (fml_dec A B); inversion H0; subst; auto. 
Defined.

Lemma wf_sub_ctx : forall Ga De,
  sub_ctx_pre Ga De -> wf_c De -> wf_c Ga.
Proof.
  induction Ga; intros; [apply wNil | apply wCons]. 
  - apply sub_cons_1 in H; apply IHGa with De; assumption. 
  - apply wf_c_wf with De; [apply H | idtac]; auto with datatypes.
Defined.

Hint Resolve rename_wf_c wf_c_wf wf_sub_ctx.

Lemma wf_fml_sub_name : forall x A, 
  wf (Forall x A) -> sub_name (ol A) (x :: nil).
Proof.
  intros; destruct (wf_ol_empty H); auto with datatypes. 
Defined.
