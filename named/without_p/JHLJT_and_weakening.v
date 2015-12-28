Set Implicit Arguments.

Require Import decidable_IN.
Require Import associations.
Require Import sublist.
Require Import language_syntax.
Require Import fresh_cst.
Require Import renaming_substitution.

(** * Intuitionistic sequent calculus LJT *)

(** For the presentation of predicate logic, we adopt Gentzen-style
  sequent calculus to represent proofs. An advantage is that it has an
  easy-to-define notion of normal form. A proof is in normal form
  merely when no cut rule is used during the proof. 

  The Gentzen-style sequent calculus LJT is obtained from the
  intuitionistic sequent calculus LJ by restricting the use of the
  left introduction rules of the implication and the universal
  quantification.  

  In our formalization, proof terms do not belong to the domain of the
  discourse, and correspondingly, derivability is defined as a
  predicate. *)

Reserved Notation "Ga |- A" (at level 70).
Reserved Notation "Ga ;; A |- C" (at level 70, A at next level).

Inductive prove : context -> fml -> Type :=
  | ProofCont : forall (A C: fml) (Ga : context), 
    IN_ctx A Ga -> Ga ;; A |- C -> Ga |- C

  | ProofImplyR : forall B C Ga, 
    B :: Ga |- C -> Ga |- B --> C

  | ProofForallR : forall y (B : fml) Ga (a : name),
    a # oc_c (B :: Ga) ->
    Ga |- open B y (Cst a) -> 
    Ga |- (Forall y B)

  where "Ga |- A" := (prove Ga A)

with prove_stoup : context -> fml -> fml -> Type :=
  | ProofAxiom Ga C: wf_c Ga -> wf C -> Ga ;; C |- C

  | ProofImplyL Ga D : forall B C, 
    Ga |- B -> Ga ;; C |- D -> Ga ;; (B --> C) |- D

  | ProofForallL Ga C : forall y (u : trm) (B : fml), 
    wf_t u ->
    Ga ;; open B y u |- C ->
    Ga ;; Forall y B |- C

  where "Ga ;; A |- C" := (prove_stoup Ga A C).

Notation "Ga |- A" := (prove Ga A) (at level 70).
Notation "Ga ;; A |- C" := (prove_stoup Ga A C) (at level 70, A at next level).

(** All the formulas occurring in derivations are well-formed.

  The so-called [Exists-Fresh] style of quantification is used for the
  right universal quantification. The same explanation for [wf] can be
  made here too. *)  

Lemma wf_prove : forall Ga A, 
    Ga |- A -> wf_c Ga /\ wf A
with wf_prove_stoup : forall Ga A B, 
    Ga ;; A |- B -> wf_c Ga /\ (wf A /\ wf B).
Proof.
  - induction 1.
    + cut (wf_c Ga /\ wf A /\ wf C).
      * tauto.
      * apply wf_prove_stoup; assumption.
    + inversion IHprove; inversion H0; split; auto; apply wImply; auto.
    + destruct IHprove; split; eauto.
  - induction 1.
    + tauto.
    + cut (wf B).
      * intros. destruct IHprove_stoup; split. 
        destruct H2; eauto; split; eauto. 
        destruct H2; split; eauto. 
        apply wImply; auto.
      * {cut (wf_c Ga /\ wf B).
         - tauto.
         - apply wf_prove; assumption.
        }
    + repeat (split; try tauto). 
      apply open_forall_wf with (u := u); tauto.
Defined.

Hint Resolve wf_prove wf_prove_stoup.
Hint Rewrite wf_prove wf_prove_stoup.

(** ** Weakening *)

(** Weakening cannot be proved by a simple structural induction on
  derivation does not work. This is a well-known issue about the
  [Exists-Fresh] style of quantification because it provides _too
  weak_ an induction principle. 

  We suggest a solution to that issue using simultaneous renaming
  because Weakneing is a special case of the following general
  lemma which is a combination of weakening and renaming. *) 

Lemma weakening_gen : forall Ga De A eta,
    sub_ctx_pre Ga De -> 
    wf_c De ->
    Ga |- A ->
          rename_c eta De |- rename eta A

with weakening_stoup_gen : forall Ga De A C eta,
    sub_ctx_pre Ga De ->
    wf_c De ->
    Ga ;; A |- C ->
               rename_c eta De ;; rename eta A |- rename eta C.
Proof.
  - destruct 3; simpl.
    * apply ProofCont with (rename eta A).
      apply rename_IN_ctx; apply H; assumption.
      apply weakening_stoup_gen with Ga; assumption.
    * apply ProofImplyR;
      change (rename_c eta (B :: De) |- rename eta C);
      apply weakening_gen with (B :: Ga); try apply sub_cons_3;
      try assumption.
      apply wCons; try assumption.
      destruct (@wf_prove (B :: Ga) C H1).
      inversion H2; auto.
    * set (a0 := new
                   ((a::nil) ++ oc_c De ++ oc B ++
                             oc_c (rename_c eta De) ++
                             oc (Forall y (rename eta B)) ++
                             dom eta ++ img eta ++
                             oc (Forall y B) ++ oc_c Ga)).
      simpl in n. destruct_notin.
      assert (a0 <> a).
      contradict H4; simpl. destruct (a0==a); try tauto.
      rewrite <- context_rename_fresh with (a:=a) (a0:=a0);
        try assumption. 
      set (De0 := rename_c ((a,a0) :: nil) De).
      rewrite <- rename_fresh with (a:=a0)(a0:=eta ** a);
        try assumption.
      apply ProofForallR with a0.
      simpl.
      apply notIN_app_2; try apply notIN_oc_rename;
      try apply notIN_oc_rename_c;
      try assumption; intro; apply H12; symmetry; assumption.
      rewrite <- rename_c_fresh with (a:=a)(a0:=a0);
        try apply notIN_oc_rename_c with (a0:=a)(Ga:=De)(eta:=nil);
        try assumption; 
        simpl; try tauto.
      rewrite <-rename_fresh with (a:=a)(a0:=a0); try assumption.
      set (eta0 := (a,a0) :: (a0, eta ** a) :: eta).
      unfold open.
      replace ((y, Cst a0) :: nil)
      with (rename_a eta0 ((y, Cst a) :: nil)); 
        [ idtac | unfold eta0; simpl; destruct (a==a); try reflexivity; 
                  try destruct n; try reflexivity; clear e].
      rewrite <- rename_subst.
      apply weakening_gen with Ga;
        [ apply sub_ctx_fresh_cst; assumption 
        | apply rename_wf_c; assumption
        | assumption ].
      simpl.
      apply forall_wf_sub. 
      apply open_forall_wf with (u:=Cst a).
      cut (wf_c Ga /\ wf (open B y (Cst a))). tauto.
      apply wf_prove; assumption.
  - destruct 3.
    * apply ProofAxiom.
      apply rename_wf_c; auto.
      apply rename_wf_f; auto.
    * apply ProofImplyL; eauto.
    * simpl.
      pose proof ProofForallL.
      pose proof H2 (rename_c eta De) (rename eta C) y; clear H2.
      pose proof H3 (rename_t eta u) (rename eta B); clear H3.
      apply H2; clear H2.
      apply rename_wf_t; auto.
      assert (open (rename eta B) y (rename_t eta u) =
              rename eta (open B y u)).
      unfold open.
      pose proof rename_subst B ((y,u)::nil) eta.
      simpl in H2.
      symmetry.
      apply H2.
      pose proof wf_prove_stoup.
      pose proof H3 Ga (open B y u) C H1.
      assert (bv (open B y u)=nil).
      apply wf_bv_empty.
      apply H4.
      pose proof sub_q_open B y u.
      rewrite H5 in H6.
      apply sub_nil in H6.
      simpl in H6.
      apply sub_rm_2.
      rewrite H6; auto. 
      rewrite H2.
      apply weakening_stoup_gen with Ga; auto.
Defined.

Lemma weakening : forall Ga De A,
  sub_ctx_pre Ga De -> 
  wf_c De ->
  Ga |- A ->
  De |- A.
Proof.
  intros.
  rewrite <- (rename_c_nil De).
  rewrite <- (rename_nil A).
  apply weakening_gen with Ga; auto.
Defined.

Lemma weakening_stoup : forall Ga De A C,
    sub_ctx_pre Ga De ->
    wf_c De ->
    Ga ;; A |- C ->
    De ;; A |- C.
Proof.
  intros.
  rewrite <- (rename_c_nil De).
  rewrite <- (rename_nil A).
  rewrite <- (rename_nil C).
  eauto using weakening_stoup_gen.
Defined.

(** Renaming Lemma *)

Lemma renaming_lemma : forall Ga A eta,
  Ga |- A ->
  rename_c eta Ga |- rename eta A.
Proof.
  intros.
  assert (wf_c Ga); cut (wf_c Ga /\ wf A);
  try tauto; try apply wf_prove; auto.
  firstorder using weakening_gen.
Defined.

Lemma renaming_stoup : forall Ga A C eta,
  Ga ;; A |- C ->
  rename_c eta Ga ;; rename eta A |- rename eta C.
Proof.
  intros.
  assert (wf_c Ga); cut (wf_c Ga /\ wf A /\ wf C); try tauto;
  try apply wf_prove_stoup; auto.
  firstorder using weakening_stoup_gen.
Defined.

Hint Resolve weakening_gen weakening_stoup_gen weakening weakening_stoup 
             renaming_lemma renaming_stoup.

Hint Rewrite weakening_gen weakening_stoup_gen weakening weakening_stoup 
             renaming_lemma renaming_stoup.