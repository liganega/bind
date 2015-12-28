(** * Intuitionistic sequent calculus LJT *)

Set Implicit Arguments.

(* Require Import decidable_IN. *)
Require Import associations.
Require Import associations_extra.
Require Import language_syntax.
Require Import variable_sets.
Require Import substitution_wellformedness.
Require Import sublist.
Require Import fresh_name.
Require Import renaming.


(** For the presentation of predicate logic, we adopt sequent calculus
   to represent proofs. The advantage of such an approach is that
   it has an easy-to-define notion of normal form (it is merely
   the absence of the cut rule). A disadvantage is that it is less
   natural than the so-called natural deduction.

   The Gentzen-style sequent calculus [LJT] is obtained from the
   intuitionistic sequent calculus [LJ] by restricting the use of
   the left introduction rules of the implication and the universal
   quantification.

   Herbelin and Mints showed that there is a one-to-one correspondence
   between cut-free proofs in [LJT] and normal lambda-terms.
   This implies that LJT is a Curry-Howard-de Bruijn-style proof system. *)

Reserved Notation "Ga |- A" (at level 70).
Reserved Notation "Ga ;; A |- C" (at level 70, A at next level).


(** ** Prove and Well-Formedness *)

Inductive prove : context -> fml -> Type :=
  | ProofCont : forall (A C: fml) (Ga : context), 
    IN_ctx A Ga -> Ga ;; A |- C -> Ga |- C

  | ProofImplyR : forall B C Ga, 
    B :: Ga |- C -> Ga |- B --> C

  | ProofForallR : forall y (B : fml) Ga (a : name),
    a # op_c (B :: Ga) ->
    Ga |- open B y (Par a) -> 
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

  where " Ga ;; B |- A " := (prove_stoup Ga B A).

Notation "Ga |- A" := (prove Ga A) (at level 70).
Notation "Ga ;; A |- C" := (prove_stoup Ga A C) (at level 70, A at next level).

(** REMARKS:

   - All the formulae occurring in derivations are well-formed.
     This is possible because we can primarily focus on [formula = pformula nil].

   - The so-called [Exists-Fresh] style of quantification is used for the right
     universal quantification. *)

Lemma wf_prove : 
  forall Ga A, 
    Ga |- A -> wf_c Ga /\ wf A

    with wf_prove_stoup : 
  forall Ga A B, 
    Ga ;; A |- B -> wf_c Ga /\ (wf A /\ wf B).
Proof.
  (* wf_prove *)
  - induction 1.
    + cut (wf_c Ga /\ wf A /\ wf C); auto; tauto.
    + destruct IHprove as [H0 H1].  
      inversion H0; split; auto; auto using wImply. 
    + destruct IHprove; split; eauto using wForall.

  (* wf_prove_stoup *)
  - induction 1; auto.
    + destruct IHprove_stoup as [H1 H2]; destruct H2 as [H2 H3]; 
      repeat split; try apply wImply; auto. 
      destruct (wf_prove Ga B p); auto. 

    + repeat (split; try tauto); apply open_forall_wf with (u := u); 
      tauto.
Defined.

Hint Resolve wf_prove wf_prove_stoup.
Hint Rewrite wf_prove wf_prove_stoup.

(** ** Weakening *)

(** Simple structural induction on derication does not work.

   - This is a well-known issue about the [Exists-Fresh] style of quantification.

   - The [Exists-Fresh] style of quantification provides too _weak_ an induction principle.

   - We suggest a solution to that issue using simultaneous [renaming].

   - No alpha-conversion is necessary. *)

(** Generalized Weakening Lemma  *)

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
    + apply ProofCont with (rename eta A).
      * apply rename_IN_ctx; auto with datatypes. 
      * apply weakening_stoup_gen with Ga; assumption.
    + apply ProofImplyR.
      change (rename_c eta (B :: De) |- rename eta C);
      apply weakening_gen with (B :: Ga); auto.
      * auto using sub_cons_3.
      * apply wf_prove in H1; destruct H1 as [HL HR]. apply wCons; auto. 
        apply wf_c_wf with (B :: Ga); auto with datatypes. 
    + set (a0 := new
                   ((a::nil) ++ op_c De ++ op B ++
                             op_c (rename_c eta De) ++ 
                             op (Forall y (rename eta B)) ++
                             dom eta ++ image eta ++
                             op (Forall y B) ++ op_c Ga)).

      simpl in n; destruct_notin.
      assert (a0 <> a).
      * contradict H4; subst; apply IN_eq.
      * { rewrite <- context_rename_fresh with (a:=a)(a0:=a0); auto.
          set (De0 := rename_c ((a,a0) :: nil) De).
          rewrite <- rename_fresh with (a:=a0)(a0:= eta ** a); auto.
          apply ProofForallR with a0. 
          - simpl ; apply notIN_app_2; try assumption;
            [ apply notIN_op_rename | apply notIN_op_rename_c]
            ; congruence.
          - rewrite <- rename_c_fresh with (a:=a) (a0:=a0); auto.
            + rewrite <- rename_fresh with (a:=a) (a0:=a0); auto.
              set (eta0:= (a, a0) :: (a0, eta ** a) :: eta). unfold open.
              assert (HH :  ((y, (Par a0)):: nil)= (rename_a eta0 ((y, Par a) :: nil))).
            subst eta0; simpl; case_var; subst; auto; intuition.
            {rewrite HH. rewrite <- rename_subst.
             - apply weakening_gen with Ga; auto. 
               + apply sub_ctx_fresh_cst; assumption. 
               + apply (rename_wf_c ((a, a0) :: nil) H0).
             - apply wf_fml_sub_name. apply open_forall_wf with (u:= Par a). 
               destruct (@wf_prove Ga (open B y (Par a)) H1); auto. 
            }
            + subst De0; change a0 with (nil ** a0); 
              apply notIN_op_rename_c; auto; tauto.
        }

  (* stoup part  *)
  - destruct 3.
    + apply ProofAxiom.
      * apply rename_wf_c; assumption.  
      * apply rename_wf_f; assumption. 

    + apply ProofImplyL; eauto. 
    + simpl; apply ProofForallL with (u:=(rename_t eta u)).
      * auto using rename_wf_t. 
      * { unfold open;
          replace ((y, (rename_t eta u)) :: nil) 
                      with (rename_a eta ((y,  u) :: nil)).  
          - rewrite <- rename_subst; eauto. change (dom ((y, u) :: nil)) with (y:: nil). 
            apply wf_fml_sub_name; apply open_forall_wf with u. 
            destruct (@wf_prove_stoup Ga (open B y u) C H1); tauto.
          - tauto.
        }
Defined.

Lemma weakening : forall Ga De A,
  sub_ctx_pre Ga De -> 
  wf_c De ->
  Ga |- A ->
  De |- A.
Proof.
  intros.
  rewrite <- (rename_c_nil De); rewrite <- (rename_nil A).
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
  rewrite <- (rename_nil A);
  rewrite <- (rename_nil C).
  eauto using weakening_stoup_gen.
Defined.

(** Renaming Lemma *)

Lemma renaming_lamma : forall Ga A eta,
  Ga |- A ->
  rename_c eta Ga |- rename eta A.
Proof.
  intros. apply weakening_gen with Ga; auto. 
  apply (@wf_prove Ga A); assumption.
Defined.

Lemma renaming_stoup : forall Ga A C eta,
  Ga ;; A |- C ->
  rename_c eta Ga ;; rename eta A |- rename eta C.
Proof.
  intros; apply weakening_stoup_gen with Ga; 
  auto; unfold sublist; apply (@wf_prove_stoup Ga A C H); auto.
Defined.

