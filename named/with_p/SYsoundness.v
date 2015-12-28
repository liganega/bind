(** * Soundness of LJT w.r.t. Kripke Semantics *)

Set Implicit Arguments.

Require Import sublist.
Require Import language_syntax.
Require Import variable_sets.
Require Import substitution_wellformedness.
Require Import fresh_name.
Require Import renaming.
Require Export LJT_and_weakening.
Require Export kripke_semantics.

(** The soundness of [LJT] with respect to Kripke semantics
   is relatively simple.

   If we had included parameters (free variables), the soundness
   proof of [LJT] would be a simple simultaneous induction
   on the derivation, cf. with_FreeVar_soundness.v.

   However, because we use constants instead, the case
   [ProofForallR] requires more attention. *) 

(** ** Some auxiliary predicates and operations *)

(** A predicate checking that a property holds for all elements
   of a list. *)

Inductive list_forall (A:Type)(P:A -> Type) : list A -> Type :=
| ForallNil  : list_forall P nil
| ForallCons : forall a l, 
               P a -> list_forall P l -> list_forall P (cons a l).

Definition force_ctx K (w:worlds K) rho eta Ga :=
  list_forall (fun B : fml => w ||- B {[rho, eta]}) Ga.

Lemma force_IN_ctx : forall K (w:worlds K) rho eta Ga,
  force_ctx K w rho eta Ga ->
  forall A,
    IN_ctx A Ga ->
    w ||- A {[rho, eta]}.
Proof.
  induction 1 as [ | B]; simpl; intros A; [ intro Hnil; elim Hnil | intro Hcons ].
  destruct (fml_dec A B); subst; auto.
Qed.

Lemma force_ctx_fresh_par : forall Ga K (w:worlds K) a d rho eta,
  force_ctx K w rho eta Ga ->
  a # op_c Ga ->
  force_ctx K w ((a,d) :: rho) eta Ga.
Proof.
  unfold force_ctx; induction 1; simpl; intros; destruct_notin; constructor;
  eauto using force_fresh_parL.
Qed.

Lemma list_force_assoc_equiv : forall Ga K (w:worlds K) rho eta eta0,
  wf_c Ga ->
  list_forall (fun B : fml => wf B -> w ||- B {[rho, eta]}) Ga ->
  list_forall (fun B : fml => wf B -> w ||- B {[rho, eta0]}) Ga.
Proof.
  induction 2;
  [constructor 
  | apply ForallCons; 
    [ intro wfa; apply force_fml_assoc_indep with (eta:=eta) 
    | apply IHX ; inversion H]; auto]. 
Qed.

(** Forcing is monotone wrt. the world relation. *)

Lemma mono_force_ctx : forall K (w w':worlds K),
  w <= w' -> 
  forall rho eta (Ga:context), 
    force_ctx K w rho eta Ga ->
    force_ctx K w' rho eta Ga.
Proof.
  induction 2 as [| B]; constructor; eauto using mono_force.
Qed.

(** ** Soundness *)

Theorem soundness : forall Ga A,
  Ga |- A ->
    forall K (w:worlds K) rho,
      list_forall (fun B => w ||- B {[rho, nil]}) Ga ->
      w ||- A {[rho, nil]}

with soundness_stoup : forall Ga A C,
  Ga ;; A |- C ->
    forall K (w:worlds K) rho,
      list_forall (fun B => w ||- B{[rho, nil]}) Ga ->
      w ||- A {[rho, nil]}
      -> w ||- C {[rho, nil]}.
Proof.
  (* soundness *)
  - { destruct 1; simpl; intros. 
      - apply soundness_stoup with (Ga:=Ga)(A:=A); auto. 
        eauto using force_IN_ctx.
      - apply soundness with (Ga:= B::Ga); auto.
        apply ForallCons; auto.
        apply mono_force_ctx with (w:=w); assumption.
      - apply force_assoc_equiv with (eta := (y,d)::nil) (m:=(ol B));
        auto with datatypes. 
        simpl in n; destruct_notin.
          cut
              (w' ||- B {[(a,d)::rho, (y, psem K (Par a) ((a,d)::rho) nil) :: nil]}).
          *  simpl; intro; case_var;
             [ apply force_fresh_parR with (a:= a)(d:=d); auto
             | congruence].

          * { apply subst_force; auto.
              - apply wPar. 
              - apply soundness with Ga; auto.
                    apply mono_force_ctx with (w:=w); auto;
                      apply force_ctx_fresh_par; auto;
                        apply list_force_assoc_equiv with eta; assumption.
  }
}
  (* soundness_stoup *)
  - { destruct 1; simpl; intros; auto.
     - apply soundness_stoup with (Ga:=Ga)(A:=C); auto.
        apply X0;
          [ apply wle_refl
            | apply soundness with Ga; auto
          ].
     - apply soundness_stoup with
        (Ga := Ga) (A := ( open B y u )); auto; 
       apply force_assoc_equiv with (m:= nil)(eta := nil); auto.
       + destruct (wf_prove_stoup H); destruct H1 as [H1 H2];
         destruct (wf_ol_empty H1); auto with datatypes. 
       + apply force_subst; auto;
         apply force_assoc_equiv with
         (m:= ol B) (eta:= (y, psem K u rho nil) :: nil); 
         auto with datatypes; apply X0; apply wle_refl. 
    }
Qed.
