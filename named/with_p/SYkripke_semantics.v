(** * Kripke Semantics *)

Set Implicit Arguments.

(* Require Import decidable_IN. *)
Require Import associations.
Require Import sublist.
Require Import language_syntax.
Require Import substitution_wellformedness.
Require Import variable_sets.
Require Import fresh_name.
Require Import LJT_and_weakening.
Require Import renaming.


(** ** Kripke Model *)

(** We use the conventional Kripke model adopted by Troelstra and van Dalen
   for the semantics of LJT.

   - A Kripke model is a tuple of a partially-ordered set of _worlds_, a domain,
     interpretations of constants and function symbols into the domain,
     and a binary relation between worlds and atomic sentences. *)

Record Kripke : Type := {
  worlds: Type;
  wle : worlds -> worlds -> Type;
  wle_refl : forall w, wle w w;
  wle_trans : forall w w' w'', wle w w' -> wle w' w'' -> wle w w'';
  domain : Type;
  csts : name -> domain;
  funs : function -> domain -> domain -> domain;
  atoms : worlds -> predicate * domain -> Type;
  atoms_mon : forall w w', wle w w' -> forall P, atoms w P -> atoms w' P
  }.

Notation "w <= w'" := (wle _ w w') (at level 70).

(** ** Semantics *)

(** Interpretation of a pseudo-term in a Kripke model using associations for variables.

   - The interpretation of pseudo-terms is made total by ignoring insignificant variables.

   - The being-in-a-list part of a term is simply ignored during the interpretation.

   - The trace relocation has no impact on the Kripke semantics. *)

Fixpoint psem K (t : trm) (rho: assoc (domain K)) (eta: assoc (domain K)){struct t} :
  domain K :=
  match t with
    | Ltr x  => match fun_assoc eta x with
                    | Some u => u
                    | None => csts _ 0 (* fixed value *)
                  end
    | Par y => match fun_assoc rho y with
                    | Some u => u
                    | None => csts _ 0 (* fixed value *)
                  end
    | Cst c => csts _ c
    | App f t1 t2 => funs _ f (psem K t1 rho eta) (psem K t2 rho eta)
  end.

(** Forcing: The Kripke semantics is extended to all formulae *)

Reserved Notation "w ||- A {[ rho , eta ]}" (at level 80).

Fixpoint force K (w: worlds K)  (A : fml) rho eta {struct A} : Type := 
  match A with
    | Atom (p,t) => atoms K w (p, psem K t rho eta)
    | B --> C    => forall w', w <= w' -> 
                    w' ||- B {[ rho, eta ]} -> w' ||- C {[rho, eta]}
    | Forall y B => forall w', w <= w' ->
                    forall (d :domain K), w' ||- B {[rho, (y, d) :: eta]}
  end
  
  where " w ||- A {[ rho , eta ]} " := (force _ w A  rho eta).

Notation "w ||- A {[ rho , eta ]}" := (force _ w A rho eta) (at level 80).

(** Forcing is monotone w.r.t. the world relation. *)

Lemma mono_force : forall K (w w':worlds K) rho eta,
  w <= w' -> 
  forall (A : fml),
    w ||- A {[rho, eta]} -> w' ||- A {[rho, eta]}.
Proof.
  induction A as [ [p t]| |]; simpl; intros; 
  [ apply atoms_mon with (w:=w)
  | apply X0
  | apply X0]; eauto using wle_trans.
Qed.

(** ** Equivalence of associations *)

Definition assoc_equiv (A:Type) m (eta eta0:assoc A) :=
  forall x, IN_name x m -> eta ^^ x = eta0 ^^ x.

Hint Unfold assoc_equiv.

Lemma assoc_equiv_comm : forall (A:Type) m (eta eta0:assoc A),
  assoc_equiv m eta eta0 ->
  assoc_equiv m eta0 eta.
Proof.
  firstorder using assoc_equiv.
Qed.

Lemma assoc_equiv_cons : forall (A: Type) m (eta eta0 : assoc A),
  assoc_equiv m eta eta0 ->
  forall x d,
    assoc_equiv (x :: m) ((x, d) :: eta) ((x, d) :: eta0).
Proof.
  unfold assoc_equiv; intros; simpl; case_var; auto.
  eauto using neq_IN_cons.
Qed.

Hint Resolve assoc_equiv_comm assoc_equiv_cons.

(** A specified tactic for handling [assoc_equiv]. *)

Ltac solve_assoc :=
  let z := fresh "z" in
    let Hz := fresh "Hz" in
      intros z Hz; simpl in *; repeat case_var; intuition.

(** Semantics for well-defined terms/formulas is fixed. *)

Lemma psem_assoc_equiv : forall K m eta eta0 rho (t:trm),
  sub_name (ol_t t) m-> 
  assoc_equiv m eta eta0 -> 
  psem K t rho eta = psem K t rho eta0.
Proof.
  induction t; intros H ?; simpl in H; simpl; auto.
  - rewrite H0; auto with datatypes. 
  - f_equal; auto with datatypes. 
Qed.

Lemma wf_t_ol_t_empty : forall t : trm, 
  wf_t t -> ol_t t = nil.
Proof.
  induction t; simpl; intros; auto;  
  [ inversion H
  | rewrite IHt1, IHt2; auto with datatypes; inversion_clear H; auto]. 
Qed.    

Lemma psem_term_assoc_indep : forall K eta eta0 rho (t:trm),
  wf_t t -> 
  psem K t rho eta = psem K t rho eta0.
Proof.
  intros; apply psem_assoc_equiv with (m:=nil); 
  [ rewrite wf_t_ol_t_empty; auto with datatypes
  | unfold assoc_equiv; intros ? H0; inversion H0].
Qed.

Lemma force_assoc_equiv : forall (A:fml) m K (w:worlds K) rho eta eta0,
  sub_name (ol A) m ->
  assoc_equiv m eta eta0 -> 
  w ||- A {[rho , eta]} ->
  w ||- A {[rho, eta0]}.
Proof.
  induction A as [ [p t]| | y A]; simpl; intros. 
  -  rewrite psem_assoc_equiv with (eta0:=eta0)(m:=m) in X; auto.
  -  apply IHA2 with (m:=m) (eta:=eta) ; eauto with datatypes.
  -  apply mono_force with (w:=w); try assumption. 
     apply IHA with (m:=(y::m))  (eta := (y,d)::eta); auto with datatypes. 
     apply X; auto; apply wle_refl. 
Qed.

Lemma force_fml_assoc_indep : forall K (w:worlds K) rho eta eta0 (A:fml),
  wf A ->
  w ||- A {[rho , eta]} ->
  w ||- A {[rho , eta0]}.
Proof.
  intros; apply force_assoc_equiv with (m:=nil : list name) (eta :=eta); 
  try firstorder; rewrite wf_ol_empty; auto. 
Qed.


(** Fresh parameters have no impact on semantics. *)

Lemma psem_fresh_par : forall  (t:trm) K a d rho eta,
  a # op_t t ->
  psem K t rho eta =  psem K t ((a,d)::rho) eta.
Proof.
  induction t; simpl; intros; auto;
    [ repeat case_var; intuition congruence
    | destruct_notin; f_equal; auto
    ].
Qed.

Lemma force_fresh_parL : forall (A: fml) K (w:worlds K) a d rho eta,
  w ||- A {[rho, eta]} ->
  a # op A ->
  w ||- A {[(a,d) :: rho, eta]}

  with force_fresh_parR : forall (A:fml) K (w:worlds K) a d rho eta,
    w ||- A {[(a,d) :: rho, eta]} ->
    a # op A ->
    w ||- A {[rho, eta]}.
Proof.
  - induction A as [ [p t]| | ]; simpl; intros;
    [ rewrite <- psem_fresh_par
    | destruct_notin
    | idtac
    ]; eauto.  

  - induction A as [ [p t]| | ]; simpl; intros;
    [ rewrite <- psem_fresh_par in *; auto
      | destruct_notin; eauto
      | eauto
    ].
Qed.

Lemma psem_tsubst : forall (t:trm) x (u:trm) K rho eta,
  psem K t rho ((x, psem K u rho eta) :: eta) =
  psem K (t [[nil, (x,u):: nil]]) rho eta.
Proof.
  induction t; simpl; intros; auto.
  - case_var; auto. 
  - f_equal; auto. 
Qed.


Definition wo_list_assoc_equiv (A : Type) (zeta zeta0: assoc A):= 
  forall z, zeta ^^ z = zeta0 ^^z.

Proposition lem0: forall (A : Type) (zeta zeta0 : assoc A), 
  wo_list_assoc_equiv zeta zeta0 -> 
  forall m, assoc_equiv m zeta zeta0.
Proof.
  intros; auto.  
Qed. 

Proposition lem1 : forall (B: fml) K0 (w0 : worlds K0) rho zeta zeta0,
  wo_list_assoc_equiv zeta zeta0 ->
  w0 ||- B {[rho, zeta]} -> w0 ||- B {[rho, zeta0]}.
Proof. 
  intros;
  apply force_assoc_equiv with (eta:= zeta) (m:=ol B); auto. 
Qed.


Theorem force_subst : forall (A : fml) x (u : trm) K (w:worlds K) rho eta,
  wf_t u ->   
  w ||- A {[rho , (x, psem K u rho eta) :: eta]} ->
  w ||- (A [nil , (x,u)::nil]) {[rho, eta]}

with subst_force : forall (A: fml) x (u : trm) K (w:worlds K) rho eta, 
  wf_t u ->
  w ||- (A [nil, (x,u)::nil]) {[rho, eta]} -> 
  w ||- A {[rho, (x, psem K u rho eta) :: eta]}.
Proof.
  (* force_subst *)
  - induction A as [ [p t] | A1 A2 | y A ]; simpl; intros.
    + rewrite <- psem_tsubst; assumption. 
    + apply force_subst; auto; apply X; auto; 
      apply subst_force with (l:=l); auto.
    + case_var.
      * rewrite <- nil_subst; 
        apply force_assoc_equiv with (m:=(ol A)) (eta:=((x, d) :: (x, psem K u rho eta) :: eta)); auto ; solve_assoc.

      * apply force_subst; auto. 
        destruct (x==y); [ contradict n| idtac]; auto. 

        rewrite psem_term_assoc_indep with (eta0 := eta); auto.

        apply lem1 with (zeta:= ((y, d) :: (x, psem K u rho eta) :: eta)); 
        [intro z; unfold wo_list_assoc_equiv; simpl;   
         repeat case_var; intuition try congruence 
        | apply X, X0]. 

  (* subst_force *)
  - induction A as  [ [p t] | A1 A2 | y A ]; simpl; intros.
    + rewrite <- psem_tsubst in X; assumption.
    + apply subst_force; auto.
    + case_var. 
      * apply force_assoc_equiv with (m:= ol A)(eta := (x, d) :: eta); auto. 
        solve_assoc. 
        replace ( w' ||- A {[rho, (x, d) :: eta]} ) with (w' ||-  A [nil, nil] {[rho, (x, d) :: eta]}). 
        apply X, X0. rewrite <- nil_subst; auto. 
        
      * apply lem1 with (zeta := (x, psem K u rho eta) :: (y, d) :: eta). 
        intro z; unfold wo_list_assoc_equiv;  auto ; simpl; 
        repeat case_var; intuition try congruence. 
        rewrite psem_term_assoc_indep with (eta0 := ((y, d):: eta)); auto.   
Qed.
