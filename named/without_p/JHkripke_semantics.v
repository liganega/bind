(** * Kripke Semantics *)

Set Implicit Arguments.

Require Import decidable_IN.
Require Import associations.
Require Import sublist.
Require Import language_syntax.
Require Import fresh_cst.
Require Import renaming_substitution.
Require Import LJT_and_weakening.

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

Fixpoint psem K (t:trm) (eta:assoc (domain K)){struct t} :
  domain K :=
  match t with
    | BVar x => match lookup eta x with
                    | Some u => u
                    | None => csts _ 0 (* fixed value *)
                  end
    | Cst c => csts _ c
    | App f t1 t2 => funs _ f (psem K t1 eta) (psem K t2 eta)
  end.


(** Forcing: The Kripke semantics is extended to all formulae *)

Reserved Notation "w ||- A {[ eta ]}" (at level 80).

Fixpoint force K (w: worlds K) (A : fml) eta {struct A} : Type :=
  match A with
    | Atom (p,t) => atoms K w (p, psem K t eta)
    | B --> C    => forall w', w <= w' -> 
                               w' ||- B {[eta]} -> w' ||- C {[ eta ]}
    | Forall y B => forall w', w <= w' ->
                    forall (d :domain K), w' ||- B {[(y, d) :: eta]}
  end
  
  where " w ||- A {[ eta ]} " := (force _ w A eta).

Notation "w ||- A {[ eta ]}" := (force _ w A eta) (at level 80).

(** Forcing is monotone w.r.t. the world relation. *)

Lemma mono_force : forall K (w w':worlds K) eta,
  w <= w' -> 
  forall (A:fml),
  w ||- A {[eta]} -> w' ||- A {[eta]}.
Proof.
  induction A as [ [p t] | | ]; simpl; intros.  
  - apply atoms_mon with (w:=w); auto. 
  - apply X0; eauto using wle_trans. 
  - apply X0; eauto using wle_trans. 
Defined.

(** ** Equivalence of associations *)

Definition assoc_equiv (A:Type) m (eta eta0:assoc A) :=
  forall x, x @ m
            -> eta ^^ x = eta0 ^^ x.

Definition st_assoc_equiv (A:Type) (eta eta0 : assoc A) :=
  forall x, eta ^^ x = eta0 ^^ x.

Hint Unfold assoc_equiv. Hint Unfold st_assoc_equiv.

Lemma assoc_equiv_comm : forall (A:Type) m (eta eta0:assoc A),
  assoc_equiv m eta eta0 ->
  assoc_equiv m eta0 eta.
Proof.
  firstorder using assoc_equiv.
Defined. 

Lemma st_assoc_equiv_comm : forall (A:Type) (eta eta0:assoc A),
  st_assoc_equiv eta eta0 ->
  st_assoc_equiv eta0 eta.
Proof.
  auto.
Defined.

Lemma assoc_equiv_cons : forall A m (eta eta0 : assoc A),
  assoc_equiv m eta eta0 ->
  forall x d,
    assoc_equiv (x::m) ((x, d) :: eta) ((x, d) :: eta0).
Proof.
  unfold assoc_equiv; intros; simpl; case_var; auto.
  eauto using neq_IN_cons.
Defined.

Lemma st_eq_0 : forall (A:Type) (eta eta0:assoc A),
  st_assoc_equiv eta eta0 ->
  forall m, assoc_equiv m eta eta0.
Proof.
  auto.
Defined.

Lemma st_eq_1 : forall (A:Type) (eta: assoc A) x t u,
  st_assoc_equiv ((x,t)::(x,u)::eta) ((x,t)::eta).
Proof.
  intros; intro; simpl; destruct (x0==x); auto.
Defined.

Lemma st_eq_2 : forall K (x y:name) (d e:domain K) eta,
 x <> y ->
 st_assoc_equiv ((x,d)::(y,e)::eta) ((y,e)::(x,d)::eta).
Proof.
  intros; intro; simpl; case_var; case_var; firstorder.
Defined.

Hint Resolve assoc_equiv_comm assoc_equiv_cons 
     st_assoc_equiv_comm st_eq_0 st_eq_1 st_eq_2.

(** A specified tactic for handling [assoc_equiv]. *)

Ltac solve_assoc :=
  let z := fresh "z" in
    let Hz := fresh "Hz" in
      intros z Hz; simpl in *; repeat case_var; intuition.

(** Semantics for well-defined terms/formulas is fixed. *)

Lemma psem_assoc_equiv : forall K eta eta0 m (t:trm),
  sub_name (bv_t t) m ->
  assoc_equiv m eta eta0 -> 
  psem K t eta = psem K t eta0.
Proof.
  induction t; simpl; intros; auto.
  - rewrite H0; auto.
    unfold sublist in H.
    apply H; simpl; destruct (n==n); try tauto.
  - assert (sub_name (bv_t t1) m).
    apply sub_appL with (bv_t t2); auto.
    assert (sub_name (bv_t t2) m).
    apply sub_appR with (bv_t t1); auto.
    rewrite IHt1, IHt2; auto.
Defined.

Lemma nil_assoc_eq : forall A (eta eta0 : assoc A),
  assoc_equiv nil eta eta0.
Proof.
intros; intro; intro.
destruct H.
Defined.

Hint Resolve nil_assoc_eq. Hint Rewrite nil_assoc_eq.

Lemma psem_term_assoc_indep : forall K eta eta' (t:trm),
 wf_t t -> psem K t eta = psem K t eta'.
Proof.
  intros; apply psem_assoc_equiv with nil; auto with datatypes.
  apply wf_t_bv_empty in H; rewrite H; auto.
Defined.

Lemma force_assoc_equiv : forall (A:fml) m K (w:worlds K) eta eta0,
  assoc_equiv m eta eta0 -> sub_name (bv A) m ->
  w ||- A {[eta]} ->
  w ||- A {[eta0]}.
Proof.
induction A as [ [p t] | |]; simpl; intros.
- rewrite psem_assoc_equiv with (eta0:=eta)(m:=m); auto.
- apply IHA2 with m eta; auto with datatypes.
  apply X; auto.
  apply IHA1 with m eta0; auto with datatypes.
- intros; simpl.
  assert (assoc_equiv (n :: m) ((n, d) :: eta) ((n, d) :: eta0)).
  apply assoc_equiv_cons; auto.
  apply mono_force with w; try apply X0.
  apply IHA with (m:=(n::m)) (eta:=((n,d)::eta)); try assumption.
  apply sub_rm_2; try assumption.
  apply X; apply wle_refl.
Defined.

Lemma force_st_assoc_equiv : forall (A:fml) K (w:worlds K) eta eta0,
  st_assoc_equiv eta eta0 ->
  w ||- A {[eta]} ->
  w ||- A {[eta0]}.
Proof.                
intros.
apply force_assoc_equiv with (m:=bv A) (eta:=eta); auto with datatypes.
Defined.

Lemma force_formula_assoc_indep : forall K (w:worlds K) eta eta' (A:fml),
  wf A ->
  w ||- A {[eta]} ->
  w ||- A {[eta']}.
Proof.
  intros.
  apply force_assoc_equiv with nil eta; auto with datatypes.  
  rewrite wf_bv_empty; auto.
Defined.

(** ** Forcing and substitution *)

Lemma psem_tsubst : forall (t:trm) x (u:trm) K eta,
  psem K t ((x, psem K u eta) :: eta) =
  psem K (t [[(x,u):: nil]]) eta.
Proof.
induction t.
- simpl.
  intros.
  destruct (n==x).
  reflexivity.
  simpl.
  destruct (eta ^^ n).
  reflexivity. 
  reflexivity.
- simpl.
  intros.
  reflexivity.
- simpl.
intros.
f_equal.
rewrite <- IHt1.
auto.
auto.
Defined.

Theorem force_subst : forall (A:fml) x (u:trm) K (w:worlds K) eta,
  wf_t u ->
  w ||- A {[(x, psem K u eta) :: eta]} ->
  w ||- (A [(x,u)::nil]) {[eta]}

with subst_force : forall (A:fml) x (u:trm) K (w:worlds K) eta, 
  wf_t u ->
  w ||- (A [(x,u)::nil]) {[eta]} ->
  w ||- A {[(x, psem K u eta) :: eta]}.
Proof.
+ destruct A as [ [p t] | A1 A2 | y A ].
  - simpl; intros; rewrite <- psem_tsubst; apply X.
  - simpl; intros; pose proof X w' X0.
    apply force_subst; try assumption.
    apply X2.
    clear X.
    apply subst_force; try assumption.
  - simpl; intros; destruct (y==x). 
    rewrite <- nil_subst.
    rewrite e in *.
    pose proof X w' X0 d.
    apply force_assoc_equiv with (m:=bv A)(eta:=(x,d)::(x,psem K u eta) :: eta).
    apply st_eq_0.
    apply st_eq_1.
    intro; intro; assumption.
    assumption.
    pose proof X w' X0 d.
    assert (w' ||- A {[(x,psem K u eta)::(y,d)::eta]}); try assumption.
    apply force_st_assoc_equiv with (eta:=((y,d)::(x,psem K u eta)::eta));
      try assumption.
    apply st_eq_2; try assumption.
    assert (psem K u eta = psem K u ((y,d)::eta)).
    rewrite psem_term_assoc_indep with (eta':=(y,d)::eta); 
      try reflexivity; try assumption.
    rewrite H0 in X2.
    apply force_subst; try assumption.
+ destruct A as [ [p t] | A1 A2 | y A ].
  - simpl; intros; rewrite psem_tsubst; apply X.
  - simpl; intros; pose proof X w' X0.
    apply subst_force; try assumption.
    apply X2.
    apply force_subst; try assumption. 
  - simpl; intros; destruct (y==x).
    pose proof X w' X0 d.
    rewrite e in *; clear e.
    rewrite <- nil_subst in X1.
    apply force_st_assoc_equiv with (eta:=(x,d)::eta).
    apply st_assoc_equiv_comm.
    apply st_eq_1.
    assumption.
    cut (w' ||- A{[(x,psem K u eta)::(y,d)::eta]}).
    apply force_st_assoc_equiv.
    apply st_eq_2.
    intro; apply n; symmetry; assumption.
    rewrite psem_term_assoc_indep with (eta':=(y,d)::eta); try assumption.
    apply subst_force with (eta:=((y,d)::eta)); try assumption.
    apply X; try assumption.
Defined.