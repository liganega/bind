(** * Associations_extra *)

(** * In this file, we consider the lemmas related with assoc_rm (denoted by ^-) 
which removes the element from the given association. 
assoc_rm is strongly used for Forall fml. *)

Require Import associations.

Set Implicit Arguments. 

(** assoc_rm A x rho = rho \ {(x,_)} *)

Fixpoint assoc_rm (A : Type)(rho : assoc A)(x : name) {struct rho} : assoc A :=
  match rho with
    | nil           => nil
    | (y,t) :: rho' => if x == y then assoc_rm rho' x
                       else (y,t) :: assoc_rm rho' x
  end.

Notation " rho ^- x " := (@assoc_rm _ rho x) (at level 60).

Lemma assoc_rm_self : forall A (rho : assoc A) x, 
                        (rho ^-x) ^^ x = None.
Proof. 
  induction rho as [| [y t]]; auto; simpl; intros.
  - case_var; auto. 
    + simpl; case_var; intuition.
Defined.

Lemma assoc_neq : forall A x y u (rho rho' : assoc A), 
                    x <> y ->
                    (rho ++ (y,u) :: rho') ^^ x = (rho ++ rho') ^^ x.
Proof.
  induction rho; intros; 
  [rewrite! app_nil_l; rewrite <-fun_assoc_neq
  | destruct a as (y0, a0); simpl; case_var
  ]; 
  auto.  
Defined.

Lemma empty_dom : forall A (x : name), x # dom (@nil (name *A)). 
Proof. 
  unfold not; intros ? ? H; inversion H.
Defined.


Lemma in_dom_neq :
  forall A (rho : assoc A) x y u, 
    x <> y ->
    x @ dom ((y,u)::rho) -> x @ dom rho.
Proof.
  intros. change (dom ((y, u) :: rho)) with ( y :: (dom rho)) in H0.
  apply neq_IN_cons with (a:=y); auto. 
Defined.

Lemma rm_dom : 
  forall A (rho : assoc A) x, 
    dom (rho ^- x) = remove eqdec x (dom rho). 
Proof.
  induction rho as [| [y t] rho]; auto; simpl; intros. 
  case_var; auto. 
  rewrite <- IHrho; simpl; auto. 
Defined. 

Lemma in_dom_neq_rm : 
  forall A (rho : assoc A) x y, 
    x <> y ->
    x @ dom rho -> x @ dom (rho ^- y).
Proof.
  intros. rewrite rm_dom.
  apply IN_rm_2;auto.
Defined.

Lemma not_in_dom :
  forall A x (rho : assoc A), 
    x # dom (rho ^- x).
Proof.
  intros. rewrite rm_dom; apply notIN_rm_1.
Defined.

Lemma rm_rm : 
  forall A x (rho : assoc A), 
    rho ^- x = (rho ^-x) ^- x.
Proof.
  induction rho as [| [y t] rho]; simpl; auto. 
  case_var; auto.
  simpl. destruct (x == y); intuition. rewrite <- IHrho; auto.
Defined.

Lemma rm_neq_rm : 
  forall A x y (rho : assoc A), 
    x <> y ->
    (rho ^- y) ^- x = (rho ^- x) ^- y.
Proof.
  induction rho as [| [z t] rho]; auto; simpl; intros. 
  case_var.  
  - rewrite IHrho; auto.
    case_var; auto; simpl; case_var; intuition. 
  - case_var; auto; simpl.
    + case_var; auto; rewrite IHrho; intuition.
    + do 2 (case_var; intuition). f_equal; auto. 
Defined.

Lemma rm_neq_rm_r : 
  forall A (rho rho' : assoc A) x y u, 
    x <> y ->
    (rho++(y,u)::rho') ^- x = rho ^- x ++ (y, u) :: rho' ^- x.
Proof.
  induction rho as [_ | [z t] rho]; auto; simpl; intros. 
  - case_var; intuition.
  - case_var; rewrite IHrho; auto. 
Defined.

Lemma rm_change : 
  forall A (rho : assoc A) x y u, 
    x <> y ->
    ((y,u)::rho) ^- x = (y, u) :: rho ^- x.
Proof.
  intros. 
  apply rm_neq_rm_r with (rho:=nil) (rho' := rho); auto. 
Defined.

Lemma rm_eq : 
  forall A (rho : assoc A) x y u, 
    x = y ->
    ((y,u)::rho) ^- x = rho ^- x.
Proof.
  intros; simpl; case_var; intuition.
Defined.


Lemma rm_r : 
  forall A x (rho rho' : assoc A),
    (rho ++ rho') ^- x = rho ^- x ++ rho' ^- x.
Proof.
  induction rho as [| [y t] rho]; auto; simpl; intros; case_var; auto. 
  rewrite IHrho. rewrite app_comm_cons; auto.
Defined.

Lemma assoc_rm_neq : 
  forall A (rho : assoc A) x y, 
    x <> y -> 
    rho ^^ x = (rho ^- y) ^^ x.
Proof.
  induction rho as [_| [z t] rho]; auto; intros. 
  destruct (y==z). 
  - subst; rewrite rm_eq with (x:=z) (y:=z); auto. rewrite <- IHrho; auto.
    rewrite <- fun_assoc_neq; auto.
  - rewrite rm_change; auto. 
    destruct (x == z). 
    + subst; rewrite! fun_assoc_eq; auto. 
    + rewrite <- fun_assoc_neq; [rewrite <- fun_assoc_neq | idtac]; auto.
Defined.


Lemma rm_eq_r : 
  forall A (rho rho' : assoc A) x y u, 
    x = y ->
    (rho++(y,u)::rho') ^- x = rho ^- x ++ rho' ^- x.
Proof.
  intros; subst; rewrite rm_r; f_equal; rewrite <- rm_eq with (rho:=rho') (y:=y) (u:=u); auto.
Defined.


Hint Rewrite <- assoc_rm_neq : assoc_rmi.
