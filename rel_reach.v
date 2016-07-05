Add LoadPath "somePath".

Require Export genBES.

(*----------relation inductions----------*)

Definition max_rel (l1 l2:list booleanEquation)(a b:nat):Prop:=
  (bnd_block l1 a /\ bnd_block l2 b).

Definition relates_bound (R:propVar_relation) (l1 l2:list booleanEquation):=
  (forall x y:nat, R x y -> (bnd_block l1 x /\ bnd_block l2 y)).

Axiom relates_decidable : forall R:propVar_relation, forall l1 l2:list booleanEquation, 
  relates_bound R l1 l2 -> forall x y:nat, {R x y}+{~R x y}.

Lemma empty_relation_relates_bound : forall E:list booleanEquation, relates_bound empty_relation E E.
Proof.
intros;intro;intros.
inversion H.
Qed.

Inductive reachable (R:propVar_relation) : propVar -> propVar -> Prop:=
| single_path (x y:propVar): R x y -> reachable R x y
| step_path (x z:propVar):forall y:propVar, R x y -> reachable R y z -> reachable R x z.

Lemma reachable_exists_to : forall R:propVar_relation, forall x z:propVar, 
  reachable R x z -> exists y:propVar, R y z.
Proof.
intros.
induction H.
exists x;auto.
destruct IHreachable.
exists x0;auto.
Qed.

Lemma reachable_exists_from : forall R:propVar_relation, forall x z:propVar, 
  reachable R x z -> exists y:propVar, R x y.
Proof.
intros.
induction H.
exists y;auto.
exists y;auto.
Qed.

Lemma reachable_trans : forall R:propVar_relation, forall x y z:propVar, reachable R x y -> 
  reachable R y z -> reachable R x z.
Proof.
intros.
induction H.
apply (step_path _ _ _ y);auto.

apply (step_path _ _ _ y);auto.
Qed.

Lemma reachable_maintains_relates_bound : forall e1 e2:list booleanEquation, forall R:propVar_relation, 
  relates_bound R e1 e2 -> relates_bound (reachable R) e1 e2.
Proof.
intros;intro;intros.
destruct (reachable_exists_to _ _ _ H0).
destruct (reachable_exists_from _ _ _ H0).
destruct (H _ _ H1).
destruct (H _ _ H2).
split;auto.
Qed.

Lemma reachable_dec_b : forall e1 e2:list booleanEquation, forall R:propVar_relation, 
  relates_bound R e1 e2 -> forall x y:propVar, {reachable R x y} + {~(reachable R x y)}.
Proof.
intros.
assert (relates_bound (reachable R) e1 e2).
  apply reachable_maintains_relates_bound;auto.
destruct (relates_decidable _ _ _ H0 x y).
left;assumption.
right;assumption.
Qed.

Definition minimal_environment_for_var (R:propVar_relation)(e1 e2:list booleanEquation)
    (H:relates_bound R e1 e2)(x:propVar):environment:=
  fun (a:propVar) => if reachable_dec_b e1 e2 R H x a then true else beq_nat x a.

Lemma minimal_environment_for_var_consistent : forall R:propVar_relation, forall e1 e2:list booleanEquation, 
  forall H:relates_bound R e1 e2, forall x:propVar, 
    consistent_environment (minimal_environment_for_var R e1 e2 H x) R.
Proof.
intros.
intro;intros.
destruct (eq_nat_decide x0 y).
rewrite (eq_nat_eq _ _ e) in *.
assumption.
unfold minimal_environment_for_var in *.
destruct y.
destruct (reachable_dec_b e1 e2 R H x 0);auto.
destruct x0.
exfalso.
apply n.
apply eq_nat_is_eq;auto.
destruct (reachable_dec_b e1 e2 R H x (S x0));auto.
exfalso.
apply n0.
apply (reachable_trans _ _ (S x0));auto.
apply single_path;auto.
apply beq_nat_true_iff in H1.
rewrite H1 in *.
exfalso.
apply n0.
apply single_path;auto.
destruct (reachable_dec_b e1 e2 R H x (S y));auto.
destruct x0.
destruct (reachable_dec_b e1 e2 R H x 0).
exfalso.
apply n0.
apply (reachable_trans _ _ 0);auto.
apply single_path;auto.
apply beq_nat_true_iff in H1.
rewrite H1 in *.
exfalso.
apply n0.
apply single_path;auto.
destruct (reachable_dec_b e1 e2 R H x (S x0)).
exfalso.
apply n0.
apply (reachable_trans _ _ (S x0));auto.
apply single_path;auto.
apply beq_nat_true_iff in H1.
rewrite H1 in *.
exfalso.
apply n0.
apply single_path;auto.
Qed.

Lemma minimal_environment_for_var_self : forall R:propVar_relation, forall e1 e2:list booleanEquation, 
  forall H:relates_bound R e1 e2, forall x:propVar, minimal_environment_for_var R e1 e2 H x x.
Proof.
intros.
unfold minimal_environment_for_var.
destruct x.
destruct (reachable_dec_b e1 e2 R H 0 0);auto.
destruct (reachable_dec_b e1 e2 R H (S x) (S x));auto.
apply beq_nat_true_iff;auto.
Qed.

Lemma min_env_rel_cons : forall e1 e2:list booleanEquation, forall R:propVar_relation, 
  forall H:relates_bound R e1 e2, forall x y:propVar, 
    rel_cons R (var x) (var y) -> minimal_environment_for_var R e1 e2 H x y.
Proof.
intros e1 e2 R H x y H1.
destruct (eq_nat_decide x y).
rewrite (eq_nat_eq _ _ e) in *.
destruct y;unfold minimal_environment_for_var.
destruct (reachable_dec_b e1 e2 R H 0 0);auto.
destruct (reachable_dec_b e1 e2 R H (S y) (S y));auto.
apply beq_nat_true_iff;auto.
assert (x <> y).
  intro.
  apply n.
  apply eq_nat_is_eq;auto.

apply H1.
apply minimal_environment_for_var_consistent;auto.
apply minimal_environment_for_var_self;auto.
Qed.

Lemma reachable_if_min_env : forall e1 e2:list booleanEquation, forall R:propVar_relation, 
  forall H:relates_bound R e1 e2, forall x y:propVar, x<>y -> 
    minimal_environment_for_var R e1 e2 H x y -> reachable R x y.
Proof.
intros.
unfold minimal_environment_for_var in H1.
destruct (reachable_dec_b e1 e2 R H x y);auto.
exfalso.
apply beq_nat_true_iff in H1;auto.
Qed.

Lemma rel_cons_min_env : forall e1 e2:list booleanEquation, forall R:propVar_relation, 
  forall H:relates_bound R e1 e2, forall x y:propVar, 
    minimal_environment_for_var R e1 e2 H x y -> rel_cons R (var x) (var y).
Proof.
intros.
intro;intros.
destruct (eq_nat_decide x y).
rewrite (eq_nat_eq _ _ e) in *;auto.
assert (reachable R x y).
  unfold minimal_environment_for_var in H0.
  destruct y.
  destruct (reachable_dec_b e1 e2 R H x 0);auto.
  exfalso.
  apply beq_nat_true_iff in H0.
  apply n.
  apply eq_nat_is_eq;auto.
  destruct (reachable_dec_b e1 e2 R H x (S y));auto.
  exfalso.
  apply beq_nat_true_iff in H0.
  apply n.
  apply eq_nat_is_eq;auto.
induction H3.
apply (H1 _ _ H3);auto.
destruct (eq_nat_decide y z).
rewrite (eq_nat_eq _ _ e) in *.
apply (H1 _ _ H3);auto.
apply IHreachable;auto.
destruct z;unfold minimal_environment_for_var.
destruct (reachable_dec_b e1 e2 R H y 0);try contradiction;auto.
destruct (reachable_dec_b e1 e2 R H y (S z));try contradiction;auto.
apply (H1 _ _ H3);auto.
Qed.

Fixpoint minimal_environment_for_conj (R:propVar_relation)(e1 e2:list booleanEquation)(H:relates_bound R e1 e2)
  (f:propForm)(x:propVar):bool :=
match f with
| var y => (minimal_environment_for_var R e1 e2 H y x)
| f1 /\p f2 => (minimal_environment_for_conj R e1 e2 H f1 x)||(minimal_environment_for_conj R e1 e2 H f2 x)
| _ => false
end.

Lemma minimal_environment_for_conj_consistent : forall R:propVar_relation, forall e1 e2:list booleanEquation, 
  forall H:relates_bound R e1 e2, forall f:propForm, 
    consistent_environment (minimal_environment_for_conj R e1 e2 H f) R.
Proof.
intros.
induction f;intro;intros;simpl in *;auto.
unfold minimal_environment_for_var in *.
destruct y.
destruct (reachable_dec_b e1 e2 R H p 0);auto.
destruct x.
destruct (reachable_dec_b e1 e2 R H p 0);try contradiction;auto.
destruct (reachable_dec_b e1 e2 R H p (S x));try contradiction;auto.
exfalso.
apply n.
apply (reachable_trans _ _ (S x));auto.
apply single_path;auto.
apply beq_nat_true_iff in H1.
rewrite H1 in *.
exfalso.
apply n.
apply single_path;auto.
destruct (reachable_dec_b e1 e2 R H p (S y));auto.
destruct x.
destruct (reachable_dec_b e1 e2 R H p 0).
exfalso.
apply n.
apply (reachable_trans _ _ 0);auto.
apply single_path;auto.
apply beq_nat_true_iff in H1.
rewrite H1 in *.
exfalso.
apply n.
apply single_path;auto.
destruct (reachable_dec_b e1 e2 R H p (S x)).
exfalso.
apply n.
apply (reachable_trans _ _ (S x));auto.
apply single_path;auto.
apply beq_nat_true_iff in H1.
rewrite H1 in *.
exfalso.
apply n.
apply single_path;auto.
apply orb_true_iff in H1.
apply orb_true_iff.
destruct H1;auto.
left.
apply (IHf1 _ _ H0);auto.
right.
apply (IHf2 _ _ H0);auto.
Qed.

Lemma conj_propForm_grows_right : forall R:propVar_relation, forall e1 e2:list booleanEquation, 
  forall H:relates_bound R e1 e2, forall f g1 g2:propForm, conj_propForm g1 -> conj_propForm g2 ->
    [[f]]minimal_environment_for_conj R e1 e2 H g1-> [[f]]minimal_environment_for_conj R e1 e2 H (g1 /\p g2).
Proof.
intros.
induction f;simpl in *;auto.

apply orb_true_iff;auto.

destruct H2;auto.

destruct H2;auto.
Qed.

Lemma conj_propForm_grows_left : forall R:propVar_relation, forall e1 e2:list booleanEquation, forall H:relates_bound R e1 e2,
  forall f g1 g2:propForm, conj_propForm g1 -> conj_propForm g2 ->
    [[f]]minimal_environment_for_conj R e1 e2 H g2 -> [[f]]minimal_environment_for_conj R e1 e2 H (g1 /\p g2).
Proof.
intros.
induction f;simpl in *;auto.

apply orb_true_iff;auto.

destruct H2;auto.

destruct H2;auto.
Qed.

Lemma minimal_environment_for_conj_self : forall R:propVar_relation, forall e1 e2:list booleanEquation, forall H:relates_bound R e1 e2,
forall f:propForm, conj_propForm f -> ~propForm_eqv f bot -> [[f]]minimal_environment_for_conj R e1 e2 H f.
Proof.
intros.
induction H0 using conj_ind;auto.
simpl;auto.

apply H1.
split;intro;auto.

apply minimal_environment_for_var_self.

assert (~propForm_eqv f bot).
  intro.
  apply H1.
  split;intro;auto.
  apply H0.
  destruct H2;auto.
  inversion H2.
assert (~propForm_eqv g bot).
  intro.
  apply H1.
  split;intro;auto.
  apply H2.
  destruct H3;auto.
  inversion H3.
split.
apply conj_propForm_grows_right;auto.
apply conj_propForm_grows_left;auto.
Qed.

Lemma min_env_var_rel_cons_form : forall e1 e2:list booleanEquation, forall R:propVar_relation, forall H:relates_bound R e1 e2, 
  forall x:propVar, forall f:propForm, 
    [[f]]minimal_environment_for_var R e1 e2 H x -> rel_cons R (var x) f.
Proof.
intros.
induction f;intro;intros;simpl in *;auto.

apply (rel_cons_min_env _ _ _ _ _ _ H0);auto.

destruct H0.
left.
apply IHf1;auto.
right.
apply IHf2;auto.

destruct H0.
split.
apply IHf1;auto.
apply IHf2;auto.
Qed.

Lemma var_rel_cons_form_min_env : forall e1 e2:list booleanEquation, forall R:propVar_relation, forall H:relates_bound R e1 e2, 
  forall x:propVar, forall f:propForm, 
    rel_cons R (var x) f -> [[f]]minimal_environment_for_var R e1 e2 H x.
Proof.
intros.
apply (H0 (minimal_environment_for_var R e1 e2 H x) (minimal_environment_for_var_consistent R e1 e2 H _));auto.
apply (minimal_environment_for_var_self).
Qed.

Lemma min_for_conj_rel_cons : forall R:propVar_relation, forall e1 e2:list booleanEquation, 
  forall H:relates_bound R e1 e2, forall f g:propForm, conj_propForm f -> 
    [[g]](minimal_environment_for_conj R e1 e2 H f) -> rel_cons R f g.
Proof.
intros.
induction g;simpl in *;auto.
intro;intros;simpl;auto.

inversion H1.

induction H0 using conj_ind;auto.
  inversion H1.

  inversion H1.

  simpl in H1.
  apply (min_env_var_rel_cons_form _ _ _ H);auto.

  intro;intros.
  destruct H2.
  apply orb_true_iff in H1.
  destruct H1.
  apply IHconj_propForm1;auto.
  apply IHconj_propForm2;auto.

destruct H1.
intro;intros.
left.
apply IHg1;auto.
intro;intros.
right;apply IHg2;auto.

destruct H1.
intro;intros.
split.
apply IHg1;auto.
apply IHg2;auto.
Qed.
