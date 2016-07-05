Add LoadPath "somePath".

Require Export propForm.

(*----------propForm cons----------*)

Definition propForm_cons (f g:propForm):Prop := 
  forall theta:environment, [[f]]theta -> [[g]]theta.

Definition propForm_eqv (f g:propForm):Prop :=
  forall theta:environment, [[f]] theta <-> [[g]] theta.

(*bot*)
Lemma propForm_eqv_bot : forall f:propForm, (forall theta:environment, ~[[f]]theta) <-> propForm_eqv f bot.
Proof.
intros.
split;intro.
induction f;simpl in *.
specialize (H full_environment).
simpl in H.
exfalso;apply H;auto.
split;simpl;auto.
specialize (H full_environment).
exfalso.
apply H.
simpl;auto.
split;intro.
specialize (H theta).
contradiction.
simpl in H0.
inversion H0.
split.
intro.
specialize (H theta).
contradiction.
intro.
simpl in H0.
inversion H0.
intros.
intro.
destruct (H theta).
apply H1.
assumption.
Qed.

Lemma eqv_bot_dec : forall f:propForm, 
  ((forall theta:environment, ~[[f]]theta) \/ exists theta:environment, [[f]]theta).
Proof.
intros.
induction f.
right;exists empty_environment;simpl;auto.
left;simpl;intros;auto.
right;exists full_environment;simpl;auto.
destruct IHf1.
destruct IHf2.
left;intros.
intro.
destruct H1.
apply (H theta H1).
apply (H0 theta H1).
destruct H0.
right;exists x;right;assumption.
destruct H.
right;exists x;left;assumption.
destruct IHf1.
left;intros.
intro.
destruct H0.
apply (H theta);auto.
destruct IHf2.
left;intros.
intro.
destruct H1.
apply (H0 theta);auto.
destruct H as [theta1 H].
destruct H0 as [theta2 H0].
right.
exists (environment_union theta1 theta2).
apply (environment_union_distributes theta1 theta2 f1 f2).
auto.
Qed.

Lemma eqv_propForm_bot_decidable : forall g:propForm, propForm_eqv g bot \/ ~propForm_eqv g bot.
Proof.
intros.
destruct (eqv_bot_dec g);auto.
left;split;intro.
simpl;apply (H theta);auto.
inversion H0.
right.
intro.
destruct H as [theta H].
destruct (H0 theta).
simpl in *;auto.
Qed.

Lemma neqv_bot_full_true : forall f:propForm, (~propForm_eqv f bot) -> [[f]]full_environment.
Proof.
intros;simpl in *.
destruct (propForm_solution_decidable f full_environment).
assumption.
exfalso.
apply H.
split;intro;simpl;auto.
specialize (full_environment_maximal f theta H1);intro;auto.
inversion H1.
Qed.

Lemma full_false_eqv_bot : forall f:propForm, ~[[f]]full_environment -> propForm_eqv f bot.
Proof.
intros;split;intro;simpl in *.
induction f;simpl in *;auto.
destruct H0.
apply IHf1;auto.
apply IHf2;auto.
destruct H0.
destruct (propForm_solution_decidable f1 full_environment).
destruct (propForm_solution_decidable f2 full_environment).
apply H;split;auto.
apply IHf2;auto.
apply IHf1;auto.
inversion H0.
Qed.

Lemma neq_var_bot : forall x:propVar, ~(propForm_eqv (var x) bot).
Proof.
intros.
unfold propForm_eqv.
intro.
specialize (H full_environment).
unfold full_environment in H.
simpl in H.
destruct H.
apply H.
auto.
Qed.

Lemma eqv_bot_full_false : forall f:propForm, propForm_eqv f bot -> ~[[f]]full_environment.
Proof.
intros;intro;induction f;simpl in *;auto.
destruct (H full_environment);simpl in *;auto.
apply (neq_var_bot p);auto.
destruct H0.
apply IHf1;auto.
split;intro;simpl in *;auto.
destruct (H theta);simpl in *;auto.
inversion H1.
apply IHf2;auto.
split;intro;simpl in *;auto.
destruct (H theta);simpl in *;auto.
inversion H1.
destruct (H full_environment);simpl in *;auto.
Qed.

(*top*)
Lemma propForm_eqv_top : forall f:propForm, (forall theta:environment, [[f]]theta) <-> propForm_eqv f top.
Proof.
intros.
split;intro.
split;intro.
simpl;auto.
apply H;auto.
induction f;simpl in *;intros;auto.
destruct (H theta);simpl in *;auto.
destruct (H empty_environment).
unfold empty_environment in H1;simpl in H1.
assert false;auto.
inversion H2.
destruct (H theta).
apply H1;simpl;auto.
destruct (H theta).
apply H1;simpl;auto.
Qed.

Lemma empty_true_eqv_top : forall f:propForm, [[f]]empty_environment -> propForm_eqv f top.
Proof.
induction f;intro;split;intro;simpl;auto.
inversion H0.
simpl in H.
unfold empty_environment in H.
inversion H.
simpl in H.
unfold empty_environment in H.
inversion H.
simpl in *.
left.
apply IHf1;auto.
right.
apply IHf2;auto.
destruct H.
split;auto.
apply IHf1;auto.
apply IHf2;auto.
Qed.

Lemma not_top_get_not_true : forall f:propForm, 
  (~(propForm_eqv top f)) -> exists theta:environment, ~[[f]]theta.
Proof.
induction f;intros;auto.
exfalso;apply H;split;intro;auto.
exists empty_environment;intro.
inversion H0.
exists empty_environment;intro.
unfold empty_environment in H0.
inversion H0.
assert (~ propForm_eqv top f1).
intro.
apply H.
split;intro.
left;apply H0;auto.
simpl;auto.
assert (~ propForm_eqv top f2).
intro.
apply H.
split;intro.
right;apply H1;auto.
simpl;auto.
destruct (IHf1 H0) as [theta1 Hf1].
destruct (IHf2 H1) as [theta2 Hf2].
assert (~[[f1]]empty_environment).
apply (empty_environment_minimal f1 theta1).
auto.
assert (~[[f2]]empty_environment).
apply (empty_environment_minimal f2 theta2).
auto.
exists empty_environment.
intro.
destruct H4;auto.
exists empty_environment.
intro.
destruct H0.
apply H.
split;simpl;intro;auto.
split.
apply (empty_true_eqv_top f1 H0);simpl;auto.
apply (empty_true_eqv_top f2 H1);simpl;auto.
Qed.

Lemma eqv_top_decidable : forall f:propForm, propForm_eqv f top \/ ~(propForm_eqv f top).
Proof.
induction f;simpl in *;auto.
left;split;intro;auto.
right;intro.
destruct (H empty_environment);simpl in *;auto.
right;intro;destruct (H empty_environment);simpl in *.
unfold empty_environment in H1.
assert True;auto.
assert false;auto.
inversion H3.
destruct IHf1.
left;split;intro;simpl;auto.
left;apply H;auto.
destruct IHf2.
left;split;intro;simpl;auto.
right;apply H0;auto.
right;intro.
assert (~propForm_eqv top f1).
intro;apply H.
split;simpl;apply H2;auto.
destruct (not_top_get_not_true f1 H2).
assert (~propForm_eqv top f2).
intro;apply H0.
split;simpl;apply H4;auto.
destruct (not_top_get_not_true f2 H4).
clear H2 H4.
assert (~[[f1]]empty_environment).
intro.
specialize (empty_true_eqv_top f1 H2).
intro;contradiction.
assert (~[[f2]]empty_environment).
intro.
specialize (empty_true_eqv_top f2 H4).
intro;contradiction.
destruct (H1 empty_environment).
simpl in *.
assert True;auto.
destruct (H7 H8);auto.
destruct IHf1.
destruct IHf2.
left;split;intro;simpl;auto.
split.
apply H;auto.
apply H0;auto.
right;intro.
assert (propForm_eqv f2 top).
split;intro;simpl;auto.
destruct (H1 theta).
destruct (H4 H2);auto.
contradiction.
right;intro.
assert (propForm_eqv f1 top).
split;intro;simpl;auto.
destruct (H0 theta).
destruct (H3 H1);auto.
contradiction.
Qed.

Lemma neq_var_top : forall x:propVar, ~(propForm_eqv (var x) top).
Proof.
intros.
intro.
specialize (H empty_environment).
unfold empty_environment in H.
simpl in H.
destruct H.
absurd (~false).
intro.
unfold not in H1.
apply H1.
apply H0;auto.
intro.
inversion H1.
Qed.

Lemma cons_var_propForm : forall f:propForm, forall x:propVar, 
  (forall theta:environment, theta x -> [[f]]theta) \/ (exists theta : environment, theta x /\ ~[[f]]theta).
Proof.
intros.
induction f.
left;simpl;auto.

right.
exists full_environment.
simpl.
unfold full_environment.
split;auto.

simpl.
destruct (eq_nat_decide x p).
rewrite (eq_nat_eq x p e) in *.
left.
intros.
auto.
destruct (beq_nat_false_iff x p).
assert (x<>p).
intro.
apply (eq_nat_is_eq) in H1.
contradiction.
specialize (H0 H1).
right.
exists (environment_point x).
unfold environment_point.
split.
rewrite<- (beq_nat_refl x).
auto.
rewrite H0.
intro.
inversion H2.

destruct IHf1.
left;intros;left;auto.
destruct IHf2.
left;intros;right;auto.
destruct H as [theta1 H].
destruct H0 as [theta2 H0].
destruct H;destruct H0.
right.
exists (environment_point x).
split.
unfold environment_point.
rewrite<- (beq_nat_refl x).
auto.
intro.
destruct H3.
apply (environment_point_minimal f1 x theta1);auto.
apply (environment_point_minimal f2 x theta2);auto.

destruct IHf1.
destruct IHf2.
left;intros;split;auto.
destruct H0 as [theta1 H0].
destruct H0.
right.
exists theta1.
split;auto.
intro.
destruct H2.
contradiction.
destruct H as [theta1 H].
destruct H.
right.
exists theta1.
split;auto.
intro.
destruct H1.
contradiction.
Qed.

Lemma cons_propForm_var : forall f:propForm, forall x:propVar, 
  (forall theta:environment, [[f]]theta -> theta x) \/ (exists theta:environment, [[f]]theta /\ ~theta x).
Proof.
intros.
induction f.
right.
exists empty_environment.
simpl.
unfold empty_environment.
split.
auto.
intro.
inversion H.

left.
simpl.
intros.
inversion H.

destruct (eq_nat_decide p x).
rewrite (eq_nat_eq p x e) in *.
left.
intros.
simpl in *.
assumption.
destruct (beq_nat_false_iff p x).
assert (p<>x).
intro.
apply (eq_nat_is_eq) in H1.
contradiction.
specialize (H0 H1).
simpl.
right.
exists (environment_point p).
unfold environment_point.
split.
rewrite<- (beq_nat_refl p).
auto.
rewrite H0.
intro.
inversion H2.

destruct IHf1.
destruct IHf2.
left.
intros.
destruct H1.
apply H;auto.
apply H0;auto.

destruct H0 as [theta2 H0].
destruct H0.
right.
exists theta2.
split.
right;assumption.
assumption.
destruct H as [theta1 H].
destruct H.
right.
exists theta1.
split.
left;assumption.
assumption.

destruct IHf1.
left.
intros.
destruct H0.
apply H;assumption.
destruct H as [theta1 H].
destruct H.
destruct IHf2.
left.
intros.
destruct H2.
apply H1.
assumption.
destruct H1 as [theta2 H1].
destruct H1.
right.
exists (environment_union theta1 theta2).
split.
specialize (environment_union_distributes theta1 theta2 f1 f2).
intros.
apply H3.
auto.
intro.
unfold environment_union in H3.
destruct (orb_prop (theta1 x) (theta2 x) H3).
rewrite H4 in H0.
apply H0.
auto.
rewrite H4 in H2.
apply H2.
auto.
Qed.

Lemma var_cons_propForm_decidable:
  forall (f : propForm) (x : propVar),
  propForm_cons f (var x) \/ ~ propForm_cons f (var x).
Proof.
intros.
destruct (cons_propForm_var f x).
left;intro;intros;apply H;auto.
right;intro.
destruct H as [theta H].
destruct H.
apply H1.
apply H0;auto.
Qed.

