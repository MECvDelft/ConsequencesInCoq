Add LoadPath "somePath".

Require Export DNF.

(*----------cons decide----------*)

Lemma conj_full_ncons_max_point : forall f:propForm, [[f]]full_environment -> conj_propForm f -> 
  forall x:propVar, ~propForm_cons f (var x) -> [[f]]environment_max_point x.
Proof.
intros.
induction f;simpl in *;auto.
unfold environment_max_point.
assert (beq_nat x p=false).
apply (beq_nat_false_iff).
intro.
apply H1.
rewrite H2;intro;auto.
rewrite H2;auto.
inversion H0.
destruct H.
destruct H0.
assert (~propForm_cons f1 (var x)).
intro.
apply H1.
intro;intro.
destruct H5;auto.
assert (~propForm_cons f2 (var x)).
intro.
apply H1.
intro;intro.
destruct H6;auto.
split.
apply IHf1;auto.
apply IHf2;auto.
Qed.

Lemma conj_cons_propForm_decidable : forall f g:propForm, conj_propForm f -> 
  (propForm_cons f g \/ exists theta:environment, ([[f]]theta /\ ~[[g]]theta)).
Proof.
intros.
destruct (eqv_propForm_bot_decidable f).
left;intro;intro.
destruct (H0 theta).
destruct H2;auto.
destruct (eqv_top_decidable g).
left;intro;intro.
apply (H1 theta);simpl;auto.
induction g;simpl in *;auto.
left;intro;intro;simpl;auto.
right.
exists (full_environment).
split;simpl;auto.
apply neqv_bot_full_true;auto.
destruct (var_cons_propForm_decidable f p);auto.
right.
exists (environment_max_point p).
split.
apply conj_full_ncons_max_point;auto.
apply neqv_bot_full_true;auto.
unfold environment_max_point.
rewrite <- (beq_nat_refl p);intro.
inversion H3.
assert (~propForm_eqv g1 top).
intro.
apply H1.
split;intro;simpl;auto.
left;apply H2;auto.
assert (~propForm_eqv g2 top).
intro.
apply H1.
split;intro;simpl;auto.
right;apply H3;auto.
destruct (IHg1 H2).
left;intro;intro.
left;apply H4;auto.
destruct (IHg2 H3).
left;intro;intro.
right;apply H5;auto.
destruct H4 as [theta1 H4].
destruct H5 as [theta2 H5].
right.
exists (environment_intersect theta1 theta2).
destruct H4.
destruct H5.
split.
apply env_intersect_conj;auto.
intro.
destruct (environment_intersect_distributes_neg theta1 theta2 g1 g2);auto.
destruct H8;contradiction.
destruct (eqv_top_decidable g1).
assert (~propForm_eqv g2 top).
intro.
apply H1.
split;intro;simpl;auto.
split.
apply H2;auto.
apply H3;auto.
destruct (IHg2 H3).
left;intro;intro.
split.
apply H2;simpl;auto.
apply H4;auto.
destruct H4 as [theta H4].
destruct H4.
right.
exists theta.
split;auto.
intro.
destruct H6;contradiction.
destruct (eqv_top_decidable g2).
destruct (IHg1 H2).
left;intro;intro.
split.
apply H4;auto.
apply H3;simpl;auto.
destruct H4 as [theta H4].
destruct H4.
right.
exists theta.
split;auto.
intro.
destruct H6;contradiction.
destruct (IHg1 H2).
destruct (IHg2 H3).
left;intro;intro.
split.
apply H4;auto.
apply H5;auto.
destruct H5 as [theta H5].
destruct H5.
right.
exists theta;split;auto.
intro.
destruct H7;contradiction.
destruct H4 as [theta H5].
destruct H5.
right.
exists theta;split;auto.
intro.
destruct H6;contradiction.
Qed.

Lemma DNF_cons_propForm_decidable : forall f g:propForm, DNF_propForm f -> 
  (propForm_cons f g \/ exists theta:environment, ([[f]]theta /\ ~[[g]]theta)).
Proof.
intros.
induction H using DNF_ind.
apply (conj_cons_propForm_decidable top g).
unfold conj_propForm;unfold singleton_propForm;auto.
apply (conj_cons_propForm_decidable bot g).
unfold conj_propForm;unfold singleton_propForm;auto.
apply (conj_cons_propForm_decidable (var x) g).
unfold conj_propForm;unfold singleton_propForm;auto.
apply (conj_cons_propForm_decidable (f /\p g0) g).
split;auto.
destruct IHDNF_propForm1.
destruct IHDNF_propForm2.
left;intro;intro.
destruct H3.
apply H1;auto.
apply H2;auto.
destruct H2 as [theta H2].
destruct H2.
right.
exists theta;split;auto.
right;auto.
destruct H1 as [theta H1].
destruct H1.
right.
exists theta;split;auto.
left;auto.
Qed.

Lemma propForm_cons_propForm_decidable : forall f g:propForm, 
  (propForm_cons f g \/ exists theta:environment, ([[f]]theta /\ ~[[g]]theta)).
Proof.
intros.
destruct (DNF_cons_propForm_decidable (toDNF f) g).
apply DNF_toDNF;auto.
left.
intro;intro.
apply H;apply cons_toDNF;auto.
right.
destruct H as [theta H].
destruct H.
exists theta.
split;auto.
apply toDNF_cons;auto.
Qed.

Lemma conj_cons_disj_decide : forall c f g:propForm, conj_propForm c ->
  propForm_cons c (f \/p g) -> (propForm_cons c f \/ propForm_cons c g).
Proof.
intros.
destruct (propForm_cons_propForm_decidable c f);auto.
destruct (propForm_cons_propForm_decidable c g);auto.
destruct H1 as [theta1 H1].
destruct H2 as [theta2 H2].
destruct H1.
destruct H2.
destruct (environment_intersect_distributes_neg theta1 theta2 f g).
split;auto.
destruct (H0 (environment_intersect theta1 theta2) (env_intersect_conj c H theta1 theta2 H1 H2));contradiction.
Qed.

Lemma propForm_eqv_decidable : forall f g:propForm, propForm_eqv f g \/ ~propForm_eqv f g.
Proof.
intros.
destruct (propForm_cons_propForm_decidable f g).
destruct (propForm_cons_propForm_decidable g f).
left;split;intro.
apply H;auto.
apply H0;auto.
destruct H0.
destruct H0.
right;intro.
destruct (H2 x).
assert ([[f]]x);auto.
destruct H.
destruct H.
right;intro.
destruct (H1 x).
assert ([[g]]x);auto.
Qed.

