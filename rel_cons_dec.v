Add LoadPath "somePath".

Require Export rel_ind.

(*----------rel_cons decide----------*)

Fixpoint flatten_genBES (e1:list block):list booleanEquation :=
match e1 with
| nil => nil
| bl::e' => bl++ (flatten_genBES e')
end.

Lemma DNF_rel_cons_DNF_decidable : forall R:propVar_relation, forall e1 e2:genBES, 
  relates_bound R (flatten_genBES e1) (flatten_genBES e2) ->
    forall f:propForm, DNF_propForm f -> forall g:propForm, DNF_propForm g -> 
      (rel_cons R f g \/ ~rel_cons R f g).
Proof.
intros R e1 e2 H f H0.
induction H0 using DNF_ind.
intros.
destruct (propForm_eqv_decidable g top).
left;intro;intros.
apply H1;auto.
right;intro;intros.
apply H1.
apply empty_true_eqv_top.
apply H2.
apply empty_environment_consistent.
simpl;auto.

left;intro;intros.
inversion H2.

intros.
destruct (propForm_solution_decidable g (minimal_environment_for_var _ _ _ H x)).
left.
apply (min_env_var_rel_cons_form _ _ _ H);auto.
right.
intro.
apply H1.
apply (var_rel_cons_form_min_env _ _ _ H);auto.

intros.
destruct (propForm_solution_decidable g0 (minimal_environment_for_conj _ _ _ H (f /\p g))).
left.
apply (min_for_conj_rel_cons _ _ _ H);auto.
split;auto.
destruct (propForm_eqv_decidable (f /\p g) bot).
left;intro;intros.
assert ([[bot]]theta).
  apply H4;auto.
inversion H7.
right.
intro.
apply H3.
apply H5.
apply minimal_environment_for_conj_consistent;auto.
apply minimal_environment_for_conj_self;auto.
split;auto.

intros.
destruct (propForm_eqv_decidable (f \/p g) bot).
left;intro;intros.
assert ([[bot]]theta).
  apply H1;auto.
inversion H4.
destruct (IHDNF_propForm1 g0);auto.
destruct (IHDNF_propForm2 g0);auto.
left.
intro;intros.
destruct H5.
apply H2;auto.
apply H3;auto.
right.
intro.
apply H3.
intro;intros.
apply H4;auto.
right;auto.
right.
intro.
apply H2.
intro;intros.
apply H3;auto.
left;auto.
Qed.

Lemma rel_cons_decidable : forall R:propVar_relation, forall e1 e2:genBES, 
  relates_bound R (flatten_genBES e1) (flatten_genBES e2) -> 
    forall f g:propForm, rel_cons R f g \/ ~rel_cons R f g.
Proof.
intros.
destruct (DNF_rel_cons_DNF_decidable _ _ _ H (toDNF f) (DNF_toDNF _) (toDNF g) (DNF_toDNF _)).
left.
intro;intros.
apply toDNF_cons.
apply H0;auto.
apply cons_toDNF;auto.

right;intro.
apply H0.
intro;intros.
apply cons_toDNF.
apply H1;auto.
apply toDNF_cons;auto.
Qed.

