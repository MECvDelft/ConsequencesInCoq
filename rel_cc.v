Add LoadPath "somePath".

Require Export cc.

(*----------relative cc----------*)

Definition relative_cc (E:BES)(R G:propVar_relation):Prop := 
forall x y:propVar, R x y -> 
  (rank E x=rank E y)
/\
  (bnd E x -> bnd E y -> consistent_environment_rhs E (R U G) x y).

Lemma empty_relation_rel_cc : forall E:BES, forall G:propVar_relation, 
  relative_cc E (empty_relation) G.
Proof.
intros;intro;intros.
inversion H.
Qed.

Lemma empty_relative_cc: forall E:BES, forall R:propVar_relation, 
  relative_cc E R empty_relation -> consistent_consequence E R.
Proof.
intros.
intro;intros.
destruct (H x y);auto.
split;auto.
intros;intro;intros.
apply (H2 H3 H4 theta);auto.
intro;intros.
destruct H7.
apply (H5 x0);auto.
inversion H7.
Qed.

Lemma cc_relative_empty: forall E:BES, forall R:propVar_relation, 
  consistent_consequence E R -> relative_cc E R empty_relation.
Proof.
intros.
unfold relative_cc.
intros.
destruct (H x y);auto.
split;auto.
intros;intro;intros.
apply H2;auto.
apply (consistent_environment_rel_union _ _ _ H5).
Qed.

Lemma rel_union_maintains_rel_cc : forall E:BES, forall R1 R2 G:propVar_relation, 
  relative_cc E R1 G -> relative_cc E R2 G -> relative_cc E (R1 U R2) G.
Proof.
intros;intro;intros.
destruct H1.
destruct (H x y);auto.
split;auto.
intros;intro;intros.
apply H3;auto.
destruct (consistent_environment_rel_union _ _ _ H6).
destruct (consistent_environment_rel_union _ _ _ H8).
apply rel_union_consistent_environment;auto.
destruct (H0 x y);auto.
split;auto.
intros;intro;intros.
apply H3;auto.
destruct (consistent_environment_rel_union _ _ _ H6).
destruct (consistent_environment_rel_union _ _ _ H8).
apply rel_union_consistent_environment;auto.
Qed.

Definition rel_cc_on_propForm (E:BES)(G:propVar_relation)(f g:propForm) : Prop := 
  exists R:propVar_relation, relates_bound R (flatten_genBES E) (flatten_genBES E) /\ relative_cc E R G /\ 
    forall theta:environment, consistent_environment theta (R U G) ->
      [[f]]theta -> [[g]]theta
.

Definition rel_cc_on_propVar (E:BES)(G:propVar_relation)(x y:propVar):Prop :=
  exists R:propVar_relation, relates_bound R (flatten_genBES E) (flatten_genBES E) /\ relative_cc E R G /\ 
    (R U G U id_rel) x y.

Lemma rel_cc_trans : forall E:BES, forall G:propVar_relation, forall a b c:propForm, 
  ((rel_cc_on_propForm E G a b)/\(rel_cc_on_propForm E G b c)) ->
    (rel_cc_on_propForm E G a c).
Proof.
intros.
destruct H.
unfold rel_cc_on_propForm.
destruct H.
destruct H0.
destruct H.
destruct H1.
destruct H0.
destruct H3.
exists (x U x0).
split.
intro;intros.
destruct H5.
apply H;auto.
apply H0;auto.
split.
apply rel_union_maintains_rel_cc;auto.
intros.
destruct (consistent_environment_rel_union _ _ _ H5).
destruct (consistent_environment_rel_union _ _ _ H7).
apply H4.
apply rel_union_consistent_environment;auto.
apply H2;auto.
apply rel_union_consistent_environment;auto.
Qed.

Lemma bnd_block_flatten_bnd : forall E:BES, forall x:propVar, bnd E x -> bnd_block (flatten_genBES E) x.
Proof.
destruct E as [e w_d_e];simpl in *.
clear w_d_e.
destruct e as [l alt_l];simpl in *.
clear alt_l.
induction l;simpl in *;auto.
destruct a as [bl t_bl n_e_bl];simpl in *.
clear t_bl.
clear n_e_bl.
induction bl.
intros.
simpl.
destruct H;auto.
inversion H.
intros.
destruct a as [y f].
simpl;destruct H;auto.
destruct H;auto.
Qed.

Lemma bnd_flatten_bnd_block : forall E:BES, forall x:propVar, bnd_block (flatten_genBES E) x -> bnd E x.
Proof.
destruct E as [e w_d_e];simpl in *.
clear w_d_e.
destruct e as [l alt_l];simpl in *.
clear alt_l.
induction l;simpl in *;auto.
destruct a as [bl t_bl n_e_bl];simpl in *.
clear t_bl.
clear n_e_bl.
induction bl.
intros.
simpl in H;auto.
intros.
destruct a as [y f];simpl in *.
destruct H;auto.
destruct (IHbl _ H);auto.
Qed.

Lemma propForm_cons_cc_max : forall E:BES, forall x y:propVar, bnd E x -> bnd E y -> 
  rel_cc_on_propForm E empty_relation (var x) (var y) -> cc_max E x y.
Proof.
intros.
destruct (eq_nat_decide x y).
rewrite (eq_nat_eq _ _ e) in *.
exists (pair_relation y y).
split.
intro;intros.
destruct H2.
rewrite H2 in *;rewrite H3 in *.
split;auto.
intros;intro;intros;auto.
split.
intro;intros.
destruct H2;rewrite H2 in *;rewrite H3 in *.
split;apply bnd_block_flatten_bnd;auto.
split;auto.

destruct H1 as [R H1].
destruct H1.
destruct H2.
exists (reachable R).
split.
intro;intros.
induction H4.
  destruct (H2 x0 y0);auto.
  split;auto.
  intros;intro;intros.
  apply H6;auto.
  intro;intros.
  destruct H11;try contradiction.
  apply (H9 x1);auto.
  apply single_path;auto.

  destruct IHreachable.
  split.
  destruct (H2 x0 y0);auto.
  rewrite H6 in *;auto.
  intros;intro;intros.
  destruct (H2 x0 y0);auto.
  apply eq_rank in H12.
  apply H7;auto.
  apply H12;auto.
  apply H13;auto.
  apply H12;auto.
  intro;intros.
  apply (H10 x1);auto.
  destruct H14;try contradiction.
  apply single_path;auto.

split.
clear - H1.
intro;intros.
induction H.
apply H1;auto.
destruct (H1 x y);auto.
destruct IHreachable;auto.

apply (reachable_if_min_env _ _ _ H1).
intro.
apply n.
apply eq_nat_is_eq;auto.
assert (rel_cons R (var x) (var y)).
  intro;intros.
  apply H3;auto.
  intro;intros.
  destruct H6;try contradiction.
  apply (H4 x0);auto.
apply H4.
apply minimal_environment_for_var_consistent.
apply minimal_environment_for_var_self.
Qed.
