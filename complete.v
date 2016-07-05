Add LoadPath "somePath".

Require Export complete_cons.

(*----------completeness----------*)

Lemma complete_fom_conj_rel_cons : forall E:BES, forall R G:propVar_relation, 
relates_bound R (flatten_genBES E) (flatten_genBES E) -> 
  forall f g:propForm, conj_propForm f -> DNF_propForm g -> 
    rel_cons R f g -> 
      (forall x y:propVar, R x y -> prv_tree E (stmt G (var x) (var y))) ->
        prv_tree E (stmt G f g).
Proof.
intros.
induction H1 using DNF_ind;simpl in *;auto.
apply (TRA _ _ (f /\p top)).
apply TOP.
apply (TRA _ _ (top /\p f)).
apply COM1.
apply INF.

assert (propForm_eqv f bot).
  apply full_false_eqv_bot.
  intro.
  specialize (H2 _ (full_environment_consistent _) H1).
  inversion H2.
apply complete_cons.
intro;intros.
apply H1;auto.

destruct (propForm_eqv_decidable f bot).
apply complete_cons.
intro;intros.
assert ([[bot]]theta).
  apply H1;auto.
inversion H5.
induction H0 using conj_ind.
  assert (empty_environment x).
    apply H2.
    apply empty_environment_consistent.
    simpl;auto.
  inversion H0.

  exfalso.
  apply H1.
  split;intro;auto.

  destruct (eq_nat_decide x0 x).
  rewrite (eq_nat_eq _ _ e) in *.
  apply REF;auto.
  apply (min_env_rel_cons _ _ _ H) in H2.
  apply reachable_if_min_env in H2.
  clear H1.
  induction H2.
  apply H3;auto.
  destruct (eq_nat_decide y z).
  rewrite (eq_nat_eq _ _ e) in *;auto.
  apply (TRA _ _ (var y));auto.
  intro.
  apply n;apply eq_nat_is_eq;auto.

  assert (~propForm_eqv f bot).
    intro.
    apply H1.
    split;intros;auto.
    destruct H4;apply H0;auto.
    inversion H4.
  assert (~propForm_eqv g bot).
    intro.
    apply H1.
    split;intros;auto.
    destruct H5;apply H4;auto.
    inversion H5.
  destruct (rel_cons_decidable _ _ _ H f (var x)).
  apply (TRA _ _ f);auto.
  apply INF.
  destruct (rel_cons_decidable _ _ _ H g (var x)).
  apply (TRA _ _ g);auto.
  apply (TRA _ _ (g /\p f)).
  apply COM1.
  apply INF.
  assert (environment_union (minimal_environment_for_conj _ _ _ H f) (minimal_environment_for_conj _ _ _ H g) x).
    apply H2.
    apply environment_union_consistent;apply (minimal_environment_for_conj_consistent _);auto.
    split.
    apply environment_union_grows.
    left.
    apply minimal_environment_for_conj_self;auto.
    apply environment_union_grows.
    right.
    apply minimal_environment_for_conj_self;auto.
  apply orb_true_iff in H7.
  destruct H7.
  exfalso.
  apply H5.
  apply (min_for_conj_rel_cons _ _ _ H);auto.
  exfalso.
  apply H6.
  apply (min_for_conj_rel_cons _ _ _ H);auto.

assert (rel_cons R f f0).
  intro;intros;apply H2;auto.
assert (rel_cons R f g).
  intro;intros;apply H2;auto.
apply cSPLIT;auto.

destruct (propForm_eqv_decidable f bot).
apply complete_cons.
intro;intros.
assert ([[bot]]theta).
  apply H1;auto.
inversion H5.
destruct (H2 (minimal_environment_for_conj _ _ _ H f)).
apply minimal_environment_for_conj_consistent.
apply minimal_environment_for_conj_self;auto.
apply min_for_conj_rel_cons in H4;auto.
apply (TRA _ _ f0);auto.
apply SUP.
apply min_for_conj_rel_cons in H4;auto.
apply (TRA _ _ g);auto.
apply (TRA _ _ (g \/p f0)).
apply SUP.
apply COM2.
Qed.

Lemma lem5_DNF : forall E:BES, forall R G:propVar_relation, 
  relates_bound R (flatten_genBES E) (flatten_genBES E) -> 
    forall f g:propForm, DNF_propForm f -> DNF_propForm g -> 
      rel_cons R f g -> 
        (forall x y:propVar, R x y -> prv_tree E (stmt G (var x) (var y))) ->
          prv_tree E (stmt G f g).
Proof.
intros.
induction H0 using DNF_ind.
  assert ([[g]]empty_environment).
    apply H2;simpl;auto.
    apply (empty_environment_consistent _).
  apply empty_true_eqv_top in H0.
  apply complete_cons.
  intro;intros;apply H0;simpl;auto.

  apply (TRA _ _ (g \/p bot)).
  apply (TRA _ _ (bot \/p g)).
  apply SUP.
  apply COM2.
  apply BOT.

  induction H1 using DNF_ind.
    apply complete_cons.
    intro;intros;simpl;auto.

    assert ([[bot]]full_environment).
      apply H2;simpl;auto.
      apply (full_environment_consistent _).
    inversion H0.

    destruct (eq_nat_decide x x0).
    rewrite (eq_nat_eq _ _ e) in *.
    apply REF;auto.
    apply (min_env_rel_cons _ _ _ H) in H2.
    apply reachable_if_min_env in H2.
    induction H2;auto.
    apply (TRA _ _ (var y));auto.
    destruct (eq_nat_decide y z);auto.
    rewrite (eq_nat_eq _ _ e) in *.
    apply REF.
    intro.
    apply n;apply eq_nat_is_eq;auto.

    assert (rel_cons R (var x) f).
      intro;intros;apply H2;auto.
    assert (rel_cons R (var x) g).
      intro;intros;apply H2;auto.
    apply (TRA _ _ (var x /\p g)).
    apply (TRA _ _ (var x /\p var x)).
    apply ID1.
    destruct (exists_unused (var x)).
    specialize (CTX _ _ _ (var x /\p var x0) x0 _ (IHDNF_propForm0 H5)).
    simpl.
    rewrite<- beq_nat_refl.
    assert (beq_nat x0 x=false).
      apply beq_nat_false_iff;auto.
    rewrite H7.
    auto.
    destruct (exists_unused g).
    specialize (CTX _ _ _ (var x0 /\p g) x0 _ (IHDNF_propForm H4)).
    simpl.
    rewrite<- beq_nat_refl.
    repeat rewrite (unused_no_rewrite _ _ _ H6).
    auto.

    destruct (H2 (minimal_environment_for_var _ _ _ H x) (minimal_environment_for_var_consistent _ _ _ H x) (minimal_environment_for_var_self _ _ _ H x)).
    apply (min_env_var_rel_cons_form _ _ _ H) in H0.
    apply (TRA _ _ f);auto.
    apply SUP.
    apply (min_env_var_rel_cons_form _ _ _ H) in H0.
    apply (TRA _ _ g);auto.
    apply (TRA _ _ (g \/p f)).
    apply SUP.
    apply COM2.

  apply (complete_fom_conj_rel_cons _ _ _ H);simpl;auto.

  assert (rel_cons R f g).
    intro;intros.
    apply H2;simpl;auto.
  assert (rel_cons R g0 g).
    intro;intros.
    apply H2;simpl;auto.

  apply aSPLIT;auto.
Qed.

Lemma lem5 : forall E:BES, forall R G:propVar_relation, 
  relates_bound R (flatten_genBES E) (flatten_genBES E) -> 
    forall f g:propForm, rel_cons R f g -> 
        (forall x y:propVar, R x y -> prv_tree E (stmt G (var x) (var y))) ->
          prv_tree E (stmt G f g).
Proof.
intros.
apply (TRA _ _ (toDNF f)).
apply complete_cons.
intro;intros;apply cons_toDNF;auto.
apply (TRA _ _ (toDNF g)).
apply (lem5_DNF _ _ _ H);auto.
apply DNF_toDNF.
apply DNF_toDNF.
intro;intros.
apply cons_toDNF.
apply H0;auto.
apply toDNF_cons;auto.
apply complete_cons.
intro;intros;apply toDNF_cons;auto.
Qed.

Lemma complete_propVar : forall E:BES, forall n:nat, forall G:propVar_relation, 
  rev_subset_card (flatten_genBES E) (flatten_genBES E) G n -> 
    forall x y:propVar, rel_cc_on_propVar E G x y -> prv_tree E (stmt G (var x) (var y)).
Proof.
intros E n.
induction n;intros.
exfalso.
apply rev_card_gt0 in H.
apply (gt_irrefl _ H).

destruct H0 as [R H0].
destruct H0.
destruct H1.
(*Id x y*)
destruct (eq_nat_decide x y).
rewrite (eq_nat_eq _ _ e) in *.
apply REF.
destruct H2.
(*G x y*)
assert (relates_bound G (flatten_genBES E) (flatten_genBES E)).
  assert (rev_subset (flatten_genBES E) (flatten_genBES E) G).
    apply (rev_subset_card_rev_subset _ _ _ _ H).
  intro;intros.
  apply (rev_subset_then_bound _ _ _ H3);auto.
destruct (relates_decidable _ _ _ H3 x y).
apply CNT;auto.
destruct H2;try contradiction.
(*R x y*)
destruct (H0 x y);auto.
apply bnd_flatten_bnd_block in H4.
apply bnd_flatten_bnd_block in H5.
destruct (H1 x y);auto.
apply CC;auto.

apply (lem5 E (R U G) (G U pair_relation x y)).
intro;intros.
destruct H8.
apply H0;auto.
apply H3;auto.
intros;intro;intros;auto.
apply H7;auto.
intros.
assert (relates_bound (G U pair_relation x y) (flatten_genBES E) (flatten_genBES E)).
  intro;intros.
  destruct H9.
  apply H3;auto.
  destruct H9.
  rewrite H9 in *;rewrite H10 in *;auto.
destruct (relates_decidable _ _ _ H9 x0 y0).
(*G x0 y0*)
apply CNT;auto.
(*~G x0 y0*)
destruct H8.
apply IHn.
assert (rev_subset_card (flatten_genBES E) (flatten_genBES E) (remPoint (G U pair_relation x y) x y) (S n)).
  apply (card_eqv _ _ G);auto.
  split;intros.
  unfold remPoint.
  destruct (eq_nat_decide x x1).
  rewrite (eq_nat_eq _ _ e) in *.
  destruct (eq_nat_decide y y1).
  rewrite (eq_nat_eq _ _ e0) in *.
  contradiction.
  assert (beq_nat x1 x1 && beq_nat y y1=false).
    apply andb_false_iff.
    right.
    apply beq_nat_false_iff.
    intro.
    apply n3.
    apply eq_nat_is_eq;auto.
  rewrite H11.
  left;auto.
  assert (beq_nat x x1 && beq_nat y y1=false).
    apply andb_false_iff.
    left.
    apply beq_nat_false_iff.
    intro.
    apply n3.
    apply eq_nat_is_eq;auto.
  rewrite H11.
  left;auto.
  unfold remPoint in H10.
  destruct (eq_nat_decide x x1).
  rewrite (eq_nat_eq _ _ e) in *.
  destruct (eq_nat_decide y y1).
  rewrite (eq_nat_eq _ _ e0) in *.
  repeat rewrite<- beq_nat_refl in H10;inversion H10.
  assert (beq_nat x1 x1 && beq_nat y y1=false).
    apply andb_false_iff.
    right.
    apply beq_nat_false_iff.
    intro.
    apply n3.
    apply eq_nat_is_eq;auto.
  rewrite H11 in H10.
  destruct H10;auto.
  destruct H10.
  rewrite H12 in *.
  apply andb_false_iff in H11.
  destruct H11;apply beq_nat_false_iff in H11.
  contradiction.
  exfalso.
  apply H11;auto.
  assert (beq_nat x x1 && beq_nat y y1=false).
    apply andb_false_iff.
    left.
    apply beq_nat_false_iff.
    intro.
    apply n3.
    apply eq_nat_is_eq;auto.
  rewrite H11 in H10.
  destruct H10;auto.
  destruct H10.
  rewrite H12 in *.
  apply andb_false_iff in H11.
  destruct H11;apply beq_nat_false_iff in H11.
  contradiction.
  exfalso.
  apply H11;auto.

assert (n=(S n) -1).
  simpl;destruct n;auto.
rewrite H11.
apply (rev_subset_decreasing (S n) (flatten_genBES E) (flatten_genBES E) G H (G U pair_relation x y) x y);auto.
right;split;auto.
apply bnd_block_flatten_bnd;auto.
apply bnd_block_flatten_bnd;auto.
split;intro;auto.

exists R.
split;auto.
split.
intro;intros.
destruct (H1 x1 y1);auto.
split;auto.
intros;intro;intros.
apply H12;auto.
destruct (consistent_environment_rel_union _ _ _ H15).
destruct (consistent_environment_rel_union _ _ _ H18).
apply rel_union_consistent_environment;auto.
left;left;auto.
exfalso.
apply n2.
left;auto.

rewrite H2 in *.
apply REF.
Qed.

Lemma prv_system_complete : forall E:BES, forall x y:propVar, 
  (cc_max E) x y -> prv_tree E (stmt empty_relation (var x) (var y)).
Proof.
intros.
assert (is_subset (flatten_genBES E) (flatten_genBES E) (empty_relation)).
  apply is_empty.
  intros;intro.
  inversion H0.
assert (rev_subset (flatten_genBES E) (flatten_genBES E) (empty_relation)).
  apply (eqv_rev _ _ (rel_minus (max_rel (flatten_genBES E) (flatten_genBES E)) (max_rel (flatten_genBES E) (flatten_genBES E)))).
  split;intro.
  destruct H1.
  contradiction.
  inversion H1.
  apply max_rel_inverse.
  apply bound_then_is_subset.
  intro;intros.
  destruct H1;auto.
destruct (rev_subset_rev_subset_card _ _ _ H1).
apply (complete_propVar _ x0 empty_relation);auto.
exists (cc_max E).
split.
intro;intros.
destruct H3 as [R H3].
destruct H3.
destruct H4.
apply H4;auto.
split.
apply cc_relative_empty.
apply cc_max_is_cc.
left;left;auto.
Qed.
