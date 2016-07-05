Add LoadPath "somePath".

Require Export prv_tree.

(*----------soundness----------*)

Lemma AS1_sound : forall E:BES, forall a b c:propForm, forall G:propVar_relation, 
  rel_cc_on_propForm E G (andp a (andp b c)) (andp (andp a b) c).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
destruct H0.
destruct H1.
simpl;auto.
Qed.

Lemma AS2_sound: forall E:BES, forall a b c:propForm, forall G:propVar_relation, 
  rel_cc_on_propForm E G (andp (andp a b) c) (andp a (andp b c)).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
destruct H0.
destruct H0.
simpl;auto.
Qed.

Lemma AS3_sound: forall E:BES, forall a b c:propForm, forall G:propVar_relation, 
  rel_cc_on_propForm E G (orp a (orp b c)) (orp (orp a b) c).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
destruct H0;auto.
Qed.

Lemma AS4_sound: forall E:BES, forall a b c:propForm, forall G:propVar_relation, 
  rel_cc_on_propForm E G (orp (orp a b) c) (orp a (orp b c)).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
destruct H0;auto.
Qed.

Lemma COM1_sound: forall E:BES, forall a b:propForm, forall G:propVar_relation, 
  rel_cc_on_propForm E G (andp a b) (andp b a).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
Qed.

Lemma COM2_sound: forall E:BES, forall a b:propForm, forall G:propVar_relation, 
  rel_cc_on_propForm E G (orp a b) (orp b a).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
Qed.

Lemma DS1_sound: forall E:BES, forall a b c:propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G (orp a (andp b c)) (andp (orp a b) (orp a c)).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
destruct H0;auto.
Qed.

Lemma DS2_sound: forall E:BES, forall a b c:propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G (andp (orp a b) (orp a c)) (orp a (andp b c)).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
destruct H0;auto.
destruct H1;auto.
Qed.

Lemma DS3_sound: forall E:BES, forall a b c:propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G (andp a (orp b c)) (orp (andp a b) (andp a c)).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
destruct H1;auto.
Qed.

Lemma DS4_sound: forall E:BES, forall a b c:propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G (orp (andp a b) (andp a c)) (andp a (orp b c)).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;destruct H0;auto.
Qed.

Lemma AB1_sound: forall E:BES, forall a b: propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G (orp a (andp a b)) a.
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
destruct H0;auto.
Qed.

Lemma AB2_sound: forall E:BES, forall a b: propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G a (orp a (andp a b)).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
left;auto.
Qed.

Lemma ID1_sound: forall E:BES, forall a: propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G a (andp a a).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
split;auto.
Qed.

Lemma ID2_sound: forall E:BES, forall a: propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G (orp a a) a.
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
Qed.

Lemma SUP_sound: forall E:BES, forall a b:propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G a (orp a b).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
left;auto.
Qed.

Lemma INF_sound: forall E:BES, forall a b:propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G (andp a b) a.
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
Qed.

Lemma TOP_sound: forall E:BES, forall a:propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G a (andp a top).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl;split;auto.
Qed.

Lemma BOT_sound: forall E:BES, forall a:propForm, forall G:propVar_relation,
  rel_cc_on_propForm E G (orp a bot) a.
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
simpl.
destruct H0;auto.
inversion H0.
Qed.

Lemma CTX_sound: forall E:BES, forall a b c:propForm, forall x:propVar, 
  forall G:propVar_relation, (rel_cc_on_propForm E G a b) -> 
    (rel_cc_on_propForm E G (replace c x a) (replace c x b)).
Proof.
intros.
destruct H as [R H].
destruct H.
destruct H0.
exists R;split;auto.
split;auto.
intros;induction c;simpl in *;auto.
destruct (eq_nat_decide x p).
rewrite (eq_nat_eq x p e) in *.
simpl in *.
rewrite<- (beq_nat_refl p) in *.
apply H1;auto.
assert (beq_nat x p=false).
  apply beq_nat_false_iff.
  intro.
  apply n.
  apply eq_nat_is_eq;auto.
rewrite H4 in *;auto.
destruct H3.
left;auto.
right;auto.
destruct H3;split;auto.
Qed.

Lemma TRA_sound: forall E:BES, forall a b c:propForm, forall G:propVar_relation, 
    (((rel_cc_on_propForm E G a b) /\ (rel_cc_on_propForm E G b c)) ->
      (rel_cc_on_propForm E G a c)).
Proof.
intros.
apply (rel_cc_trans E G a b c);auto.
Qed.

Lemma REF_sound: forall E:BES, forall a:propForm, forall G:propVar_relation, 
  (rel_cc_on_propForm E G a a).
Proof.
intros.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros;auto.
Qed.

Lemma CC_sound : forall E:BES, forall x y:propVar, forall G:propVar_relation,
  (bnd E x) /\ (bnd E y) /\ (rank E x=rank E y) -> 
    (rel_cc_on_propForm E (G U (pair_relation x y)) (rhs E x) (rhs E y)) -> (rel_cc_on_propForm E G (var x) (var y)).
Proof.
intros.
destruct H;destruct H1.
destruct H0 as [R H0].
destruct H0.
destruct H3.
assert (relative_cc E (rel_union R (pair_relation x y)) G).
  intro;intros.
  destruct H5.
  destruct (H3 x0 y0);auto.
  split;auto.
  intros;intro;intros.
  apply H7;auto.
  destruct (consistent_environment_rel_union theta _ _ H10).
  destruct (consistent_environment_rel_union theta _ _ H12).
  apply rel_union_consistent_environment;split;auto.
  apply rel_union_consistent_environment;split;auto.
  destruct H5.
  rewrite H5 in *.
  rewrite H6 in *.
  split;auto.
  intros;intro;intros.
  apply H4;auto.
  destruct (consistent_environment_rel_union theta _ _ H9).
  destruct (consistent_environment_rel_union theta _ _ H11).
  apply rel_union_consistent_environment;split;auto.
  apply rel_union_consistent_environment;split;auto.
exists (R U pair_relation x y).
split.
intro;intros.
destruct H6.
apply H0;auto.
destruct H6.
rewrite H6 in *.
rewrite H7 in *;auto.
split;apply bnd_block_flatten_bnd;auto.
split;auto.
intros.
apply (H6 x y);auto.
left;right;unfold pair_relation;auto.
Qed.

Lemma CNT_sound: forall E:BES, forall x y:propVar, forall G:propVar_relation,
  ((G x y) -> (rel_cc_on_propForm E G (var x) (var y))).
Proof.
intros.
exists empty_relation.
split.
apply empty_relation_relates_bound.
split.
apply empty_relation_rel_cc.
intros.
apply (H0 x);auto.
right;auto.
Qed.

Definition mk_rel_cc(E:BES)(s : statement) : Prop :=
match s with
| stmt G f g => rel_cc_on_propForm E G f g
end.

Lemma soundness: forall E:BES, forall f g:propForm, forall G:propVar_relation, 
  prv_tree E (stmt G f g) -> mk_rel_cc E (stmt G f g).
Proof.
intros.
induction H.
apply AS1_sound.
apply AS2_sound.
apply AS3_sound.
apply AS4_sound.
apply COM1_sound.
apply COM2_sound.
apply DS1_sound.
apply DS2_sound.
apply DS3_sound.
apply DS4_sound.
apply AB1_sound.
apply AB2_sound.
apply ID1_sound.
apply ID2_sound.
apply SUP_sound.
apply INF_sound.
apply TOP_sound.
apply BOT_sound.
apply CTX_sound.
assumption.
apply (TRA_sound E a b c).
split;assumption.
apply REF_sound.
apply (CC_sound).
auto.
unfold mk_rel_cc in IHprv_tree.
assumption.
apply CNT_sound.
assumption.
Qed.

Lemma prv_system_sound : forall E:BES, forall x y:propVar, bnd E x -> bnd E y -> 
  prv_tree E (stmt empty_relation (var x) (var y)) -> (cc_max E) x y.
Proof.
intros.
destruct (eq_nat_decide x y).
rewrite (eq_nat_eq _ _ e) in *.
exists (pair_relation y y).
split.
intro;intros.
destruct H2.
rewrite H2 in *.
rewrite H3 in *.
split;auto.
intros;intro;intros;auto.
split.
intro;intros.
destruct H2.
rewrite H2 in *;rewrite H3 in *.
split;apply bnd_block_flatten_bnd;auto.
split;auto.
apply (propForm_cons_cc_max E x y);auto.
apply soundness;auto.
Qed.

