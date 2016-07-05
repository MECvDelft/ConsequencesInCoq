Add LoadPath "somePath".

Require Export rel_reach.

Inductive is_subset (l1 l2:list booleanEquation): propVar_relation -> Prop :=
| is_empty : forall R:propVar_relation, 
  (forall x y:nat, ~R x y) -> is_subset l1 l2 R
| not_empty : forall R:propVar_relation, is_subset l1 l2 R -> 
  forall x y:nat, ~R x y -> bnd_block l1 x -> bnd_block l2 y -> 
    is_subset l1 l2 (rel_union R (pair_relation x y))
| eqv : forall R1 R2:propVar_relation, rel_eqv R1 R2 -> is_subset l1 l2 R1 -> is_subset l1 l2 R2.

Lemma separe_subset_then_union_subset : forall l1 l2:list booleanEquation, forall R1 R2:propVar_relation, 
  relates_bound R1 l1 l2 -> relates_bound R2 l1 l2 -> 
    is_subset l1 l2 R1 -> is_subset l1 l2 R2 -> is_subset l1 l2 (rel_union R1 R2).
Proof.
intros l1 l2 R1 R2 R1sub R2sub.
intros.
induction H.
induction H0.
apply is_empty.
intros;intro.
destruct H1.
apply (H _ _ H1).
apply (H0 _ _ H1).

apply (eqv l1 l2 (rel_union (rel_union R R0) (pair_relation x y)));auto.
split;intros.
destruct H4.
destruct H4.
left;auto.
right;left;auto.
right;right;auto.
destruct H4.
left;left;auto.
destruct H4.
left;right;auto.
right;auto.
apply not_empty;auto.
apply IHis_subset.
intro;intros.
apply R2sub.
left;auto.
intro.
destruct H4;auto.
apply (H _ _ H4).

apply (eqv l1 l2 (rel_union R R1));auto.
split;intro.
destruct H2.
left;auto.
right;apply H0;auto.
destruct H2.
left;auto.
right;apply H0;auto.
apply IHis_subset.
intro;intros.
apply R2sub.
apply H0;auto.

destruct (relates_decidable R2 l1 l2 R2sub x y).
apply (eqv l1 l2 (rel_union R R2));auto.
split;intro.
destruct H4.
left;left;auto.
right;auto.
destruct H4.
destruct H4.
left;auto.
destruct H4.
rewrite H4 in *.
rewrite H5 in *.
right;auto.
right;auto.
apply IHis_subset.
intro;intros.
apply R1sub.
left;auto.

apply (eqv l1 l2 (rel_union (rel_union R R2) (pair_relation x y)));auto.
split;intro.
destruct H4.
destruct H4.
left;left;auto.
right;auto.
left;right;auto.
destruct H4.
destruct H4.
left;left;auto.
right;auto.
left;right;auto.
apply not_empty;auto.
apply IHis_subset.
intro;intros.
apply R1sub.
left;auto.
intro.
destruct H4;auto.

apply (eqv l1 l2 (rel_union R1 R2));auto.
split;intro.
destruct H2.
left;apply H;auto.
right;auto.
destruct H2.
left;apply H;auto.
right;auto.
apply IHis_subset.
intro;intros.
apply R1sub.
apply H;auto.
Qed.

Lemma add_still_subset_left : forall l2 l1:list booleanEquation, forall a:booleanEquation, forall R:propVar_relation,
  is_subset l1 l2 R -> is_subset (a::l1) l2 R.
Proof.
intros.
induction H.
apply is_empty;auto.
apply not_empty;auto.
destruct a.
right;auto.
apply (eqv (a::l1) l2 R1);auto.
Qed.

Lemma add_still_subset_right : forall l2 l1:list booleanEquation, forall a:booleanEquation, forall R:propVar_relation,
  is_subset l1 l2 R -> is_subset l1 (a::l2) R.
Proof.
intros.
induction H.
apply is_empty;auto.
apply not_empty;auto.
destruct a.
right;auto.
apply (eqv l1 (a::l2) R1);auto.
Qed.

Lemma bound_then_is_subset : forall l1 l2:list booleanEquation, forall R:propVar_relation, 
  (forall x y:nat, R x y -> (bnd_block l1 x /\ bnd_block l2 y)) -> is_subset l1 l2 R.
Proof.
induction l1.
intros.
apply is_empty.
intros;intro.
destruct (H _ _ H0);auto.

induction l2;intros.
apply is_empty.
intros;intro.
destruct (H _ _ H0);auto.

destruct a.
cut (is_subset ((bEqn p p0)::l1) (a0::l2) (remove_var_left R p)).
destruct a0.
cut (is_subset ((bEqn p p0)::l1) ((bEqn p1 p2)::l2) (remove_var_right R p1)).

intros.
destruct (relates_decidable R ((bEqn p p0)::l1) ((bEqn p1 p2)::l2) H p p1).
apply (eqv ((bEqn p p0)::l1) ((bEqn p1 p2)::l2) (rel_union (rel_union (remove_var_right R p1) (remove_var_left R p)) (pair_relation p p1))).
split;intro.
destruct H2;destruct H2.
unfold remove_var_right in H2.
destruct (beq_nat p1 y);auto.
inversion H2.
unfold remove_var_left in H2.
destruct (beq_nat p x);auto.
inversion H2.
rewrite H2 in *;rewrite H3 in *;auto.
destruct (eq_nat_decide p x).
rewrite (eq_nat_eq _ _ e) in *.
destruct (eq_nat_decide p1 y).
rewrite (eq_nat_eq _ _ e0) in *.
right;unfold pair_relation;auto.
left.
left.
unfold remove_var_right.
assert (beq_nat p1 y=false).
  apply beq_nat_false_iff.
  intro.
  apply eq_nat_is_eq in H3.
  contradiction.
rewrite H3;auto.
left.
right.
unfold remove_var_left.
unfold remove_var_right.
assert (beq_nat p x=false).
  apply beq_nat_false_iff.
  intro.
  apply eq_nat_is_eq in H3.
  contradiction.
rewrite H3;auto.
apply separe_subset_then_union_subset;auto.
intro;intros.
apply H.
destruct H2.
unfold remove_var_right in H2.
destruct (beq_nat p1 y);auto.
inversion H2.
unfold remove_var_left in H2.
destruct (beq_nat p x);auto.
inversion H2.
intro;intros.
destruct H2.
rewrite H2 in *.
rewrite H3 in *.
simpl;auto.
apply separe_subset_then_union_subset;auto.
intro;intros.
unfold remove_var_right in H2.
apply H.
destruct (beq_nat p1 y);auto.
inversion H2.
intro;intros.
unfold remove_var_left in H2.
apply H.
destruct (beq_nat p x);auto.
inversion H2.
apply (eqv (bEqn p p0::l1) (bEqn p1 p2::l2) (rel_union empty_relation (pair_relation p p1)));auto.
split;intro.
destruct H2;auto.
inversion H2.
right;auto.
apply not_empty;auto.
apply is_empty;auto.
left;auto.
left;auto.

apply (eqv ((bEqn p p0)::l1) ((bEqn p1 p2)::l2)  (rel_union (remove_var_right R p1) (remove_var_left R p))).
split;intro.
destruct H2.
unfold remove_var_right in H2.
destruct (beq_nat p1 y);auto.
inversion H2.
unfold remove_var_left in H2.
destruct (beq_nat p x);auto.
inversion H2.
destruct (eq_nat_decide p x).
rewrite (eq_nat_eq _ _ e) in *.
destruct (eq_nat_decide p1 y).
rewrite (eq_nat_eq _ _ e0) in *.
exfalso;auto.
left.
unfold remove_var_right.
assert (beq_nat p1 y=false).
  apply beq_nat_false_iff.
  intro.
  apply eq_nat_is_eq in H3.
  contradiction.
rewrite H3;auto.
right.
unfold remove_var_left.
assert (beq_nat p x=false).
  apply beq_nat_false_iff.
  intro.
  apply eq_nat_is_eq in H3.
  contradiction.
rewrite H3;auto.
apply separe_subset_then_union_subset;auto.
intro;intros.
apply H.
unfold remove_var_right in H2.
destruct (beq_nat p1 y);auto.
inversion H2.
intro;intros.
apply H.
unfold remove_var_left in H2.
destruct (beq_nat p x);auto.
inversion H2.

apply add_still_subset_right.
apply IHl2.
intros.
unfold remove_var_right in H0.
destruct (eq_nat_decide p1 y).
rewrite (eq_nat_eq _ _ e) in *.
rewrite<- (beq_nat_refl _) in H0.
inversion H0.
destruct (beq_nat p1 y).
inversion H0.
destruct (H _ _ H0).
split;auto.
destruct H2;auto.
exfalso.
apply n.
apply eq_nat_is_eq;auto.

apply add_still_subset_left.
apply IHl1.
intros.
unfold remove_var_left in H0.
destruct (eq_nat_decide p x).
rewrite (eq_nat_eq _ _ e) in *.
rewrite<- (beq_nat_refl x) in H0.
inversion H0.
destruct (beq_nat p x).
inversion H0.
destruct (H _ _ H0).
split;auto.
destruct H1;auto.
exfalso.
apply n.
apply eq_nat_is_eq;auto.
Qed.

Inductive rev_subset (l1 l2:list booleanEquation): propVar_relation -> Prop :=
| is_full : forall R:propVar_relation, 
  (forall x y:nat, R x y <-> (bnd_block l1 x /\ bnd_block l2 y)) -> rev_subset l1 l2 R
| not_full : forall R:propVar_relation, rev_subset l1 l2 R -> 
  forall x y:nat, R x y -> rev_subset l1 l2 (remPoint R x y)
| eqv_rev : forall R1 R2:propVar_relation, rel_eqv R1 R2 -> rev_subset l1 l2 R1 -> rev_subset l1 l2 R2.

Lemma max_rel_inverse : forall l1 l2:list booleanEquation, forall R:propVar_relation, is_subset l1 l2 R ->
  rev_subset l1 l2 (rel_minus (max_rel l1 l2) R).
Proof.
intros l1 l2 R H.
induction H.
apply is_full.
split;intro.
destruct H0.
destruct H0;auto.
unfold rel_minus.
unfold max_rel.
split;auto.
apply (eqv_rev l1 l2 (remPoint (rel_minus (max_rel l1 l2) R) x y)).
split;intro.
unfold remPoint in H3.
destruct (eq_nat_decide x x0).
rewrite (eq_nat_eq _ _ e) in *.
destruct (eq_nat_decide y y0).
rewrite (eq_nat_eq _ _ e0) in *.
repeat rewrite <- (beq_nat_refl _) in H3.
inversion H3.
assert (beq_nat x0 x0 && beq_nat y y0=false).
  apply andb_false_iff.
  right.
  apply beq_nat_false_iff.
  intro.
  apply eq_nat_is_eq in H4;auto.
rewrite H4 in H3.
unfold rel_minus in H3.
destruct H3.
destruct H3.
split.
split;auto.
unfold rel_union.
intro.
destruct H7;auto.
destruct H7.
apply eq_nat_is_eq in H8;auto.
split;auto.
assert (beq_nat x x0 && beq_nat y y0=false).
  apply andb_false_iff.
  left.
  apply beq_nat_false_iff.
  intro.
  apply eq_nat_is_eq in H4;auto.
rewrite H4 in H3.
destruct H3.
destruct H3.
split;auto.
unfold rel_union.
intro.
assert (beq_nat x x0 && beq_nat y y0=true).
  destruct (beq_nat x x0 && beq_nat y y0);auto.
  destruct H3.
  destruct H3.
  destruct H4;try contradiction.
  destruct H4.
  exfalso.
  apply n.
  apply eq_nat_is_eq;auto.
rewrite H5 in H3;auto.
unfold remPoint.
destruct H3.
unfold rel_union in H4.
destruct (eq_nat_decide x x0).
rewrite (eq_nat_eq _ _ e) in *.
destruct (eq_nat_decide y y0).
rewrite (eq_nat_eq _ _ e0) in *.
exfalso.
apply H4.
right.
split;auto.
assert (beq_nat x0 x0 && beq_nat y y0=false).
  apply andb_false_iff.
  right.
  apply beq_nat_false_iff.
  intro.
  apply eq_nat_is_eq in H5;auto.
rewrite H5.
split;auto.
assert (beq_nat x x0 && beq_nat y y0=false).
  apply andb_false_iff.
  left.
  apply beq_nat_false_iff.
  intro.
  apply eq_nat_is_eq in H5;auto.
rewrite H5.
split;auto.
apply not_full;auto.
unfold rel_minus.
split;auto.
split;auto.
apply (eqv_rev l1 l2 (rel_minus (max_rel l1 l2) R1));auto.
split;intro.
destruct H1.
split;auto.
intro.
apply H2.
apply H;auto.
destruct H1.
split;auto.
intro.
apply H2.
apply H;auto.
Qed.

Lemma rev_subset_then_bound : forall l1 l2:list booleanEquation, forall R:propVar_relation, rev_subset l1 l2 R -> 
  forall x y:nat, R x y -> (bnd_block l1 x /\ bnd_block l2 y).
Proof.
intros.
induction H.
apply H;auto.
apply IHrev_subset.
unfold remPoint in H0.
destruct (beq_nat x0 x && beq_nat y0 y);auto.
inversion H0.
apply IHrev_subset.
apply H;auto.
Qed.

Inductive rev_subset_card (l1 l2:list booleanEquation): propVar_relation -> nat -> Prop :=
| card_full : forall R:propVar_relation, 
  (forall x y:nat, R x y <-> (bnd_block l1 x /\ bnd_block l2 y)) -> rev_subset_card l1 l2 R 1
| card_not_full : forall R:propVar_relation, forall n:nat, rev_subset_card l1 l2 R n -> 
  forall x y:nat, R x y -> rev_subset_card l1 l2 (remPoint R x y) (S n)
| card_eqv : forall R1 R2:propVar_relation, forall n:nat, rev_subset_card l1 l2 R1 n -> 
  rel_eqv R1 R2 -> rev_subset_card l1 l2 R2 n.

Lemma rev_card_gt0 : forall l1 l2:list booleanEquation, forall G:propVar_relation, forall n:nat, 
  rev_subset_card l1 l2 G n -> n>0.
Proof.
intros.
induction H;auto.
Qed.

Lemma rev_subset_rev_subset_card : forall l1 l2:list booleanEquation, forall R:propVar_relation, 
  rev_subset l1 l2 R -> exists n:nat, rev_subset_card l1 l2 R n.
Proof.
intros.
induction H.
exists 1.
apply card_full;auto.

destruct IHrev_subset as [n IH].
exists (S n);apply card_not_full;auto.

destruct IHrev_subset as [n IH].
exists n.
apply (card_eqv _ _ R1);auto.
Qed.

Lemma rev_subset_card_rev_subset : forall l1 l2:list booleanEquation, forall n:nat, forall R:propVar_relation, 
  rev_subset_card l1 l2 R n -> rev_subset l1 l2 R.
Proof.
intros.
induction H.
apply is_full;auto.

apply not_full;auto.

apply (eqv_rev _ _ R1);auto.
Qed.

Lemma rev_subset_decreasing : forall n:nat, 
  forall l1 l2:list booleanEquation, forall G':propVar_relation, rev_subset_card l1 l2 G' n -> 
    forall G:propVar_relation, forall x y:propVar, ~G' x y -> G x y -> bnd_block l1 x -> bnd_block l2 y -> 
      rel_eqv G (G' U pair_relation x y) -> rev_subset_card l1 l2 G (n-1).
Proof.
intros n l1 l2 G' H.
induction H as [G'|G'|G'];intros.
exfalso.
apply H0.
apply H;auto.

unfold remPoint in H1.
destruct (eq_nat_decide x x0).
rewrite (eq_nat_eq _ _ e) in *.
destruct (eq_nat_decide y y0).
rewrite (eq_nat_eq _ _ e0) in *.
simpl.
assert (n-0=n).
  clear.
  destruct n;auto.
rewrite H6.
clear H1.
apply (card_eqv _ _ G');auto.
split;intros.
apply H5.
destruct (eq_nat_decide x0 x1).
rewrite (eq_nat_eq _ _ e1) in *.
destruct (eq_nat_decide y0 y1).
rewrite (eq_nat_eq _ _ e2) in *.
right;split;auto.
left.
unfold remPoint.
assert (beq_nat x1 x1 && beq_nat y0 y1=false).
  apply andb_false_iff.
  right.
  apply beq_nat_false_iff;intro.
  apply n0;apply eq_nat_is_eq;auto.
rewrite H7;auto.
left.
unfold remPoint.
assert (beq_nat x0 x1 && beq_nat y0 y1=false).
  apply andb_false_iff.
  left.
  apply beq_nat_false_iff;intro.
  apply n0;apply eq_nat_is_eq;auto.
rewrite H7;auto.
assert ((remPoint G' x0 y0 U pair_relation x0 y0) x1 y1).
  apply H5;auto.
destruct H7.
unfold remPoint in H7.
destruct (beq_nat x0 x1 && beq_nat y0 y1);auto.
inversion H7.
destruct H7.
rewrite H7 in *.
rewrite H8 in *;auto.

assert (beq_nat x0 x0&&beq_nat y y0=false).
  apply andb_false_iff.
  right.
  apply beq_nat_false_iff.
  intro.
  apply n0.
  apply eq_nat_is_eq;auto.
rewrite H6 in H1.
assert (~G x0 y).
  intro.
  destruct (H5 x0 y).
  destruct (H8 H7).
  unfold remPoint in H10.
  repeat rewrite<- beq_nat_refl in H10;auto.
  destruct H10.
  rewrite H11 in *.
  contradiction.

assert (S n - 1 = S (n-1)).
  specialize (rev_card_gt0 _ _ _ _ H).
  clear.
  intros.
  induction n;simpl;auto.
  exfalso.
  apply (gt_irrefl _ H).
  assert (n-0=n).
    destruct n;simpl;auto.
  rewrite H0;auto.
rewrite H8.
apply (card_eqv _ _ (remPoint (G U pair_relation x0 y) x0 y)).
apply card_not_full.
apply (IHrev_subset_card _ x0 y0);auto.
left;auto.
split;intro.
destruct H9.
destruct (H5 x1 y1).
specialize (H10 H9).
destruct H10.
clear H11.
unfold remPoint in H10.
assert (beq_nat x0 x1 && beq_nat y y1=false).
  apply not_true_is_false.
  intro.
  rewrite H11 in H10;auto.
rewrite H11 in H10.
left;auto.
right;auto.
destruct H9.
rewrite H9 in *.
rewrite H10 in *.
left;auto.
destruct (H5 x1 y1).
destruct (eq_nat_decide x0 x1).
rewrite (eq_nat_eq _ _ e0) in *.
destruct (eq_nat_decide y y1).
rewrite (eq_nat_eq _ _ e1) in *.
right;split;auto.
left.
apply H11.
destruct (eq_nat_decide y0 y1).
rewrite (eq_nat_eq _ _ e1) in *;right;split;auto.
left.
unfold remPoint.
assert (beq_nat x1 x1&&beq_nat y y1=false).
  apply andb_false_iff.
  right.
  apply beq_nat_false_iff.
  intro.
  apply n1.
  apply eq_nat_is_eq;auto.
rewrite H12.
destruct H9;auto.
destruct H9.
exfalso.
apply n2.
apply eq_nat_is_eq;auto.
left.
apply H11.
left.
unfold remPoint.
assert (beq_nat x0 x1&&beq_nat y y1=false).
  apply andb_false_iff.
  left.
  apply beq_nat_false_iff.
  intro.
  apply n1.
  apply eq_nat_is_eq;auto.
rewrite H12.
destruct H9;auto.
destruct H9.
exfalso.
apply n1.
apply eq_nat_is_eq;auto.
right;split;auto.
split;intro.
unfold remPoint in H9.
assert (beq_nat x0 x1 && beq_nat y y1=false).
  apply not_true_is_false.
  intro.
  rewrite H10 in H9;auto.
rewrite H10 in H9.
destruct H9;auto.
destruct H9.
rewrite H9 in *;rewrite H11 in *.
apply andb_false_iff in H10.
destruct H10;apply beq_nat_false_iff in H10;exfalso;apply H10;auto.
unfold remPoint.
assert (beq_nat x0 x1&&beq_nat y y1=false).
  apply not_true_is_false.
  intro.
  apply andb_true_iff in H10.
  destruct H10.
  apply beq_nat_true_iff in H10;apply beq_nat_true_iff in H11.
  rewrite H10 in *;rewrite H11 in *.
  contradiction.
rewrite H10.
left;auto.

assert (S n - 1 = S (n-1)).
  specialize (rev_card_gt0 _ _ _ _ H).
  clear.
  intros.
  induction n;simpl;auto.
  exfalso.
  apply (gt_irrefl _ H).
  assert (n-0=n).
    destruct n;simpl;auto.
  rewrite H0;auto.
rewrite H6.
assert (beq_nat x x0&&beq_nat y y0=false).
  apply andb_false_iff.
  left.
  apply beq_nat_false_iff.
  intro.
  apply n0.
  apply eq_nat_is_eq;auto.
rewrite H7 in H1;clear H7.
remember x0 as a.
remember y0 as b.
remember G' as R.
apply (card_eqv _ _ (remPoint (G U pair_relation x y) x y)).
apply card_not_full;auto.
apply (IHrev_subset_card _ a b);auto.
left;auto.
split;intro.
destruct H7.
destruct (H5 x1 y1).
destruct (H8 H7).
clear H8 H9.
unfold remPoint in H10.
destruct (beq_nat x x1 && beq_nat y y1);left;auto.
inversion H10.
destruct H10.
rewrite H10 in *.
rewrite H11 in *.
clear H8 H9.
right;split;auto.
destruct H7.
rewrite H7 in *.
rewrite H8 in *.
left;auto.
destruct (eq_nat_decide x x1).
rewrite (eq_nat_eq _ _ e) in *.
destruct (eq_nat_decide y y1).
rewrite (eq_nat_eq _ _ e0) in *.
right;split;auto.
left.
apply H5.
destruct H7.
left.
unfold remPoint.
assert (beq_nat x1 x1 && beq_nat y y1=false).
  apply not_true_is_false.
  intro.
  apply andb_true_iff in H8.
  destruct H8.
  apply beq_nat_true_iff in H9.
  apply n1;apply eq_nat_is_eq;auto.
rewrite H8.
assumption.
destruct H7.
exfalso;apply n0;apply eq_nat_is_eq;auto.
destruct H7.
left.
apply H5.
left.
unfold remPoint.
assert (beq_nat x x1 && beq_nat y y1=false).
  apply not_true_is_false.
  intro.
  apply andb_true_iff in H8.
  destruct H8.
  apply beq_nat_true_iff in H8.
  apply n1;apply eq_nat_is_eq;auto.
rewrite H8.
assumption.
destruct H7.
rewrite H7 in *.
rewrite H8 in *.
left.
assumption.
right;split;auto.
split;intro.
unfold remPoint in H7.
destruct (eq_nat_decide x x1).
rewrite (eq_nat_eq _ _ e) in *.
destruct (eq_nat_decide y y1).
rewrite (eq_nat_eq _ _ e0) in *.
repeat rewrite<- beq_nat_refl in H7;inversion H7.
assert (beq_nat x1 x1 && beq_nat y y1=false).
  apply not_true_is_false.
  intro.
  apply andb_true_iff in H8.
  destruct H8.
  apply beq_nat_true_iff in H9.
  apply n1;apply eq_nat_is_eq;auto.
rewrite H8 in H7.
destruct H7;auto.
destruct H7.
exfalso.
apply n1.
apply eq_nat_is_eq;auto.
destruct (beq_nat x x1 && beq_nat y y1).
inversion H7.
destruct H7;auto.
destruct H7.
exfalso.
apply n1.
apply eq_nat_is_eq;auto.
unfold remPoint.
destruct (eq_nat_decide x x1).
rewrite (eq_nat_eq _ _ e) in *.
destruct (eq_nat_decide y y1).
rewrite (eq_nat_eq _ _ e0) in *.
exfalso.
destruct (H5 x1 y1).
destruct (H8 H7).
unfold remPoint in H10.
repeat rewrite<- beq_nat_refl in H10.
simpl in H10;auto.
destruct H10.
apply n0.
apply eq_nat_is_eq;auto.
assert (beq_nat x1 x1 && beq_nat y y1=false).
  apply andb_false_iff.
  right.
  apply not_true_is_false.
  intro.
  apply n1.
  apply beq_nat_true_iff in H8.
  apply eq_nat_is_eq;auto.
rewrite H8;left;auto.
assert (beq_nat x x1 && beq_nat y y1=false).
  apply andb_false_iff.
  left.
  apply not_true_is_false.
  intro.
  apply n1.
  apply beq_nat_true_iff in H8.
  apply eq_nat_is_eq;auto.
rewrite H8;left;auto.

assert (~G' x y).
  intro.
  apply H1.
  apply H0;auto.
assert (rev_subset_card l1 l2 (R2 U pair_relation x y) (n - 1)).
  apply (IHrev_subset_card _ x y);auto.
  right;split;auto.
  split;intro.
  destruct H7.
  left;apply H0;auto.
  right;auto.
  destruct H7.
  left;apply H0;auto.
  right;auto.
apply (card_eqv _ _ (R2 U pair_relation x y));auto.
split;intro;apply H5;auto.
Qed.

