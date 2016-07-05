Add LoadPath "somePath".

Require Export List.
Require Export Bool.
Require Export Arith.

Coercion is_true : bool >-> Sortclass.

(*----------propForm----------*)

Definition propVar:=nat.

Inductive propForm : Set :=
| top : propForm
| bot : propForm
| var : propVar -> propForm
| orp : propForm -> propForm -> propForm
| andp : propForm -> propForm -> propForm.

Definition T:=top.
Definition B:=bot.
Notation "A \/p B" := (orp A B) (at level 80).
Notation "A /\p B" := (andp A B) (at level 85).

Fixpoint uses (f:propForm)(x:propVar) : Prop :=
match f with 
| a \/p b => (uses a x) \/ (uses b x)
| a /\p b => (uses a x) \/ (uses b x)
| var y => x=y
| T => False
| B => False
end.

Fixpoint replace (f:propForm)(x:propVar)(g:propForm):propForm :=
match f with
| a /\p b => (replace a x g) /\p (replace b x g)
| a \/p b => (replace a x g) \/p (replace b x g)
| var y => if (beq_nat x y) then g else var y
| _ => f
end.

Definition environment := propVar -> bool.

Definition redefineEnvironment (theta:environment)(x:propVar)(s:bool) : environment :=
fun (y:propVar) => if beq_nat x y then s else theta y.

Definition full_environment (x:propVar) : bool := true.

Definition empty_environment (x:propVar) : bool := false.

Definition environment_point (x y:propVar) := if beq_nat x y then true else false.

Definition environment_max_point (x y:propVar) := if beq_nat x y then false else true.

Notation "theta [ x := f ]" := (redefineEnvironment theta x f) (at level 90).
Notation "f [ X := g ]" := (replace f X g)(at level 90).

Definition environment_union (theta1 theta2:environment)(x:propVar) := (theta1 x) || (theta2 x).

Definition environment_intersect (theta1 theta2:environment)(x:propVar) := (theta1 x) && (theta2 x).

Fixpoint propForm_solution (f:propForm)(theta:environment) : Prop :=
match f with
| a \/p b => (propForm_solution a theta) \/ (propForm_solution b theta)
| a /\p b => (propForm_solution a theta) /\ (propForm_solution b theta)
| var x => theta x
| T => True
| B => False
end.

Notation "[[ f ]] theta" := (propForm_solution f theta) (at level 30).

Lemma environment_union_grows : forall f:propForm, forall th1 th2:environment, 
  ([[f]]th1 \/ [[f]]th2) -> [[f]]environment_union th1 th2.
Proof.
intros.
destruct H.
induction f;simpl in *;auto.
apply orb_true_iff;left;auto.
destruct H;auto.
destruct H;auto.
induction f;simpl in *;auto.
apply orb_true_iff;right;auto.
destruct H;auto.
destruct H;auto.
Qed.

Lemma propForm_solution_decidable : forall f:propForm, forall theta:environment,
  [[f]]theta \/ ~[[f]]theta.
Proof.
intros.
induction f;simpl in *.
left;auto.
right;intro;auto.
destruct (bool_dec (theta p) true).
left;auto.
right;intro.
apply n;auto.
destruct IHf1.
left;left;auto.
destruct IHf2.
left;right;auto.
right;intro.
destruct H1;contradiction.
destruct IHf1.
destruct IHf2.
left;split;auto.
right;intro.
destruct H1;contradiction.
right;intro.
destruct H0;contradiction.
Qed.

Lemma full_environment_maximal : forall f:propForm, forall theta:environment, 
  [[f]]theta -> [[f]]full_environment.
Proof.
intros.
induction f;simpl in *;auto.
destruct H;auto.
destruct H;split;auto.
Qed.

Lemma empty_environment_minimal : forall f:propForm, forall theta:environment, 
  ~[[f]]theta -> ~[[f]]empty_environment.
Proof.
intros;intro.
induction f;simpl in *;auto.
unfold empty_environment in H0.
inversion H0.
destruct H0.
assert (~[[f1]]theta).
intro.
apply H;auto.
apply IHf1;auto.
assert (~[[f2]]theta).
intro.
apply H;auto.
apply IHf2;auto.
destruct H0.
destruct (propForm_solution_decidable f1 theta).
destruct (propForm_solution_decidable f2 theta).
apply H;split;auto.
apply IHf2;auto.
apply IHf1;auto.
Qed.

Lemma propForm_solution_deMorgan_conj : forall f1 f2:propForm, forall theta:environment,
  ~ ([[f1]]theta /\ [[f2]]theta) -> (~[[f1]]theta \/ ~[[f2]]theta).
Proof.
intros.
destruct (propForm_solution_decidable f1 theta).
right;intro.
apply H.
split;auto.
left;auto.
Qed.

Lemma environment_point_minimal : forall f:propForm, forall x:propVar, forall theta:environment,
  theta x -> ~[[f]]theta -> ~[[f]](environment_point x).
Proof.
intros.
induction f;simpl in *;auto.
destruct (eq_nat_decide x p).
rewrite (eq_nat_eq x p e) in *.
contradiction.
destruct (beq_nat_false_iff x p).
assert (x<>p).
intro.
apply (eq_nat_is_eq) in H3.
contradiction.
specialize (H2 H3).
intro.
unfold environment_point in H4.
rewrite H2 in H4.
inversion H4.
intro.
destruct H1.
assert (~[[f1]]theta).
intro.
apply H0.
left;auto.
apply IHf1;auto.
assert (~[[f2]]theta).
intro.
apply H0.
right;auto.
apply IHf2;auto.
intro.
destruct H1.
cut (~[[f1]]theta \/ ~[[f2]]theta).
intro.
destruct H3.
apply IHf1;auto.
apply IHf2;auto.
apply propForm_solution_deMorgan_conj;auto.
Qed.

Lemma environment_union_distributes: forall theta1 theta2:environment, forall f1 f2:propForm,
  [[f1]]theta1 /\ [[f2]]theta2 -> 
    ([[f1]](environment_union theta1 theta2) /\ [[f2]](environment_union theta1 theta2)).
Proof.
intros.
destruct H.
split.
induction f1;simpl in *.
assumption.
inversion H.
unfold environment_union.
apply (orb_true_iff (theta1 p) (theta2 p)).
left;assumption.
destruct H.
left;apply (IHf1_1 H).
right;apply (IHf1_2 H).
destruct H.
split.
apply (IHf1_1 H).
apply (IHf1_2 H1).
induction f2;simpl in *.
assumption.
inversion H0.
unfold environment_union.
apply (orb_true_iff (theta1 p) (theta2 p)).
right;assumption.
destruct H0.
left;apply (IHf2_1 H0).
right;apply (IHf2_2 H0).
destruct H0.
split.
apply (IHf2_1 H0).
apply (IHf2_2 H1).
Qed.

Lemma environment_intersect_distributes_neg: forall theta1 theta2:environment, forall f1 f2:propForm,
  ~[[f1]]theta1 /\ ~[[f2]]theta2 -> 
    (~[[f1]](environment_intersect theta1 theta2) /\ ~[[f2]](environment_intersect theta1 theta2)).
Proof.
intros.
destruct H.
split.
induction f1;simpl in *;auto.
unfold environment_intersect.
intro.
destruct (andb_true_iff (theta1 p) (theta2 p)).
destruct (H2 H1);auto.
assert (~[[f1_1]]theta1).
intro;apply H;left;auto.
assert (~[[f1_2]]theta1).
intro;apply H;right;auto.
intro.
destruct H3;auto.
apply IHf1_1;auto.
apply IHf1_2;auto.
intro.
destruct (propForm_solution_deMorgan_conj f1_1 f1_2 theta1 H).
destruct H1.
apply IHf1_1;auto.
destruct H1.
apply IHf1_2;auto.

induction f2;simpl in *;auto.
unfold environment_intersect.
intro.
destruct (andb_true_iff (theta1 p) (theta2 p)).
destruct (H2 H1);auto.
assert (~[[f2_1]]theta2).
intro;apply H0;left;auto.
assert (~[[f2_2]]theta2).
intro;apply H0;right;auto.
intro.
destruct H3;auto.
apply IHf2_1;auto.
apply IHf2_2;auto.
intro.
destruct (propForm_solution_deMorgan_conj f2_1 f2_2 theta2 H0).
destruct H1.
apply IHf2_1;auto.
destruct H1.
apply IHf2_2;auto.
Qed.





Fixpoint mxUsed(f:propForm):propVar:=
match f with
| var x => x
| g1 /\p g2 => max (mxUsed g1) (mxUsed g2)
| g1 \/p g2 => max (mxUsed g1) (mxUsed g2)
| _ => 0
end.

Lemma maxlteq : forall x y z:nat, (x<=y\/x<=z)->x<=(max y z).
Proof.
intros.
destruct (Max.max_spec y z).
destruct H0.
rewrite H1 in *.
destruct H;auto.
assert (y<=z).
  apply lt_le_weak;auto.
apply (le_trans _ y);auto.
destruct H0.
rewrite H1 in *.
destruct H;auto.
apply (le_trans _ z);auto.
Qed.

Lemma uses_lteq_mxUsed : forall f:propForm, forall x:propVar, uses f x -> x<=(mxUsed f).
Proof.
induction f;simpl in *;intros;auto.
inversion H.
inversion H.
rewrite H in *;auto.
apply maxlteq.
destruct H;auto.
apply maxlteq.
destruct H;auto.
Qed.

Lemma suc_mxUsed_unused : forall f:propForm, ~uses f (S (mxUsed f)).
Proof.
induction f;simpl in *;intros;auto.
intro.
rewrite Max.succ_max_distr in H.
destruct (Max.max_spec (S (mxUsed f1)) (S (mxUsed f2))).
destruct H0.
rewrite H1 in *.
destruct H.
clear H1.
specialize (uses_lteq_mxUsed _ _ H).
intro.
apply le_S_gt in H1.
apply lt_n_Sm_le in H0.
apply le_S_gt in H0.
apply (gt_asym _ _ H0);auto.
apply IHf2;auto.
destruct H0.
rewrite H1 in *.
destruct H.
apply IHf1;auto.
clear H1.
specialize (uses_lteq_mxUsed _ _ H).
intro.
apply le_S_gt in H1.
apply lt_n_Sm_le in H0.
apply (le_not_gt _ _ H0);auto.

intro.
rewrite Max.succ_max_distr in H.
destruct (Max.max_spec (S (mxUsed f1)) (S (mxUsed f2))).
destruct H0.
rewrite H1 in *.
destruct H.
clear H1.
specialize (uses_lteq_mxUsed _ _ H).
intro.
apply le_S_gt in H1.
apply lt_n_Sm_le in H0.
apply le_S_gt in H0.
apply (gt_asym _ _ H0);auto.
apply IHf2;auto.
destruct H0.
rewrite H1 in *.
destruct H.
apply IHf1;auto.
clear H1.
specialize (uses_lteq_mxUsed _ _ H).
intro.
apply le_S_gt in H1.
apply lt_n_Sm_le in H0.
apply (le_not_gt _ _ H0);auto.
Qed.

Lemma exists_unused : forall f:propForm, exists x:propVar, ~uses f x.
Proof.
intros.
exists (S (mxUsed f)).
apply suc_mxUsed_unused.
Qed.

Lemma unused_no_rewrite : forall f f':propForm, forall x:propVar, (~uses f x) -> f[x:=f']=f.
Proof.
intros.
induction f;simpl in *.
auto.
auto.
assert (beq_nat x p=false).
apply beq_nat_false_iff.
assumption.
rewrite H0.
auto.
assert (~uses f1 x /\ ~uses f2 x).
split;intro;apply H;auto.
destruct H0.
specialize (IHf1 H0).
specialize (IHf2 H1).
rewrite IHf1.
rewrite IHf2.
auto.
assert (~uses f1 x /\ ~uses f2 x).
split;intro;apply H;auto.
destruct H0.
specialize (IHf1 H0).
specialize (IHf2 H1).
rewrite IHf1.
rewrite IHf2.
auto.
Qed.

