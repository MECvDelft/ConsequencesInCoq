Add LoadPath "somePath".

Require Export propVar_relation.

(*----------rel cons----------*)
Definition consistent_environment (theta : environment)(R:propVar_relation) := 
  forall x y: propVar, (R x y) -> (theta x -> theta y).

Lemma environment_union_consistent : forall R:propVar_relation, forall th1 th2:environment, 
consistent_environment th1 R -> consistent_environment th2 R -> consistent_environment (environment_union th1 th2) R.
Proof.
intros.
intro;intros.
apply orb_true_iff in H2.
destruct H2.
apply orb_true_iff.
left.
apply (H x);auto.
apply orb_true_iff.
right.
apply (H0 x);auto.
Qed.

Lemma full_environment_consistent : forall R:propVar_relation, consistent_environment full_environment R.
Proof.
intros;intro;intros.
unfold full_environment;auto.
Qed.

Lemma empty_environment_consistent : forall R:propVar_relation, consistent_environment empty_environment R.
Proof.
intros;intro;intros.
inversion H0.
Qed.

Definition rel_cons (R:propVar_relation)(f g:propForm):=
forall theta:environment, consistent_environment theta R -> [[f]]theta -> [[g]]theta.

Lemma consistent_environment_rel_union : forall theta:environment, forall R1 R2:propVar_relation,
consistent_environment theta (R1 U R2)
->
(consistent_environment theta R1 /\ consistent_environment theta R2).
Proof.
intros.
unfold consistent_environment in *.
split.
intros.
apply (H x y).
left;auto.
assumption.
intros.
apply (H x y).
right;auto.
assumption.
Qed.

Lemma rel_union_consistent_environment : forall theta:environment, forall R1 R2:propVar_relation,
(consistent_environment theta R1 /\ consistent_environment theta R2)
->
consistent_environment theta (R1 U R2).
Proof.
intros.
unfold consistent_environment.
destruct H.
intros.
destruct H1.
exact (H x y H1 H2).
exact (H0 x y H1 H2).
Qed.

