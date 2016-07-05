Add LoadPath "somePath".

Require Export BES.

(*----------consistent consequences----------*)

Definition consistent_environment_rhs (E:BES)(R:propVar_relation)(x y:propVar) :=
  forall theta:environment, consistent_environment theta R -> 
    [[rhs E x]]theta -> [[rhs E y]]theta.

Definition consistent_consequence (E:BES)(R:propVar_relation) : Prop :=
forall x y:propVar, R x y -> 
  (rank E x=rank E y)
/\
  (bnd E x -> bnd E y -> consistent_environment_rhs E R x y).


Notation "'cc' E R" := (consistent_consequence E R)(at level 200).

Definition cc_max (E:BES)(x:propVar)(y:propVar):Prop :=
  exists R:propVar_relation, consistent_consequence E R /\ relates_bound R (flatten_genBES E) (flatten_genBES E) /\ R x y.

Notation "E |- x <, y" := (cc_max E x y)(at level 50).

Lemma cc_max_consistent_environment_has_cc: forall E:BES, forall theta:environment, 
consistent_environment theta (cc_max E) -> 
  forall x y:propVar, (E |- x <, y) -> 
    exists R:propVar_relation, 
      consistent_consequence E R /\ R x y /\ consistent_environment theta R.
Proof.
intros.
destruct H0 as [R H0].
destruct H0.
destruct H1.
exists R.
split;auto.
split;auto.
intro;intros.
apply (H x0);auto.
exists R.
split;auto.
Qed.


Lemma cc_max_is_cc : forall E:BES, consistent_consequence E (cc_max E).
Proof.
intros;intro;intros.
destruct H as [R H].
destruct H.
destruct H0.
destruct (H x y);auto.
split;auto.
intros;intro;intros.
specialize (cc_max_consistent_environment_has_cc E theta H6 x y).
intro.
assert (cc_max E x y).
  exists R;auto.
specialize (H8 H9).
destruct H9 as [R' H9].
destruct H9;destruct H10.
destruct (H9 x y);auto.
apply (H13 H4 H5);auto.
intro;intros.
apply (H6 x0);auto.
exists R';auto.
Qed.
