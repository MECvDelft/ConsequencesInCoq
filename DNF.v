Add LoadPath "somePath".

Require Export propForm_cons.

(*----------DNF----------*)

Definition singleton_propForm (f:propForm):Prop :=
match f with
| top => True
| bot => True
| var x => True
| _ => False
end.

Fixpoint conj_propForm (f:propForm):Prop :=
match f with
| a /\p b => conj_propForm a /\ conj_propForm b
| _ => singleton_propForm f
end.

Definition conj_ind : forall P:propForm -> Prop,
  P top ->
  P bot ->
  (forall x:propVar, P (var x)) ->
  (forall f g:propForm, conj_propForm f -> conj_propForm g -> P f -> P g ->
    P (f /\p g)) ->
  (forall f:propForm, conj_propForm f -> P f).
Proof.
intros;induction f;simpl in *;auto.
inversion H3.
destruct H3;auto.
Qed.

Lemma env_intersect_conj : forall f:propForm, conj_propForm f -> 
  forall theta1 theta2:environment, [[f]]theta1 -> [[f]]theta2 -> [[f]]environment_intersect theta1 theta2.
Proof.
intros.
induction H using conj_ind;simpl in *;auto.
unfold environment_intersect.
apply andb_true_iff.
split;auto.
destruct H0.
destruct H1.
split.
apply IHconj_propForm1;auto.
apply IHconj_propForm2;auto.
Qed.

Fixpoint DNF_propForm (f:propForm):Prop := 
match f with
| f1 \/p f2 => (DNF_propForm f1 /\ DNF_propForm f2)
| _ => conj_propForm f
end.

Definition DNF_ind : forall P:propForm -> Prop,
  P top ->
  P bot ->
  (forall x:propVar, P (var x)) ->
  (forall f g:propForm, conj_propForm f -> conj_propForm g -> P f -> P g -> P (f /\p g)) ->
  (forall f g:propForm, DNF_propForm f -> DNF_propForm g -> P f -> P g -> P (f \/p g)) ->
  (forall f:propForm, DNF_propForm f -> P f).
Proof.
intros.
induction f;simpl in *;auto.
destruct H4;apply H3;auto.
destruct H4;apply H2;auto.
apply IHf1.
destruct f1;unfold DNF_propForm;auto.
inversion H4.
destruct f2;unfold DNF_propForm;auto.
inversion H5.
Qed.

Fixpoint distribute (f:propForm) : propForm -> propForm :=
fix distribute1 (g:propForm) : propForm :=
match f with
| f1 \/p f2 => distribute f1 g \/p distribute f2 g
| _ => match g with
       | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
       | _ => f /\p g
       end
end.

Lemma distribute_f_top : forall f:propForm, forall theta:environment, [[f]]theta <-> [[distribute f top]]theta.
Proof.
intros.
induction f;simpl in *.
split;auto.
split;intro;inversion H;auto.
split;intro;auto;apply H;auto.
split;intro.
destruct H.
left;apply IHf1;auto.
right;apply IHf2;auto.
destruct H.
left;apply IHf1;auto.
right;apply IHf2;auto.
split;intro.
split;auto.
apply H.
Qed.

Lemma distribute_top_f : forall f:propForm, forall theta:environment, [[f]]theta <-> [[distribute top f]]theta.
Proof.
intros.
induction f;simpl in *.
split;auto.
split;intro;inversion H;auto.
split;intro;auto;apply H;auto.
split;intro.
destruct H.
left;apply IHf1;auto.
right;apply IHf2;auto.
destruct H.
left;apply IHf1;auto.
right;apply IHf2;auto.
split;intro.
split;auto.
apply H.
Qed.

Lemma distribute_bot_f : forall f:propForm, forall theta:environment, [[distribute bot f]]theta <-> False.
Proof.
intros.
induction f;simpl in *.
split;intro;inversion H;auto.
split;intro;inversion H;auto.
split;intro;inversion H;auto.
split;intro.
destruct H.
apply IHf1;auto.
apply IHf2;auto.
inversion H.
split;intro;inversion H;auto.
Qed.

Lemma distribute_f_bot : forall f:propForm, forall theta:environment, [[distribute f bot]]theta <-> False.
Proof.
intros.
induction f;simpl in *.
split;intro;inversion H;auto.
split;intro;inversion H;auto.
split;intro;inversion H;auto.
split;intro.
destruct H.
apply IHf1;auto.
apply IHf2;auto.
inversion H.
split;intro;inversion H;auto.
Qed.

Lemma distribute_f_var : forall f:propForm, forall x:propVar, forall theta:environment, [[distribute f (var x)]]theta <-> [[f /\p var x]]theta.
Proof.
intros.
induction f;split;intro.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
destruct H.
split.
left;apply IHf1;assumption.
apply IHf1;assumption.
split.
right;apply IHf2;assumption.
apply IHf2;assumption.
destruct H.
simpl.
destruct H.
left;apply IHf1;split;auto.
right;apply IHf2;split;auto.
destruct H.
destruct H.
split;auto.
split;auto.
destruct H.
destruct H.
split;auto.
split;auto.
Qed.

Lemma distribute_var_f : forall f:propForm, forall x:propVar, forall theta:environment, 
  [[distribute (var x) f]]theta <-> [[var x /\p f]]theta.
Proof.
intros.
induction f;split;intro.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
destruct H.
split.
apply IHf1.
assumption.
left;apply IHf1.
simpl;assumption.
split.
apply IHf2.
assumption.
right;apply IHf2.
simpl;assumption.
destruct H.
destruct H0.
left.
apply IHf1.
split;auto.
right;apply IHf2.
split;auto.
destruct H.
destruct H0.
split;auto.
split;auto.
destruct H.
destruct H0.
simpl.
split;auto.
Qed.

Lemma distribute_DNF : forall f g:propForm, DNF_propForm f -> DNF_propForm g -> 
  DNF_propForm (distribute f g).
Proof.
intros.
induction f;simpl in *;auto.
induction g;simpl in *;auto.
destruct H0.
split;auto.
induction g;simpl in *;auto.
destruct H0.
split;auto.
induction g;simpl in *;auto.
destruct H0.
split;auto.
destruct H.
specialize (IHf1 H).
specialize (IHf2 H1).
induction g;simpl in *;auto.
destruct H.
assert (DNF_propForm f1).
destruct f1;simpl in *;auto.
inversion H.
assert (DNF_propForm f2).
destruct f2;simpl in *;auto.
inversion H1.
specialize (IHf1 H2).
specialize (IHf2 H3).
induction g;simpl in *;auto.
destruct H0.
split;auto.
apply IHg1.
assumption.
destruct f1;destruct IHf1;simpl in *;auto.
inversion H.
destruct f2;destruct IHf2;simpl in *;auto.
inversion H1.
apply IHg2.
assumption.
destruct f1;destruct IHf1;simpl in *;auto.
inversion H.
destruct f2;destruct IHf2;simpl in *;auto.
inversion H1.
Qed.

Lemma distribute_DNF_left : forall f g:propForm, 
  DNF_propForm f -> DNF_propForm g -> propForm_cons (distribute f g) f.
Proof.
intros.
induction H using DNF_ind.
intro;intros;simpl;auto.
intro;intros;simpl.
destruct (distribute_bot_f g theta);auto.
intro;intros;simpl.
apply (distribute_var_f g x theta);auto.

induction H0 using DNF_ind;intro;intros;simpl;auto.
destruct (distribute_f_top (f /\p g0) theta).
simpl in H3;auto.
exfalso;destruct (distribute_f_bot (f /\p g0) theta);auto.
destruct (distribute_f_var (f /\p g0) x theta).
apply H2;auto.
simpl in H3.
apply H3.
destruct H0.
apply IHDNF_propForm1.
intro.
intro.
apply IHDNF_propForm.
destruct f.
left;assumption.
left;assumption.
left;assumption.
inversion H.
left;assumption.
intro.
intro.
apply IHDNF_propForm0.
destruct g0.
left;assumption.
left;assumption.
left;assumption.
inversion H1.
left;assumption.
assumption.
apply IHDNF_propForm2.
intro.
intro.
apply IHDNF_propForm.
destruct f.
right;assumption.
right;assumption.
right;assumption.
inversion H.
right;assumption.
intro.
intro.
apply IHDNF_propForm0.
destruct g0.
right;assumption.
right;assumption.
right;assumption.
inversion H1.
right;assumption.
assumption.

induction H0 using DNF_ind;intro;intros;simpl;auto.
destruct (distribute_f_top (f \/p g0) theta).
simpl in H3;auto.
exfalso;destruct (distribute_f_bot (f \/p g0) theta);auto.
destruct (distribute_f_var (f \/p g0) x theta).
apply H2;auto.

destruct H3.
left;auto.
right;auto.
destruct H0.
left;auto.
right;auto.
Qed.

Lemma distribute_DNF_right : forall f g:propForm, 
  DNF_propForm g -> DNF_propForm f -> propForm_cons (distribute f g) g.
Proof.
intros.
induction H using DNF_ind.
intro;intros;simpl;auto.
intro;intros;simpl.
destruct (distribute_f_bot f theta);auto.
intro;intros;simpl.
apply (distribute_f_var f x theta);auto.

induction H0 using DNF_ind.
intro;intro.
destruct (distribute_top_f (f0 /\p g)theta);auto.
intro;intro.
exfalso.
destruct (distribute_bot_f (f0 /\p g)theta);auto.
intro;intros.
destruct (distribute_var_f (f0 /\p g)x theta);auto.
apply H2;auto.
simpl.
intro;intro.
apply H3.
intro;intro.
simpl in H0.
destruct H0.
apply IHDNF_propForm1.
intro.
intro.
apply IHDNF_propForm.
destruct f0.
left;assumption.
left;assumption.
left;assumption.
inversion H.
left;assumption.
intro.
intro.
apply IHDNF_propForm0.
destruct g.
left;assumption.
left;assumption.
left;assumption.
inversion H1.
left;assumption.
assumption.
apply IHDNF_propForm2.
intro.
intro.
apply IHDNF_propForm.
destruct f0.
right;assumption.
right;assumption.
right;assumption.
inversion H.
right;assumption.
intro.
intro.
apply IHDNF_propForm0.
destruct g.
right;assumption.
right;assumption.
right;assumption.
inversion H1.
right;assumption.
assumption.

induction H0 using DNF_ind;intro;intros;simpl;auto.
destruct (distribute_top_f (f0 \/p g) theta).
simpl in H3;auto.
exfalso;destruct (distribute_bot_f (f0 \/p g) theta);auto.
destruct (distribute_var_f (f0 \/p g) x theta).
apply H2;auto.

destruct H3.
left;auto.
right;auto.
destruct H0.
apply IHDNF_propForm3.
intro;intros.
apply IHDNF_propForm1.
destruct f0;simpl.
left;assumption.
left;assumption.
left;assumption.
left;assumption.
left;assumption.
intro;intros.
apply IHDNF_propForm2.
destruct g;simpl.
left;assumption.
left;assumption.
left;assumption.
left;assumption.
left;assumption.
assumption.

apply IHDNF_propForm4.
intro;intros.
apply IHDNF_propForm1.
destruct f0;simpl.
right;assumption.
right;assumption.
right;assumption.
right;assumption.
right;assumption.
intro;intros.
apply IHDNF_propForm2.
destruct g;simpl.
right;assumption.
right;assumption.
right;assumption.
right;assumption.
right;assumption.
assumption.
Qed.

Lemma distribute_sound : forall f g:propForm, forall theta:environment,
[[f]]theta -> [[g]]theta -> [[distribute f g]]theta.
Proof.
intro.
induction f;intro;simpl in *;auto.
intros.
apply (distribute_top_f g);auto.
intros.
inversion H.
intros.
apply (distribute_var_f g p theta);split;auto.
destruct g;intros;auto.
simpl in *;destruct H.
left;apply (distribute_f_top f1);auto.
right;apply (distribute_f_top f2);auto.
inversion H0.
simpl in *;destruct H.
left;apply (distribute_f_var f1 p);split;auto.
right;apply (distribute_f_var f2 p);split;auto.
destruct H.
left.
apply IHf1.
assumption.
assumption.
right.
apply IHf2.
assumption.
assumption.
destruct H.
left.
apply IHf1.
assumption.
assumption.
right.
apply IHf2.
assumption.
assumption.
induction g;intros;simpl in *;auto.
destruct H.
destruct H0.
left.
apply IHg1;auto.
right.
apply IHg2;auto.
Qed.

Fixpoint toDNF (f:propForm):propForm :=
match f with
| f1 \/p f2 => toDNF f1 \/p toDNF f2
| f1 /\p f2 => distribute (toDNF f1) (toDNF f2)
| _ => f
end.

Lemma DNF_toDNF : forall f:propForm, DNF_propForm (toDNF f).
Proof.
intros.
induction f;simpl in *;auto.
apply distribute_DNF;auto.
Qed.

Lemma toDNF_cons : forall f:propForm, forall theta:environment,
  [[toDNF f]]theta -> [[f]]theta.
Proof.
intros.
induction f;simpl in *;auto.
destruct H;auto.
split.
apply IHf1;auto.
apply (distribute_DNF_left (toDNF f1) (toDNF f2)).
apply DNF_toDNF.
apply DNF_toDNF.
assumption.
apply IHf2;auto.
apply (distribute_DNF_right (toDNF f1) (toDNF f2)).
apply DNF_toDNF.
apply DNF_toDNF.
assumption.
Qed.

Lemma cons_toDNF : forall f:propForm, forall theta:environment, [[f]]theta -> [[toDNF f]]theta.
Proof.
intros.
induction f;simpl;auto.
destruct H;auto.
destruct H.
apply distribute_sound;auto.
Qed.

