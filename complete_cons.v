Add LoadPath "somePath".

Require Export sound.

(*----------complete cons----------*)

Lemma conj_distribute_prv_tree : forall E:BES, forall G:propVar_relation, forall f g:propForm, 
  conj_propForm f -> DNF_propForm g -> prv_tree E (stmt G (f /\p g) (distribute f g)).
Proof.
intros.
induction H0 using DNF_ind.
destruct f;simpl in *;try apply REF.
inversion H.
destruct f;simpl in *;try apply REF.
inversion H.
destruct f;simpl in *;try apply REF.
inversion H.
destruct f;simpl in *;try apply REF.
inversion H.

apply (TRA _ _ ((f /\p f0) \/p (f /\p g))).
apply DS3.
apply (TRA _ _ ((f /\p f0) \/p (distribute f (f0 \/p g)))).
destruct (exists_unused (f /\p f0)).
apply (TRA _ _ ((f /\p f0) \/p distribute f g)).
specialize (CTX E (f /\p g) (distribute f g) ((f /\p f0) \/p var x) x G IHDNF_propForm2).
simpl;intro.
assert (~uses f x).
intro.
apply H0.
left;auto.
rewrite (unused_no_rewrite _ _ _ H2) in H1.
rewrite (unused_no_rewrite _ _ _ H2) in H1.
assert (~uses f0 x).
intro.
apply H0.
right;auto.
rewrite (unused_no_rewrite _ _ _ H3) in H1.
rewrite (unused_no_rewrite _ _ _ H3) in H1.
rewrite <- (beq_nat_refl _) in H1.
assumption.
assert (prv_tree E (G |- distribute f g --> distribute f (f0 \/p g))).
clear IHDNF_propForm1 IHDNF_propForm2.
destruct f;simpl.
remember ((fix distribute1 (g0 : propForm) : propForm :=
         match g0 with
         | top => top /\p g0
         | bot => top /\p g0
         | var _ => top /\p g0
         | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
         | _ /\p _ => top /\p g0
         end) g) as gd.
remember ((fix distribute1 (g0 : propForm) : propForm :=
         match g0 with
         | top => top /\p g0
         | bot => top /\p g0
         | var _ => top /\p g0
         | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
         | _ /\p _ => top /\p g0
         end) f0) as f0d.
apply (TRA _ _ (gd \/p f0d)).
apply SUP.
apply COM2.
remember ((fix distribute1 (g0 : propForm) : propForm :=
         match g0 with
         | top => bot /\p g0
         | bot => bot /\p g0
         | var _ => bot /\p g0
         | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
         | _ /\p _ => bot /\p g0
         end) g) as gd.
remember ((fix distribute1 (g0 : propForm) : propForm :=
         match g0 with
         | top => bot /\p g0
         | bot => bot /\p g0
         | var _ => bot /\p g0
         | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
         | _ /\p _ => bot /\p g0
         end) f0) as f0d.
apply (TRA _ _ (gd \/p f0d)).
apply SUP.
apply COM2.
remember ((fix distribute1 (g0 : propForm) : propForm :=
         match g0 with
         | top => var p /\p g0
         | bot => var p /\p g0
         | var _ => var p /\p g0
         | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
         | _ /\p _ => var p /\p g0
         end) g) as gd.
remember ((fix distribute1 (g0 : propForm) : propForm :=
         match g0 with
         | top => var p /\p g0
         | bot => var p /\p g0
         | var _ => var p /\p g0
         | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
         | _ /\p _ => var p /\p g0
         end) f0) as f0d.
apply (TRA _ _ (gd \/p f0d)).
apply SUP.
apply COM2.
inversion H.
remember ((fix distribute1 (g0 : propForm) : propForm :=
         match g0 with
         | top => (f1 /\p f2) /\p g0
         | bot => (f1 /\p f2) /\p g0
         | var _ => (f1 /\p f2) /\p g0
         | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
         | _ /\p _ => (f1 /\p f2) /\p g0
         end) g) as gd.
remember ((fix distribute1 (g0 : propForm) : propForm :=
         match g0 with
         | top => (f1 /\p f2) /\p g0
         | bot => (f1 /\p f2) /\p g0
         | var _ => (f1 /\p f2) /\p g0
         | g1 \/p g2 => distribute1 g1 \/p distribute1 g2
         | _ /\p _ => (f1 /\p f2) /\p g0
         end) f0) as f0d.
apply (TRA _ _ (gd \/p f0d)).
apply SUP.
apply COM2.
specialize (CTX E (distribute f g) (distribute f (f0 \/p g)) ((f /\p f0) \/p var x) x G H1).
simpl;intro.
assert (~uses f x).
intro.
apply H0.
left;auto.
assert (~uses f0 x).
intro.
apply H0.
right;auto.
rewrite (unused_no_rewrite _ _ _ H3) in H2.
rewrite (unused_no_rewrite _ _ _ H3) in H2.
rewrite (unused_no_rewrite _ _ _ H4) in H2.
rewrite (unused_no_rewrite _ _ _ H4) in H2.
rewrite <- (beq_nat_refl _) in H2.
assumption.
apply (TRA _ _ (distribute f (f0 \/p g) \/p distribute f (f0 \/p g))).
destruct (exists_unused (distribute f (f0 \/p g))).
assert (prv_tree E (G |- f /\p f0 --> distribute f (f0 \/p g))).
apply (TRA _ _ (distribute f f0));auto.
clear - H H0_ H0_0.
destruct f;simpl;try apply SUP.
inversion H.
specialize (CTX E (f /\p f0) (distribute f (f0 \/p g)) (var x \/p distribute f (f0 \/p g)) x G H1).
simpl;intro.
rewrite (unused_no_rewrite _ _ _ H0) in H2.
rewrite (unused_no_rewrite _ _ _ H0) in H2.
rewrite <- (beq_nat_refl x) in H2.
assumption.
apply ID2.
Qed.

Lemma complete_to_bot : forall E:BES, forall G:propVar_relation, forall f:propForm,
  propForm_cons f bot -> prv_tree E (stmt G f bot).
Proof.
intros.
unfold propForm_cons in H.
specialize (propForm_eqv_bot f).
intro.
induction f;simpl in *.
exfalso.
apply (H empty_environment).
auto.
apply (REF).
specialize (H full_environment).
exfalso;apply H;auto.
unfold not in H0.
destruct H0.
specialize (H0 H).
assert (forall theta : environment, [[f1]]theta -> False).
intros.
apply (H theta).
left;assumption.
assert (forall theta : environment, [[f2]]theta -> False).
intros.
apply (H theta).
right;assumption.
specialize (IHf1 H2).
specialize (IHf2 H3).
specialize (IHf1 (propForm_eqv_bot f1)).
specialize (IHf2 (propForm_eqv_bot f2)).
apply (TRA _ _ (f1 \/p bot) _).
destruct (exists_unused f1) as [x Hn].
specialize (CTX E f2 bot (f1 \/p var x) x G IHf2).
intro.
simpl in H4.
rewrite<- (beq_nat_refl x) in *.
rewrite (unused_no_rewrite f1 f2 x Hn) in H4.
rewrite (unused_no_rewrite f1 bot x Hn) in H4.
assumption.
apply (TRA E (f1 \/p bot) (bot \/p bot) bot).
apply (TRA E _ (bot \/p f1) _).
exact (COM2 E f1 bot G).
specialize (CTX E f1 bot (bot \/p var 0) 0 G).
intros.
simpl in H4.
apply H4.
assumption.
exact (ID2 E bot G).

cut ((forall theta : environment, ~[[f1]]theta) \/ (forall theta:environment, ~[[f2]]theta)).
intros.
destruct H1.
apply (TRA _ _ (f2 /\p bot) _).
destruct (exists_unused f2) as [x Hn].
specialize (IHf1 H1).
specialize (IHf1 (propForm_eqv_bot f1)).
apply (TRA _ _ (f2 /\p f1) _).
apply COM1.
specialize (CTX E f1 bot (f2 /\p var x) x G IHf1).
intros.
simpl in H2.
rewrite<- (beq_nat_refl x) in *.
rewrite (unused_no_rewrite f2 f1 x Hn) in H2.
rewrite (unused_no_rewrite f2 bot x Hn) in H2.
assumption.
apply (TRA _ _ (bot /\p f2) _).
apply (COM1).
apply INF.
apply (TRA _ _ (f1 /\p bot) _).
destruct (exists_unused f1) as [x Hn].
assert (forall theta : environment, [[f2]]theta -> False).
intros.
apply (H1 theta).
assumption.
specialize (IHf2 H1).
specialize (IHf2 (propForm_eqv_bot f2)).
specialize (CTX E f2 bot (f1 /\p var x) x G IHf2).
intros.
simpl in H3.
rewrite<- (beq_nat_refl x) in *.
rewrite (unused_no_rewrite f1 f2 x Hn) in H3.
rewrite (unused_no_rewrite f1 bot x Hn) in H3.
assumption.
apply (TRA _ _ (bot /\p f1) _).
apply (COM1).
apply INF.

unfold propForm_eqv in H0.
simpl in H0.
destruct H0.
specialize (H0 H).
destruct (eqv_bot_dec f1).
left;assumption.
destruct (eqv_bot_dec f2).
right;assumption.
destruct H2 as [theta1 H2].
destruct H3 as [theta2 H3].
specialize (H (environment_union theta1 theta2)).
exfalso.
apply H.
apply (environment_union_distributes).
auto.
Qed.

Lemma complete_from_top : forall E:BES, forall G:propVar_relation, forall f:propForm,
  propForm_cons top f -> prv_tree E (stmt G top f).
Proof.
intros.
unfold propForm_cons in H.
destruct (propForm_eqv_top f).
induction f;simpl in *.
apply (REF).

exfalso.
apply (H empty_environment).
auto.

specialize (H empty_environment).
assert false;unfold empty_environment in H.
  apply H;auto.
inversion H2.

assert (forall theta:environment, [[f1]]theta \/ [[f2]]theta).
  intros;auto.
specialize (H0 H2).
assert (propForm_eqv f1 top \/ propForm_eqv f2 top).
  clear IHf1 IHf2.
  destruct (eqv_top_decidable f1).
  left;assumption.
  destruct (eqv_top_decidable f2).
  right;assumption.
  exfalso.
  assert True;auto.
  destruct (H empty_environment H5).
  apply H3.
  apply empty_true_eqv_top;auto.
  apply H4.
  apply empty_true_eqv_top;auto.
destruct H3.
clear IHf2.
assert (forall theta : environment, True -> [[f1]]theta).
  intros;apply H3;simpl;auto.
specialize (IHf1 H4).
assert ((forall theta : environment, [[f1]]theta) -> propForm_eqv f1 top).
  intros;auto.
specialize (IHf1 H5).
assert (propForm_eqv f1 top -> forall theta : environment, [[f1]]theta).
  intros;auto.
specialize (IHf1 H6).
clear - IHf1.
apply (TRA _ _ (f2 \/p top)).
apply (TRA _ _ (top \/p f2)).
apply SUP.
apply COM2.
apply (TRA _ _ (f2 \/p f1)).
destruct (exists_unused f2) as [x H].
specialize (CTX E top f1 (f2 \/p (var x)) x G IHf1).
intro.
simpl in H0.
rewrite<- (beq_nat_refl x) in H0.
rewrite (unused_no_rewrite f2 top x H) in H0.
rewrite (unused_no_rewrite f2 f1 x H) in H0.
assumption.
apply COM2.
clear IHf1.
assert (forall theta : environment, True -> [[f2]]theta).
  intros;apply H3;simpl;auto.
specialize (IHf2 H4).
  assert ((forall theta : environment, [[f2]]theta) -> propForm_eqv f2 top).
intros;auto.
specialize (IHf2 H5).
assert (propForm_eqv f2 top -> forall theta : environment, [[f2]]theta).
  intros;auto.
specialize (IHf2 H6).
clear - IHf2.
apply (TRA _ _ (f1 \/p top)).
apply (TRA _ _ (top \/p f1)).
apply SUP.
apply COM2.
destruct (exists_unused f1) as [x H].
specialize (CTX E top f2 (f1 \/p (var x)) x G IHf2).
intro.
simpl in H0.
rewrite<- (beq_nat_refl x) in H0.
rewrite (unused_no_rewrite f1 top x H) in H0.
rewrite (unused_no_rewrite f1 f2 x H) in H0.
assumption.

assert (forall theta : environment, True -> [[f1]]theta).
intros;apply H;auto.
assert ((forall theta : environment, [[f1]]theta) -> propForm_eqv f1 top).
intros;split;intro;intros;simpl;auto.
assert (propForm_eqv f1 top -> forall theta : environment, [[f1]]theta).
intros;auto.
specialize (IHf1 H2 H3 H4).
assert (forall theta : environment, True -> [[f2]]theta).
intros;apply H;auto.
assert ((forall theta : environment, [[f2]]theta) -> propForm_eqv f2 top).
intros;split;intro;intros;simpl;auto.
assert (propForm_eqv f2 top -> forall theta : environment, [[f2]]theta).
intros;auto.
specialize (IHf2 H5 H6 H7).
clear - IHf1 IHf2.
apply (TRA _ _ (top /\p f1)).
apply (TRA _ _ (top /\p top)).
apply ID1.
destruct (exists_unused top) as [x H].
specialize (CTX E top f1 (top /\p (var x)) x G IHf1).
intro.
simpl in H0.
rewrite<- (beq_nat_refl x) in H0.
assumption.
apply (TRA _ _ (f1 /\p top)).
apply COM1.
destruct (exists_unused f1) as [x H].
specialize (CTX E top f2 (f1 /\p (var x)) x G IHf2).
intro.
simpl in H0.
rewrite<- (beq_nat_refl x) in H0.
rewrite (unused_no_rewrite f1 top x H) in H0.
rewrite (unused_no_rewrite f1 f2 x H) in H0.
assumption.
Qed.

Lemma complete_from_var : forall E:BES, forall G:propVar_relation, forall f:propForm, forall x:propVar,
  propForm_cons (var x) f -> prv_tree E (stmt G (var x) f).
Proof.
intros.
induction f;simpl in *.

apply (TRA _ _ ((var x) /\p top)).
apply TOP.
apply (TRA _ _ (top /\p (var x))).
apply COM1.
apply INF.

exfalso.
specialize (H full_environment).
apply H.
simpl;auto.

unfold propForm_cons in H.
simpl in H.
destruct (eq_nat_decide p x).
rewrite (eq_nat_eq p x e).
apply REF.
destruct (beq_nat_false_iff x p).
assert (x<>p).
intro.
rewrite H2 in n.
specialize (eq_nat_refl p).
intro.
contradiction.
specialize (H1 H2).
specialize (H (environment_point x)).
assert false.
unfold environment_point in H.
rewrite<- (beq_nat_refl x) in H.
rewrite H1 in H.
apply H.
auto.
inversion H3.

cut (propForm_cons (var x) f1 \/ propForm_cons (var x) f2).
intro.
destruct H0.
specialize (IHf1 H0).
apply (TRA _ _ (var x \/p f2)).
apply SUP.
destruct (exists_unused f2) as [fx Hn].
specialize (CTX E (var x) f1 (var fx \/p f2) fx G IHf1).
intro.
simpl in H1.
rewrite (unused_no_rewrite f2 f1 fx Hn) in H1.
rewrite (unused_no_rewrite f2 (var x) fx Hn) in H1.
rewrite<- (beq_nat_refl fx) in H1.
assumption.
specialize (IHf2 H0).
apply (TRA _ _ (f1 \/p var x)).
apply (TRA _ _ (var x \/p f1)).
apply SUP.
apply COM2.
destruct (exists_unused f1) as [fx Hn].
specialize (CTX E (var x) f2 (f1 \/p var fx) fx G IHf2).
intro.
simpl in H1.
rewrite (unused_no_rewrite f1 f2 fx Hn) in H1.
rewrite (unused_no_rewrite f1 (var x) fx Hn) in H1.
rewrite<- (beq_nat_refl fx) in H1.
assumption.
destruct (cons_var_propForm f1 x).
left;assumption.
destruct (cons_var_propForm f2 x).
right;assumption.
destruct H0 as [theta1 H0].
destruct H1 as [theta2 H1].
destruct H0.
destruct H1.
specialize (environment_point_minimal f1 x theta1 H0 H2).
specialize (environment_point_minimal f2 x theta2 H1 H3).
intros.
assert (environment_point x x).
unfold environment_point.
rewrite<- (beq_nat_refl x).
auto.
destruct (H (environment_point x) H6);contradiction.

unfold propForm_cons in H.
assert (propForm_cons (var x) f1 /\ propForm_cons (var x) f2).
split.
intro.
intro.
apply (H theta).
auto.
intro;intro.
apply H;auto.
destruct H0.
specialize (IHf1 H0).
specialize (IHf2 H1).
apply (TRA _ _ (f1 /\p (var x))).
apply (TRA _ _ (var x /\p var x)).
apply ID1;auto.
destruct (exists_unused (var x)) as [fx Hn].
specialize (CTX E (var x) f1 (var fx /\p var x) fx G).
intros.
simpl in H2.
rewrite<- (beq_nat_refl fx) in H2.
assert (beq_nat fx x=false).
apply beq_nat_false_iff.
auto.
rewrite H3 in H2.
apply H2;auto.
destruct (exists_unused f1) as [fx Hn].
specialize (CTX E (var x) f2 (f1 /\p var fx) fx G IHf2).
intro.
simpl in H2.
rewrite<- (beq_nat_refl fx) in *.
rewrite (unused_no_rewrite f1 f2 fx Hn) in H2.
rewrite (unused_no_rewrite f1 (var x) fx Hn) in H2.
assumption.
Qed.

Lemma complete_to_var : forall E:BES, forall G:propVar_relation, forall f:propForm, forall x:propVar,
  propForm_cons f (var x) -> prv_tree E (stmt G f (var x)).
Proof.
intros.
intros.
induction f;simpl in *.
exfalso.
apply (neq_var_top x).
split.
intro;simpl;auto.
intro;apply (H theta);assumption.

unfold propForm_cons in H.
specialize (neq_var_bot x).
intro.
unfold propForm_eqv in H0.
apply (TRA _ _ ((var x) \/p bot) _).
apply (TRA _ _ (bot \/p (var x)) _).
apply SUP.
apply (COM2).
apply BOT.

unfold propForm_cons in H.
simpl in H.
destruct (eq_nat_decide p x).
rewrite (eq_nat_eq p x e).
apply REF.
destruct (beq_nat_false_iff p x).
assert (p<>x).
intro.
destruct (eq_nat_is_eq p x).
specialize (H4 H2).
contradiction.
specialize (H (environment_point p)).
assert false.
unfold environment_point in H.
rewrite<- (beq_nat_refl p) in H.
rewrite (H1 H2) in H.
apply H.
auto.
inversion H3.

unfold propForm_cons in H.
assert (propForm_cons f1 (var x) /\ propForm_cons f2 (var x)).
split.
intro.
intro.
apply (H theta).
left;auto.
intro.
intro.
apply (H theta).
right;auto.
simpl in *.
destruct H0.
specialize (IHf1 H0).
specialize (IHf2 H1).
apply (TRA _ _ (f1 \/p (var x)) _).
destruct (exists_unused f1) as [fx Hn].
specialize (CTX E f2 (var x) (f1 \/p var fx) fx G IHf2).
intro.
simpl in H2.
rewrite<- (beq_nat_refl fx) in *.
rewrite (unused_no_rewrite f1 f2 fx Hn) in H2.
rewrite (unused_no_rewrite f1 (var x) fx Hn) in H2.
assumption.
apply (TRA _ _ (var x \/p var x) _).
apply (TRA _ _ (var x \/p f1) _).
apply COM2.
specialize (CTX E f1 (var x) (var x \/p var (S x)) (S x) G IHf1).
intros.
simpl in H2.
destruct x.
rewrite<- (beq_nat_refl 0) in H2.
assumption.
rewrite<- (beq_nat_refl (S x)) in H2.
cut (beq_nat (S x) x=false).
intro.
rewrite H3 in H2.
assumption.
apply (beq_nat_false_iff).
auto.
apply ID2.

cut (propForm_cons f1 (var x) \/ propForm_cons f2 (var x)).
intro.
destruct H0.
specialize (IHf1 H0).
apply (TRA _ _ (f2 /\p var x)).
apply (TRA _ _ (f2 /\p f1)).
apply COM1.
destruct (exists_unused f2) as [fx Hn].
specialize (CTX E f1 (var x) (f2 /\p var fx) fx G IHf1).
intro.
simpl in H1.
rewrite (unused_no_rewrite f2 f1 fx Hn) in H1.
rewrite (unused_no_rewrite f2 (var x) fx Hn) in H1.
rewrite<- (beq_nat_refl fx) in H1.
assumption.
apply (TRA _ _ (var x /\p f2)).
apply COM1.
apply INF.
specialize (IHf2 H0).
apply (TRA _ _ (f1 /\p var x)).
destruct (exists_unused f1) as [fx Hn].
specialize (CTX E f2 (var x) (f1 /\p var fx) fx G IHf2).
intro.
simpl in H1.
rewrite (unused_no_rewrite f1 f2 fx Hn) in H1.
rewrite (unused_no_rewrite f1 (var x) fx Hn) in H1.
rewrite<- (beq_nat_refl fx) in H1.
assumption.
apply (TRA _ _ (var x /\p f1)).
apply COM1.
apply INF.

destruct (cons_propForm_var f1 x).
left;auto.
destruct (cons_propForm_var f2 x).
right;auto.
destruct H0 as [theta1 H0].
destruct H1 as [theta2 H1].
destruct H0.
destruct H1.
specialize (H (environment_union theta1 theta2)).
simpl in H.
exfalso.
assert (~environment_union theta1 theta2 x).
intro.
unfold environment_union in H4.
destruct (orb_prop (theta1 x) (theta2 x) H4).
rewrite H5 in H2.
apply H2.
auto.
rewrite H5 in H3.
apply H3.
auto.
assert (environment_union theta1 theta2 x).
apply H.
apply (environment_union_distributes).
auto.
contradiction.
Qed.

Lemma cSPLIT : forall E:BES, forall G:propVar_relation, forall f g1 g2:propForm, 
  prv_tree E (stmt G f g1) -> prv_tree E (stmt G f g2) -> prv_tree E (stmt G f (g1 /\p g2)).
Proof.
intros.
apply (TRA _ _ (f /\p g2)).
apply (TRA _ _ (f /\p f)).
apply ID1.
destruct (exists_unused f) as [fx Hx].
specialize (CTX _ f g2 (f /\p var fx) fx _ H0);auto;intro.
simpl in H1.
rewrite <- beq_nat_refl in H1.
rewrite unused_no_rewrite in H1;auto.
rewrite unused_no_rewrite in H1;auto.
destruct (exists_unused g2) as [gx Hx].
specialize (CTX _ f g1 (var gx /\p g2) gx _ H);intro.
simpl in H1.
rewrite <- beq_nat_refl in H1.
rewrite unused_no_rewrite in H1;auto.
rewrite unused_no_rewrite in H1;auto.
Qed.

Lemma cGROW_L : forall E:BES, forall G:propVar_relation, forall f g1 g2:propForm, 
  prv_tree E (stmt G f g1) -> prv_tree E (stmt G f (g1 \/p g2)).
Proof.
intros.
apply (TRA _ _ (f \/p g2)).
apply SUP.
destruct (exists_unused g2) as [gx Hx].
specialize (CTX _ f g1 (var gx \/p g2) gx _ H);intro.
simpl in H0.
rewrite <- beq_nat_refl in H0.
rewrite unused_no_rewrite in H0;auto.
rewrite unused_no_rewrite in H0;auto.
Qed.

Lemma cGROW_R : forall E:BES, forall G:propVar_relation, forall f g1 g2:propForm, 
  prv_tree E (stmt G f g2) -> prv_tree E (stmt G f (g1 \/p g2)).
Proof.
intros.
apply (TRA _ _ (g2 \/p g1)).
apply cGROW_L;auto.
apply COM2.
Qed.

Lemma aSPLIT : forall E:BES, forall G:propVar_relation, forall f1 f2 g:propForm, 
  prv_tree E (stmt G f1 g) -> prv_tree E (stmt G f2 g) -> prv_tree E (stmt G (f1 \/p f2) g).
Proof.
intros.
apply (TRA _ _ (f1 \/p g)).
destruct (exists_unused f1) as [fx Hx].
specialize (CTX _ f2 g (f1 \/p var fx) fx _ H0);intro.
simpl in H1.
rewrite <- beq_nat_refl in H1.
rewrite unused_no_rewrite in H1;auto.
rewrite unused_no_rewrite in H1;auto.
apply (TRA _ _ (g \/p g)).
destruct (exists_unused g) as [gx Hx].
specialize (CTX _ f1 g (var gx \/p g) gx _ H);intro.
simpl in H1.
rewrite <- beq_nat_refl in H1.
rewrite unused_no_rewrite in H1;auto.
rewrite unused_no_rewrite in H1;auto.
apply ID2.
Qed.

Lemma aGROW_L : forall E:BES, forall G:propVar_relation, forall f1 f2 g:propForm, 
  prv_tree E (stmt G f1 g) -> prv_tree E (stmt G (f1 /\p f2) g).
Proof.
intros.
apply (TRA _ _ (g /\p f2)).
destruct (exists_unused f2) as [fx Hx].
specialize (CTX _ f1 g (var fx /\p f2) fx _ H);intro.
simpl in H0.
rewrite <- beq_nat_refl in H0.
rewrite unused_no_rewrite in H0;auto.
rewrite unused_no_rewrite in H0;auto.
apply INF.
Qed.

Lemma aGROW_R : forall E:BES, forall G:propVar_relation, forall f1 f2 g:propForm, 
  prv_tree E (stmt G f2 g) -> prv_tree E (stmt G (f1 /\p f2) g).
Proof.
intros.
apply (TRA _ _ (f2 /\p f1)).
apply COM1.
apply aGROW_L;auto.
Qed.

Lemma distribute_prv_tree : forall E:BES, forall G:propVar_relation, forall g:propForm, 
  DNF_propForm g -> forall f:propForm, DNF_propForm f -> prv_tree E (stmt G (f /\p g) (distribute f g)).
Proof.
intros E G g H.
induction H using DNF_ind;intros.
apply (TRA _ _ (top /\p f)).
apply COM1.
induction H using DNF_ind;simpl in *.
  apply REF.
  apply COM1.
  apply COM1.
  apply COM1.
  apply (TRA _ _ ((top /\p f) \/p (top /\p g))).
  apply DS3.
  apply aSPLIT.
  apply cGROW_L;auto.
  apply cGROW_R;auto.

apply (TRA _ _ (bot /\p f)).
apply COM1.
induction H using DNF_ind;simpl.
  apply COM1.
  apply REF.
  apply COM1.
  apply COM1.
  apply (TRA _ _ ((bot /\p f) \/p (bot /\p g))).
  apply DS3.
  apply aSPLIT.
  apply cGROW_L;auto.
  apply cGROW_R;auto.

apply (TRA _ _ (var x /\p f)).
apply COM1.
induction H using DNF_ind;simpl.
  apply COM1.
  apply COM1.
  apply COM1.
  apply COM1.
  apply (TRA _ _ ((var x /\p f) \/p (var x /\p g))).
  apply DS3.
  apply aSPLIT.
  apply cGROW_L;auto.
  apply cGROW_R;auto.

apply (TRA _ _ ((f /\p g) /\p f0)).
apply COM1.
induction H1 using DNF_ind;simpl.
  apply COM1.
  apply COM1.
  apply COM1.
  apply COM1.
  apply (TRA _ _ (((f /\p g) /\p f0) \/p ((f /\p g) /\p g0))).
  apply DS3.
  apply aSPLIT.
  apply cGROW_L;auto.
  apply cGROW_R;auto.

apply (TRA _ _ ((f0 /\p f) \/p (f0 /\p g))).
apply DS3.
apply aSPLIT.
induction H1 using DNF_ind.
  apply cGROW_L;apply IHDNF_propForm1;simpl;auto.
  apply cGROW_L;apply IHDNF_propForm1;simpl;auto.
  apply cGROW_L;apply IHDNF_propForm1;simpl;auto.
  apply cGROW_L;apply IHDNF_propForm1;simpl;auto.
  apply (TRA _ _ ((f /\p f0) \/p (f /\p g0))).
  apply (TRA _ _ (f /\p (f0 \/p g0))).
  apply COM1.
  apply DS3.
  apply aSPLIT.
  apply cGROW_L.
  apply (TRA _ _ (f0 /\p f));auto.
  apply COM1.
  apply cGROW_R.
  apply (TRA _ _ (g0 /\p f));auto.
  apply COM1.
induction H1 using DNF_ind.
  apply cGROW_R;apply IHDNF_propForm2;simpl;auto.
  apply cGROW_R;apply IHDNF_propForm2;simpl;auto.
  apply cGROW_R;apply IHDNF_propForm2;simpl;auto.
  apply cGROW_R;apply IHDNF_propForm2;simpl;auto.
  apply (TRA _ _ ((g /\p f0) \/p (g /\p g0))).
  apply (TRA _ _ (g /\p (f0 \/p g0))).
  apply COM1.
  apply DS3.
  apply aSPLIT.
  apply cGROW_L.
  apply (TRA _ _ (f0 /\p g));auto.
  apply COM1.
  apply cGROW_R;auto.
  apply (TRA _ _ (g0 /\p g));auto.
  apply COM1.
Qed.

Lemma complete_propForm_cons_DNF : forall E:BES, forall G:propVar_relation, forall f:propForm, 
  prv_tree E (stmt G f (toDNF f)).
Proof.
intros.
induction f;simpl in *;auto.
apply REF.
apply REF.
apply REF.

apply aSPLIT;auto.
apply cGROW_L;auto.
apply cGROW_R;auto.

apply (TRA _ _ (toDNF f1 /\p toDNF f2)).
apply cSPLIT.
apply aGROW_L;auto.
apply aGROW_R;auto.
apply distribute_prv_tree;apply DNF_toDNF.
Qed.

Lemma generalized_complete_from_conj_propForm : forall E:BES, forall G:propVar_relation, forall f g:propForm, 
  conj_propForm f -> 
    propForm_cons f g -> prv_tree E (stmt G f g).
Proof.
intros.
induction g;simpl in *;auto.
(*g=top*)
apply (TRA _ _ (f /\p top)).
apply TOP.
apply (TRA _ _ (top /\p f)).
apply COM1.
apply INF.

(*g=bot*)
apply (complete_to_bot _ _ _ H0).

(*g=X*)
apply (complete_to_var _ _ _ _ H0).

(*g=a \/p b*)
destruct (conj_cons_disj_decide f g1 g2 H H0).
specialize (IHg1 H1).
apply (TRA _ _ (f \/p g2)).
apply SUP.
destruct (exists_unused g2) as [x Hx].
specialize (CTX E f g1 (var x \/p g2) x G IHg1).
intro.
simpl in H2.
rewrite (unused_no_rewrite g2 f x Hx) in H2.
rewrite (unused_no_rewrite g2 g1 x Hx) in H2.
rewrite<- (beq_nat_refl x) in H2.
assumption.

specialize (IHg2 H1).
apply (TRA _ _ (g1 \/p f)).
apply (TRA _ _ (f \/p g1)).
apply SUP.
apply COM2.
destruct (exists_unused g1) as [x Hx].
specialize (CTX E f g2 (g1 \/p var x) x G IHg2).
intro.
simpl in H2.
rewrite (unused_no_rewrite g1 f x Hx) in H2.
rewrite (unused_no_rewrite g1 g2 x Hx) in H2.
rewrite<- (beq_nat_refl x) in H2.
assumption.

(*g=a /\p b*)
assert (propForm_cons f g1).
intro;intro.
apply H0;auto.
assert (propForm_cons f g2).
intro;intro.
apply H0;auto.
specialize (IHg1 H1).
specialize (IHg2 H2).
apply (TRA _ _ (f /\p g2)).
apply (TRA _ _ (f /\p f)).
apply ID1.
destruct (exists_unused f) as [x Hx].
specialize (CTX E f g2 (f /\p (var x)) x G IHg2).
intro.
simpl in H3.
rewrite (unused_no_rewrite f f x Hx) in H3.
rewrite (unused_no_rewrite f g2 x Hx) in H3.
rewrite<- (beq_nat_refl x) in H3.
assumption.
destruct (exists_unused g2) as [x Hx].
specialize (CTX E f g1 ((var x) /\p g2) x G IHg1).
intro.
simpl in H3.
rewrite (unused_no_rewrite g2 f x Hx) in H3.
rewrite (unused_no_rewrite g2 g1 x Hx) in H3.
rewrite<- (beq_nat_refl x) in H3.
assumption.
Qed.

Lemma complete_DNF_cons_propForm : forall E:BES, forall G:propVar_relation, forall g f:propForm, DNF_propForm f -> 
  propForm_cons f g -> prv_tree E (stmt G f g).
Proof.
intros.
induction H using DNF_ind;simpl in *;auto.

apply complete_from_top;auto.

apply (TRA _ _ (g \/p bot)).
apply (TRA _ _ (bot \/p g)).
apply SUP.
apply COM2.
apply BOT.

apply complete_from_var;auto.

apply generalized_complete_from_conj_propForm;auto.
split;auto.

assert (propForm_cons f g).
intro;intro;apply H0;left;auto.
assert (propForm_cons g0 g).
intro;intro;apply H0;right;auto.
specialize (IHDNF_propForm1 H2).
specialize (IHDNF_propForm2 H3).
apply (TRA _ _ (f \/p g)).
destruct (exists_unused f) as [x Hx].
specialize (CTX E g0 g (f \/p (var x)) x G IHDNF_propForm2).
intro.
simpl in H4.
rewrite (unused_no_rewrite f g0 x Hx) in H4.
rewrite (unused_no_rewrite f g x Hx) in H4.
rewrite<- (beq_nat_refl x) in H4.
assumption.
apply (TRA _ _ (g \/p g)).
destruct (exists_unused g) as [x Hx].
specialize (CTX E f g ((var x) \/p g) x G IHDNF_propForm1).
intro.
simpl in H4.
rewrite (unused_no_rewrite g g x Hx) in H4.
rewrite (unused_no_rewrite g f x Hx) in H4.
rewrite<- (beq_nat_refl x) in H4.
assumption.
apply ID2.
Qed.

Lemma complete_cons : forall E:BES, forall G:propVar_relation, forall g f:propForm,
  propForm_cons f g -> prv_tree E (stmt G f g).
Proof.
intros.
apply (TRA _ _ (toDNF f)).
apply complete_propForm_cons_DNF.
apply (TRA _ _ (toDNF g)).
apply complete_DNF_cons_propForm.
apply DNF_toDNF.
intro;intro.
apply cons_toDNF.
apply H.
apply toDNF_cons.
assumption.
apply complete_DNF_cons_propForm.
apply DNF_toDNF.
intro;intro.
apply toDNF_cons;auto.
Qed.

