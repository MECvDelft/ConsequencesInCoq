Add LoadPath "somePath".

Require Export sound_and_complete.
Require Import Omega.

Fixpoint b_propForm_solution(f:propForm)(theta:environment):bool:=
match f with
| top => true
| bot => false
| var x => theta x
| f1 /\p f2 => b_propForm_solution f1 theta && b_propForm_solution f2 theta
| f1 \/p f2 => b_propForm_solution f1 theta || b_propForm_solution f2 theta
end.

Notation "[[ f ]]_b theta" := (b_propForm_solution f theta) (at level 50).

Fixpoint unfold_block (bl:list booleanEquation)(theta:environment):environment:=
match bl with
| nil => theta
| bEqn x fx::bl' => redefineEnvironment (unfold_block bl' theta) x ([[fx]]_b theta)
end.

Definition redefine_bound (bl:list booleanEquation)(result_unbound result_bound:environment):environment:=
fun (x:propVar) => if bnd_block_dec bl x then result_bound x else result_unbound x.

Definition w_d_block(bl:list booleanEquation) := forall x:propVar, bnd_block bl x <->bnd_cnt_block bl x=1.

Fixpoint sol_iterator (H:environment -> environment)(theta_b:environment)(i:nat) :=
match i with
| 0 => H theta_b
| S(k) => H (sol_iterator H theta_b k)
end.

Fixpoint genBES_solution (e:list block)(theta:environment){struct e} : environment :=
let F (e'':list block)(B'':block)(theta'' theta_b'':environment) : environment :=
  unfold_block B'' (genBES_solution e'' (redefine_bound B'' theta'' theta_b''))
in
match e with
| nil => theta
| cons bl e' => if (blockType bl)
                then genBES_solution e' (redefine_bound bl theta (sol_iterator (F e' bl theta) full_environment (length bl)))
                else genBES_solution e' (redefine_bound bl theta (sol_iterator (F e' bl theta) empty_environment (length bl)))
end.

Definition BES_solution (E:BES)(Theta:environment) : environment :=
  genBES_solution (the_genBES (bes E)) Theta.

Lemma neq_no_rewrite : forall theta:environment, forall x y:propVar, x<>y -> 
  forall b:bool, theta x <-> (redefineEnvironment theta y b) x.
Proof.
unfold redefineEnvironment.
split;intro.
assert (beq_nat y x=false).
  apply beq_nat_false_iff;auto.
rewrite H1;auto.
assert (beq_nat y x=false).
  apply beq_nat_false_iff;auto.
rewrite H1 in H0;auto.
Qed.

Lemma unbound_no_change_block_function : forall bl:list booleanEquation, forall x:propVar, 
  ~bnd_block bl x -> forall theta:environment, theta x <-> unfold_block bl theta x.
Proof.
induction bl;simpl in *;auto.
split;intro;auto.

destruct a as [y fy].
split;intro.
assert (~bnd_block bl x).
  intro;apply H;auto.
apply neq_no_rewrite.
intro.
apply H;auto.
apply-> IHbl;auto.
apply neq_no_rewrite in H0.
apply IHbl;auto.
intro;apply H;auto.
Qed.

Lemma rank_bound_split: forall E:BES, forall R:propVar_relation, consistent_consequence E R ->
  forall x y:propVar, R x y -> ((bnd E x /\ bnd E y) \/ (~bnd E x /\ ~bnd E y)).
Proof.
intros.
destruct (H x y);auto.
destruct (eq_rank _ _ _ H1);auto.
destruct (bnd_dec E x);auto.
destruct (bnd_dec E y);auto.
Qed.

Lemma b_propForm_solution_correct : forall f:propForm, forall theta:environment, 
  (propForm_solution f theta) <-> [[f]]_b theta.
Proof.
induction f;split;intro;simpl in *;auto.
inversion H.
apply orb_true_iff.
destruct H.
left;apply IHf1;auto.
right;apply IHf2;auto.
apply orb_true_iff in H.
destruct H.
left;apply IHf1;auto.
right;apply IHf2;auto.
apply andb_true_iff.
destruct H.
split.
apply IHf1;auto.
apply IHf2;auto.
apply andb_true_iff in H.
destruct H.
split.
apply IHf1;auto.
apply IHf2;auto.
Qed.

Lemma alt_tl : forall l:list block, forall h:block, 
  alternating_list_block (h::l) -> alternating_list_block l.
Proof.
induction l;simpl in *;auto.
intros.
destruct H.
destruct l;simpl in *;auto.
Qed.

Lemma bnd_cnt_block_gt : forall bl:list booleanEquation, forall x :propVar, bnd_block bl x <-> bnd_cnt_block bl x > 0.
Proof.
induction bl.
split;intro.
inversion H.
simpl in H.
inversion H.

destruct a as [z fz].
simpl in *.
split;intro.
destruct H.
rewrite H.
rewrite<- beq_nat_refl.
omega.
destruct (IHbl x).
specialize (H0 H).
destruct (beq_nat x z);omega.

destruct (eq_nat_decide x z).
rewrite (eq_nat_eq _ _ e);auto.
right.
apply IHbl.
assert (beq_nat x z=false).
  apply beq_nat_false_iff.
  intro.
  apply n;apply eq_nat_is_eq;auto.
rewrite H0 in H.
assumption.
Qed.

Lemma bnd_cnt_gt : forall bl:list block, forall x :propVar, bnd bl x <-> bnd_cnt bl x > 0.
Proof.
induction bl.
split;intro.
inversion H.
simpl in H.
inversion H.

destruct a as [b].
simpl in *.
split;intro.
destruct H.
assert (bnd_cnt_block b x>0).
  apply bnd_cnt_block_gt;auto.
omega.
destruct (IHbl x).
specialize (H0 H);omega.
destruct (gt_dec (bnd_cnt bl x) 0).
right;apply IHbl;auto.
assert (bnd_cnt_block b x>0).
  omega.
left;apply bnd_cnt_block_gt;auto.
Qed.

Lemma w_d_w_d_block : forall bl:list booleanEquation, 
  forall b:bool, forall exists_bl:exists beqn:booleanEquation, In beqn bl, 
    (w_d ((makeBlock bl b exists_bl)::nil)) <-> w_d_block bl.
Proof.
destruct bl.
split;intros;destruct exists_bl;inversion i.

split;intros.
intro.
destruct b as [z fz].
destruct (H x).
simpl in *.
destruct (eq_nat_decide x z).
rewrite (eq_nat_eq _ _ e) in *.
rewrite<- beq_nat_refl in *.
assert (~bnd_block bl z).
  intro.
  assert (S (bnd_cnt_block bl z) > 1).
    apply gt_n_S.
    apply bnd_cnt_block_gt;auto.
  assert (S (bnd_cnt_block bl z) + 0 = 1).
    apply H0;auto.
  omega.
split;intro;auto.
assert (S (bnd_cnt_block bl z) + 0 = 1);auto.
omega.
assert (beq_nat x z=false).
  apply beq_nat_false_iff.
  intro.
  apply n;apply eq_nat_is_eq;auto.
split;intro.
destruct H3.
exfalso.
apply n;apply eq_nat_is_eq;auto.
rewrite H2 in *.
assert (bnd_cnt_block bl x + 0 = 1);auto.
omega.
rewrite H2 in *.
right.
apply bnd_cnt_block_gt;omega.

destruct b as [z fz].
intro;intros.
destruct (H x).
simpl in *.
destruct (eq_nat_decide x z).
rewrite (eq_nat_eq _ _ e) in *;auto.
rewrite<- beq_nat_refl in *.
split;intro;auto.
destruct H2;try contradiction.
assert (S (bnd_cnt_block bl z)=1);auto.
omega.
assert (beq_nat x z=false).
  apply beq_nat_false_iff;intro.
  apply n;apply eq_nat_is_eq;auto.
rewrite H2 in *.
split;intro.
destruct H3;try contradiction.
assert (bnd_cnt_block bl x=1);auto.
omega.
left.
apply H1.
omega.
Qed.

Lemma w_d_block_tl : forall bl:list booleanEquation, forall heqn:booleanEquation, 
  w_d_block (heqn::bl) -> w_d_block bl.
Proof.
destruct heqn as [z fz].
intros;intro.
destruct (H x).
simpl in *.
split;intro.
assert (beq_nat x z=false).
  apply beq_nat_false_iff.
  intro.
  rewrite H3 in *.
  rewrite<- beq_nat_refl in *.
  assert (S(bnd_cnt_block bl z)=1);auto.
  assert (S(bnd_cnt_block bl z)>1).
    apply gt_n_S.
    apply bnd_cnt_block_gt;auto.
  omega.
rewrite H3 in *;auto.
assert (beq_nat x z=false).
  apply beq_nat_false_iff.
  intro.
  rewrite H3 in *.
  rewrite<- beq_nat_refl in *.
  assert (S(bnd_cnt_block bl z)=1);auto.
  assert (S(bnd_cnt_block bl z)>1).
    apply gt_n_S.
    rewrite H2;auto.
  omega.
rewrite H3 in *.
destruct (H1 H2);auto.
exfalso.
apply beq_nat_false_iff in H3;auto.
Qed.

Lemma rhs_unfold_block : forall bl:block, 
  forall alt_bl: alternating_list_block (bl::nil), 
    forall w_d_bl: w_d (make_genBES (bl::nil) alt_bl), 
      forall x:propVar, bnd_block bl x -> 
        forall theta:environment, 
          (unfold_block bl theta) x
        <->
          propForm_solution (rhs (makeBES (make_genBES (bl::nil) alt_bl) w_d_bl) x) theta.
Proof.
destruct bl as [bl type_bl exists_bl].
induction bl;simpl in *;auto.
intros;contradiction.

destruct a as [z fz].
intros.
simpl in *.
destruct (bnd_block_dec (bEqn z fz :: bl) x);try contradiction.
destruct (eq_nat_decide x z).
rewrite (eq_nat_eq _ _ e) in *;auto.
unfold redefineEnvironment.
rewrite<- beq_nat_refl.
split;intro;apply b_propForm_solution_correct;auto.
unfold redefineEnvironment.
assert (beq_nat z x=false).
  apply beq_nat_false_iff.
  intro.
  apply n;apply eq_nat_is_eq;auto.
repeat rewrite H0.
destruct H.
exfalso.
apply n;apply eq_nat_is_eq;auto.
assert (exists beqn : booleanEquation, In beqn bl).
  clear - b n.
  destruct bl;simpl in *.
  exfalso.
  destruct b;auto.
  apply n;apply eq_nat_is_eq;auto.
  exists b0;auto.
assert (type_bl=type_bl /\ True);auto.
assert (w_d ((makeBlock bl type_bl H1)::nil)).
  apply w_d_w_d_block.
  apply (w_d_block_tl bl (bEqn z fz)).
  apply (w_d_w_d_block (bEqn z fz::bl) type_bl exists_bl);auto.
assert (is_true true);auto.
destruct (IHbl H1 H4 H3 x H theta).
destruct (bnd_block_dec bl x);try contradiction.
split;intro;auto.
Qed.

Lemma useful_unfold_block : forall bl:block, 
  forall alt_bl: alternating_list_block (bl::nil), 
    forall w_d_bl: w_d (make_genBES (bl::nil) alt_bl), 
      forall R:propVar_relation, 
        consistent_consequence (makeBES (make_genBES (bl::nil) alt_bl) w_d_bl) R -> 
forall theta:environment, consistent_environment theta R -> 
  consistent_environment (unfold_block bl theta) R.
Proof.
destruct bl as [bl type_bl exists_bl].
induction bl;simpl;auto.

destruct a as [z fz].
intros.
intro;intros.
destruct (H x y);auto.
destruct (rank_bound_split _ _ H _ _ H1).
clear H4.
simpl in H5.
destruct H5.
destruct H4;try contradiction.
destruct H5;try contradiction.

destruct (rhs_unfold_block (makeBlock (bEqn z fz::bl) type_bl exists_bl) alt_bl w_d_bl y H5 theta);simpl in *.
apply H7.
destruct (bnd_block_dec (bEqn z fz :: bl) y);try contradiction.
destruct (H x y);auto.
simpl in H9.
assert ((x = z \/ bnd_block bl x) \/ False);auto.
assert ((y = z \/ bnd_block bl y) \/ False);auto.
specialize (H9 H10 H11 theta H0).
clear H10 H11.
simpl in H9.
destruct (bnd_block_dec (bEqn z fz :: bl) x);try contradiction.
destruct (bnd_block_dec (bEqn z fz :: bl) y);try contradiction.
apply H9.
clear H6 H7 H8 H9 b b0 b1.
destruct (rhs_unfold_block (makeBlock (bEqn z fz::bl) type_bl exists_bl) alt_bl w_d_bl x H4 theta);simpl in *.
specialize (H6 H2).
destruct (bnd_block_dec (bEqn z fz :: bl) x);try contradiction;auto.

destruct H5.
simpl in *.
unfold redefineEnvironment in *.
assert (beq_nat z x=false).
  apply beq_nat_false_iff;intro.
  apply H5;simpl;auto.
assert (beq_nat z y=false).
  apply beq_nat_false_iff;intro.
  apply H6;simpl;auto.
rewrite H8.
rewrite H7 in H2.
assert (~bnd_block bl x).
  intro;apply H5;simpl;auto.
assert (~bnd_block bl y).
  intro;apply H6;simpl;auto.
apply (unbound_no_change_block_function _ _ H10 theta).
apply (unbound_no_change_block_function _ _ H9) in H2.
apply (H0 x);auto.
Qed.

Lemma useful_sol_iterator : forall f:environment -> environment, forall R:propVar_relation, 
(forall theta:environment, consistent_environment theta R -> (consistent_environment (f theta) R)) ->
  forall n:nat, forall theta:environment, consistent_environment theta R -> 
    consistent_environment (sol_iterator f theta n) R.
Proof.
induction n;simpl in *;auto.
Qed.

Lemma w_d_tl : forall bl:list block, forall bh:block, 
  w_d (bh::bl) -> w_d bl.
Proof.
intros;intro.
destruct bh as [bh type_bh exists_bh].
destruct (H x).
simpl in *.
split;intro.
assert (bnd_cnt_block bh x+bnd_cnt bl x=1);auto.
assert (bnd_cnt bl x>0).
  apply bnd_cnt_gt;auto.
  omega.
apply bnd_cnt_gt.
omega.
Qed.

Lemma w_d_hd : forall bl:list block, forall bh:block, 
  w_d (bh::bl) -> w_d_block bh.
Proof.
intros;intro.
destruct bh as [bh type_bh exists_bh].
destruct (H x).
simpl in *.
split;intro.
assert (bnd_cnt_block bh x+bnd_cnt bl x=1);auto.
assert (bnd_cnt_block bh x>0).
  apply bnd_cnt_block_gt;auto.
  omega.
apply bnd_cnt_block_gt.
omega.
Qed.

Lemma rank_tl : forall bl:block, forall e:list block, forall w_d_bl_e:w_d (bl::e), 
  forall x y:propVar, rank (bl::e) x=rank (bl::e) y -> rank e x = rank e y.
Proof.
destruct bl as [bl type_bl exists_bl].
induction bl;simpl in *.
destruct exists_bl;contradiction.

simpl in *.
intros.
unfold rank in H.
destruct a as [z fz].
simpl in *.
destruct (bnd_block_dec (bEqn z fz :: bl) y).
destruct (bnd_block_dec (bEqn z fz :: bl) x).
clear H.
simpl in *.
assert (~bnd e x).
  clear IHbl.
  intro.
  destruct (w_d_bl_e x).
  simpl in *.
  assert ((x = z \/ bnd_block bl x) \/ bnd e x);auto.
  specialize (H0 H2).
  assert (bnd_cnt e x>0).
    apply bnd_cnt_gt;auto.
  assert (bnd_cnt_block (bEqn z fz::bl) x>0).
    apply bnd_cnt_block_gt;auto.
  simpl in H4.
  destruct (beq_nat x z);omega.
assert (~bnd e y).
  clear IHbl H.
  intro.
  destruct (w_d_bl_e y).
  simpl in *.
  assert ((y = z \/ bnd_block bl y) \/ bnd e y);auto.
  specialize (H0 H2).
  assert (bnd_cnt e y>0).
    apply bnd_cnt_gt;auto.
  assert (bnd_cnt_block (bEqn z fz::bl) y>0).
    apply bnd_cnt_block_gt;auto.
  simpl in H4.
  destruct (beq_nat y z);omega.
clear - H H0.
induction e;simpl in *.
unfold rank.
destruct (bnd_dec nil x);try contradiction.
destruct (bnd_dec nil y);try contradiction;auto.

destruct a as [bl type_bl exists_bl].
simpl in *.
unfold rank.
destruct (bnd_dec
      ({| theBlock := bl; blockType := type_bl; non_empty := exists_bl |}
       :: e) x);try contradiction.
destruct (bnd_dec
      ({| theBlock := bl; blockType := type_bl; non_empty := exists_bl |}
       :: e) y);try contradiction;auto.
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) x).
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) y).
destruct type_bl;exfalso;clear - H;omega.
simpl in *.
exfalso.
apply n0.
left;auto.
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) y).
destruct type_bl;exfalso;clear - H;omega.
simpl in *.
exfalso.
apply n1.
left;auto.
destruct (bnd_block_dec (bEqn z fz :: bl) x).
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) x).
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) y).
destruct type_bl;exfalso;clear - H;omega.
destruct type_bl;exfalso;clear - H;omega.
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) y).
destruct type_bl;exfalso;clear - H;omega.
simpl in *.
exfalso.
apply n0.
left;auto.
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) x).
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) y).
simpl in *.
assert (bnd e x).
  destruct b;auto;contradiction.
assert (bnd e y).
  destruct b0;auto;contradiction.
clear - w_d_bl_e H H0 H1.
induction e.
inversion H0.
simpl in *.
destruct (bnd_block_dec a x).
destruct (bnd_block_dec a y).
assert (~bnd e x).
  intro.
  clear - w_d_bl_e b H2.
  destruct (w_d_bl_e x).
  simpl in *.
  assert ((if beq_nat x z then S (bnd_cnt_block bl x) else bnd_cnt_block bl x) +
    (bnd_cnt_block a x + bnd_cnt e x) = 1).
    apply H;auto.
  assert (bnd_cnt_block a x>0).
    apply bnd_cnt_block_gt;auto.
  assert (bnd_cnt e x>0).
    apply bnd_cnt_gt;auto.
  omega.
assert (~bnd e y).
  intro.
  clear - w_d_bl_e b0 H3.
  destruct (w_d_bl_e y).
  simpl in *.
  assert ((if beq_nat y z then S (bnd_cnt_block bl y) else bnd_cnt_block bl y) +
    (bnd_cnt_block a y + bnd_cnt e y) = 1).
    apply H;auto.
  assert (bnd_cnt_block a y>0).
    apply bnd_cnt_block_gt;auto.
  assert (bnd_cnt e y>0).
    apply bnd_cnt_gt;auto.
  omega.
unfold rank.
destruct (bnd_dec (a :: e) x);try contradiction.
destruct (bnd_dec (a :: e) y);try contradiction.
simpl.
destruct H0;try contradiction.
destruct H1;try contradiction.
destruct (bnd_block_dec a x);try contradiction.
destruct (bnd_block_dec a y);try contradiction.
destruct (blockType a);auto.
destruct type_bl;clear - H;exfalso;omega.
destruct (bnd_block_dec a y).
destruct type_bl;clear - H;exfalso;omega.
unfold rank.
destruct (bnd_dec (a :: e) x);try contradiction.
destruct (bnd_dec (a :: e) y);try contradiction.
simpl.
destruct (bnd_block_dec a x);try contradiction.
destruct (bnd_block_dec a y);try contradiction.
assert (bnd_block_number e x=bnd_block_number e y).
  clear - H.
  destruct type_bl;omega.
rewrite H2;auto.
simpl in *.
destruct type_bl;clear - H;exfalso;omega.
destruct (bnd_dec
          ({|
           theBlock := bEqn z fz :: bl;
           blockType := type_bl;
           non_empty := exists_bl |} :: e) y).
destruct type_bl;clear - H;exfalso;omega.
simpl in *.
assert (~bnd e x).
  intro;apply n1;auto.
assert (~bnd e y).
  intro;apply n2;auto.
clear - H0 H1.
unfold rank.
destruct (bnd_dec e x);try contradiction.
destruct (bnd_dec e y);try contradiction;auto.
Qed.

Lemma cc_tl : forall e:list block, forall bl:block, 
forall alt_bl_e: alternating_list_block (bl::e), forall w_d_bl_e: w_d (make_genBES (bl::e) alt_bl_e), 
  forall R:propVar_relation, consistent_consequence (makeBES (make_genBES (bl::e) alt_bl_e) w_d_bl_e) R -> 
    forall alt_e:alternating_list_block e, forall w_d_e:w_d (make_genBES e alt_e), 
      consistent_consequence (makeBES (make_genBES e alt_e) w_d_e) R.
Proof.
induction e;simpl in *.
intros;intro;intros.
split.
unfold rank.
simpl.
destruct (bnd_dec nil x);try contradiction.
destruct (bnd_dec nil y);try contradiction;auto.
simpl;intros.
inversion H1.

intros;simpl in *.
intro;intros;simpl in *.
split.
destruct (H x y H0).
simpl in *.

apply (rank_tl bl (a::e));auto.

intros.
intro;intros.
destruct (H x y H0).
simpl in *.
assert (bnd_block bl x \/ bnd_block a x \/ bnd e x);auto.
assert (bnd_block bl y \/ bnd_block a y \/ bnd e y);auto.
specialize (H6 H7 H8 _ H3).
destruct (bnd_block_dec a y);try contradiction.
assert (bnd_block a x).
  clear - H5 b w_d_bl_e w_d_e.
  specialize (rank_tl bl (a::e) w_d_bl_e _ _ H5).
  intro.
  destruct (eq_rank (a::e) x y H).
  simpl in *.
  assert (bnd_block a y \/ bnd e y);auto.
  specialize (H1 H2).
  unfold rank in H.
  destruct (bnd_dec (a :: e) x);try contradiction.
  destruct (bnd_dec (a :: e) y);try contradiction.
  unfold bnd_block_number in H.
  simpl in H.
  destruct (bnd_block_dec a y);try contradiction.
  destruct (bnd_block_dec a x);auto.
  destruct (blockType a);exfalso;clear - H;omega.
simpl in H6.
assert (~bnd_block bl x).
  clear - H9 w_d_bl_e.
  intro.
  destruct (w_d_bl_e x).
  assert (bnd_cnt (bl::a::e)x=1).
    apply H0;simpl;auto.
  simpl in H2.
  assert (bnd_cnt_block bl x>0).
    apply bnd_cnt_block_gt;auto.
  assert (bnd_cnt_block a x>0).
    apply bnd_cnt_block_gt;auto.
  omega.
assert (~bnd_block bl y).
  clear - b w_d_bl_e.
  intro.
  destruct (w_d_bl_e y).
  assert (bnd_cnt (bl::a::e)y=1).
    apply H0;simpl;auto.
  simpl in H2.
  assert (bnd_cnt_block bl y>0).
    apply bnd_cnt_block_gt;auto.
  assert (bnd_cnt_block a y>0).
    apply bnd_cnt_block_gt;auto.
  omega.
assert (~bnd e x).
  clear - H9 w_d_bl_e.
  intro.
  destruct (w_d_bl_e x).
  assert (bnd_cnt (bl::a::e)x=1).
    apply H0;simpl;auto.
  simpl in H2.
  assert (bnd_cnt e x>0).
    apply bnd_cnt_gt;auto.
  assert (bnd_cnt_block a x>0).
    apply bnd_cnt_block_gt;auto.
  omega.
assert (~bnd e y).
  clear - b w_d_bl_e.
  intro.
  destruct (w_d_bl_e y).
  assert (bnd_cnt (bl::a::e)y=1).
    apply H0;simpl;auto.
  simpl in H2.
  assert (bnd_cnt e y>0).
    apply bnd_cnt_gt;auto.
  assert (bnd_cnt_block a y>0).
    apply bnd_cnt_block_gt;auto.
  omega.
destruct (bnd_block_dec bl y);try contradiction.
destruct (bnd_block_dec bl x);try contradiction.
destruct (bnd_block_dec a x);try contradiction.
destruct (bnd_block_dec a y);try contradiction.
apply H6;auto.
destruct H2;try contradiction.
simpl in *.
destruct (bnd_block_dec a y);try contradiction.
assert (~bnd_block bl y).
  clear - H2 w_d_bl_e.
  intro.
  destruct (w_d_bl_e y).
  assert (bnd_cnt_block bl y + (bnd_cnt_block a y + bnd_cnt e y) = 1).
    apply H0;simpl;auto.
  assert (bnd_cnt_block bl y>0).
    apply bnd_cnt_block_gt;auto.
  assert (bnd_cnt e y>0).
    apply bnd_cnt_gt;auto.
  omega.
destruct (bnd_block_dec bl y);try contradiction.
apply H6.
assert (~bnd_block bl x).
  clear - H1 w_d_bl_e.
  intro.
  destruct (w_d_bl_e x).
  assert (bnd_cnt_block bl x + (bnd_cnt_block a x + bnd_cnt e x) = 1).
    apply H0;simpl;auto.
  assert (bnd_cnt_block bl x>0).
    apply bnd_cnt_block_gt;auto.
  destruct H1.
  assert (bnd_cnt_block a x>0).
    apply bnd_cnt_block_gt;auto.
  omega.
  assert (bnd_cnt e x>0).
    apply bnd_cnt_gt;auto.
  omega.
destruct (bnd_block_dec bl x);try contradiction.
assumption.
Qed.

Lemma cc_hd : forall e:list block, forall bl:block, 
forall alt_bl_e: alternating_list_block (bl::e), forall w_d_bl_e: w_d (make_genBES (bl::e) alt_bl_e), 
  forall R:propVar_relation, consistent_consequence (makeBES (make_genBES (bl::e) alt_bl_e) w_d_bl_e) R -> 
    forall alt_bl:alternating_list_block (bl::nil), forall w_d_bl:w_d (make_genBES (bl::nil) alt_bl), 
      consistent_consequence (makeBES (make_genBES (bl::nil) alt_bl) w_d_bl) R.
Proof.
intros;intro;intros.
destruct (H x y H0).

simpl in *;auto.
split.
clear - w_d_bl_e H1.
unfold rank in *.
simpl in *.
destruct (bnd_dec (bl :: nil) x).
destruct (bnd_dec (bl :: nil) y).
simpl in *.
destruct (bnd_dec (bl::e) x).
destruct (bnd_dec (bl::e) y).
destruct (blockType bl).
destruct (bnd_block_dec bl x).
destruct (bnd_block_dec bl y);auto.
inversion H1.
exfalso.
destruct b;auto.
destruct (bnd_block_dec bl x);try contradiction.
destruct (bnd_block_dec bl y);try contradiction;auto.
inversion H1.
destruct (bnd_block_dec bl y);try contradiction.
inversion H1.
auto.
destruct (blockType bl);inversion H1.
exfalso.
destruct b;auto;apply n;simpl;auto.
exfalso.
destruct (bnd_dec (bl::e) x).
destruct (bnd_dec (bl::e) y).
destruct (blockType bl).
simpl in *.
destruct b;auto.
destruct (bnd_block_dec bl x);auto.
destruct (bnd_block_dec bl y).
apply n;auto.
inversion H1.
destruct (bnd_block_dec bl x);auto.
destruct (bnd_block_dec bl y).
apply n;simpl;auto.
inversion H1.
destruct (bnd_block_dec bl y).
inversion H1.
destruct b;auto.
destruct (blockType bl);inversion H1.
destruct (bnd_block_dec bl y).
destruct (bnd_dec (bl::e) y).
destruct (blockType bl);inversion H1.
simpl in *.
apply n;auto.
destruct (bnd_dec (bl::e) y).
destruct (blockType bl);inversion H1.
simpl in *.
destruct b;auto.
destruct (bnd_dec (bl::e) x).
destruct (blockType bl).
destruct (bnd_dec (bl::nil) y);auto.
exfalso.
destruct (bnd_dec (bl::e) y).
destruct (bnd_block_dec bl x);simpl in *;try contradiction.
destruct b0;auto.
destruct b0;auto.
destruct (bnd_block_dec bl y);try contradiction;inversion H1.
destruct b0;auto.
apply n0;simpl;auto.
destruct (bnd_block_dec bl x).
destruct (bnd_dec (bl::e) y).
destruct (bnd_block_dec bl y).
destruct (bnd_dec (bl::nil) y);auto.
exfalso.
simpl in *.
apply n;auto.
destruct (bnd_dec (bl::nil) y);auto.
exfalso.
destruct b2;auto.
destruct (bnd_dec (bl::nil) y);auto.
destruct (bnd_block_dec bl y);auto.
exfalso.
destruct b1;auto.
destruct (bnd_dec (bl::nil) y);auto.
exfalso.
destruct (bnd_dec (bl::e) y).
destruct (bnd_block_dec bl y);auto.
inversion H1.
destruct b0;auto.
destruct b0;auto.
apply n1;left;auto.
destruct (bnd_dec (bl::e) y);auto.
destruct (bnd_block_dec bl y);auto.
destruct (bnd_dec (bl::nil) y);auto.
destruct (blockType bl);inversion H1.
destruct (bnd_dec (bl::nil) y);auto.
exfalso.
destruct b;auto.
apply n1;auto.
left;auto.

intros.
destruct H3;try contradiction.
destruct H4;try contradiction.
assert (bnd_block bl x \/ bnd e x);auto.
assert (bnd_block bl y \/ bnd e y);auto.
intro;intros.
specialize (H2 H5 H6 _ H7).
unfold rhs in *.
simpl in *.
destruct (bnd_block_dec bl x);try contradiction.
destruct (bnd_block_dec bl y);try contradiction.
apply H2;auto.
Qed.

Lemma redef_bnd_consistent : forall bl:block, 
forall alt_bl:alternating_list_block (bl::nil), 
  forall w_d_bl: w_d (make_genBES (bl::nil) alt_bl), forall R:propVar_relation, 
    consistent_consequence (makeBES (make_genBES (bl::nil) alt_bl) w_d_bl) R -> 
forall theta_bound theta_unbound:environment, consistent_environment theta_bound R -> 
  consistent_environment theta_unbound R -> 
    consistent_environment (redefine_bound bl theta_bound theta_unbound) R.
Proof.
destruct bl as  [bl type_bl exists_bl].
destruct bl;simpl in *;auto.
intros;intro;intros.
unfold redefine_bound in *.
destruct (bnd_block_dec nil x);try contradiction.
destruct (bnd_block_dec nil y);try contradiction.
apply (H0 x);auto.

intros.
specialize (rank_bound_split _ _ H).
simpl in *;intros.
destruct b as [z fz].
intro;intros.
destruct (H2 _ _ H3).
destruct H5.
destruct H5;try contradiction.
destruct H6;try contradiction.
unfold redefine_bound in *.
destruct (bnd_block_dec (bEqn z fz::bl) x);try contradiction.
destruct (bnd_block_dec (bEqn z fz::bl) y);try contradiction.
apply (H1 x);auto.
destruct H5.
unfold redefine_bound in *.
destruct (bnd_block_dec (bEqn z fz::bl) x).
exfalso.
apply H5;destruct b;auto.
destruct (bnd_block_dec (bEqn z fz::bl) y).
exfalso.
apply H6;destruct b;auto.
apply (H0 x);auto.
Qed.

Lemma useful : forall E:BES, forall R:propVar_relation, 
  consistent_consequence E R -> 
    forall theta:environment, consistent_environment theta R -> 
      consistent_environment (BES_solution E theta) R.
Proof.
destruct E as [e w_d_e].
destruct e as [e alt_e].
induction e.
simpl in *;auto.

simpl;intros.
assert (alternating_list_block e).
  apply (alt_tl _ a);auto.
assert (w_d e).
  apply (w_d_tl e a);auto.
assert (consistent_consequence (makeBES (make_genBES e H1) H2) R).
  apply (cc_tl _ _ _ _ _ H).
assert (consistent_environment (genBES_solution e theta) R).
  apply (IHe H1 H2 R H3 theta);auto.
assert (alternating_list_block (a::nil)).
  simpl;auto.
assert (w_d (make_genBES (a::nil) H5)).
  destruct a as [al].
  apply w_d_w_d_block.
  apply (w_d_hd _ _ w_d_e).
assert (consistent_consequence (makeBES (make_genBES (a::nil) H5) H6) R).
  apply (cc_hd e _ alt_e w_d_e);auto.
destruct a as [bl bl_type bl_exists].
simpl.
destruct bl_type.

(*nu*)
cut (consistent_environment (redefine_bound bl theta
        (sol_iterator
           (fun theta_b'' : environment =>
            unfold_block bl
              (genBES_solution e (redefine_bound bl theta theta_b'')))
           full_environment (length bl))) R).
intro.
apply (IHe H1 H2 R H3);auto.
apply (redef_bnd_consistent _ H5 H6 _ H7 _ _ H0).
apply useful_sol_iterator.
intros.
cut (consistent_environment (genBES_solution e (redefine_bound bl theta theta0)) R).
intro.
apply (useful_unfold_block _ H5 H6 _ H7 _ H9).
apply (IHe H1 H2 R H3);auto.
apply (redef_bnd_consistent _ H5 H6 _ H7);auto.
apply full_environment_consistent.

(*mu*)
cut (consistent_environment (redefine_bound bl theta
        (sol_iterator
           (fun theta_b'' : environment =>
            unfold_block bl
              (genBES_solution e (redefine_bound bl theta theta_b'')))
           empty_environment (length bl))) R).
intro.
apply (IHe H1 H2 R H3);auto.
apply (redef_bnd_consistent _ H5 H6 _ H7 _ _ H0).
apply useful_sol_iterator.
intros.
cut (consistent_environment (genBES_solution e (redefine_bound bl theta theta0)) R).
intro.
apply (useful_unfold_block _ H5 H6 _ H7 _ H9).
apply (IHe H1 H2 R H3);auto.
apply (redef_bnd_consistent _ H5 H6 _ H7);auto.
apply empty_environment_consistent.
Qed.