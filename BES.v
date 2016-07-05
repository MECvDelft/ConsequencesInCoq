Add LoadPath "somePath".

Require Export rel_cons_dec.

(*----------BES----------*)

Definition w_d(E:list block) := forall x:propVar, bnd E x <-> bnd_cnt E x=1.

Record BES : Set := makeBES {
  bes:> genBES;
  well_defined: w_d bes
}.

Fixpoint rhs_block (l:list booleanEquation)(x:propVar):propForm :=
match l with 
| nil => var x
| cons (bEqn xc f) l' => if beq_nat xc x then f else rhs_block l' x
end.

Lemma bnd_block_dec : forall l:list booleanEquation, forall x:propVar, 
{bnd_block l x} + {~bnd_block l x}.
Proof.
induction l;simpl;intros;auto.
destruct a as [y f];simpl in *.
destruct (eq_nat_decide x y).
rewrite (eq_nat_eq _ _ e) in *;auto.
destruct (IHl x);auto.
right;intro.
destruct H;auto.
apply n;apply eq_nat_is_eq;auto.
Qed.

Fixpoint rhs (E:BES)(x:propVar) : propForm :=
let fix helper (l:list block):propForm :=
match l with
| nil => bot
| bl::l' => if (bnd_block_dec bl x) 
            then rhs_block bl x
            else helper l'
end in helper E.

Fixpoint bnd_block_number (e:list block)(x:propVar):=
match e with
| nil => 0
| bl::e' => if (bnd_block_dec bl x) then 0 else S(bnd_block_number e' x)
end.

Lemma bnd_dec : forall e:list block, forall x:propVar, 
  {bnd e x} + {~bnd e x}.
Proof.
induction e;simpl in *;auto.

intros.
destruct (bnd_block_dec a x);auto.
destruct (IHe x);auto.
right;intro.
destruct H;auto.
Qed.

Definition rank (E:list block)(x:propVar) : nat := if (bnd_dec E x) then
match E with
| nil => 0 
| bl::_ => if blockType bl 
           then S(S(bnd_block_number E x))
           else S(bnd_block_number E x)
end
else 0.

Lemma eq_rank : forall e:list block, forall x y:propVar, rank e x=rank e y -> (bnd e x <-> bnd e y).
Proof.
induction e;simpl in *.
split;intro;auto.

unfold rank.
intros x y.
split;intro.
destruct (bnd_dec (a :: e) x).
destruct (bnd_dec (a :: e) y);auto.
exfalso.
destruct a.
simpl in H.
destruct blockType;inversion H.
exfalso.
apply n;simpl;auto.
destruct (bnd_dec (a :: e) x);auto.
destruct (bnd_dec (a::e) y);try contradiction.
destruct a.
simpl in H.
destruct blockType;inversion H.
Qed.