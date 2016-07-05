Add LoadPath "somePath".

Require Export rel_cons.

(*----------genBES----------*)

Inductive booleanEquation := bEqn : propVar -> propForm -> booleanEquation.

Record block:=makeBlock{
  theBlock:> list booleanEquation;
  blockType:bool;
  non_empty: exists beqn:booleanEquation, In beqn theBlock (*blocks are non-empty*)
}.

Fixpoint alternating_list_block (theList:list block):Prop:=
match theList with
| nil => true
| b1::l => match l with
           | nil => true
           | b2::l' => (eqb (blockType b1) (negb (blockType b2))) /\ alternating_list_block l
           end
end.

Record genBES := make_genBES {
  the_genBES:> list block;
  block_alternates: alternating_list_block the_genBES
}.

Fixpoint bnd_block (E:list booleanEquation)(x:propVar):Prop:=
match E with 
| nil => False
| cons (bEqn y _) E' => x=y \/ bnd_block E' x
end.

Fixpoint bnd (E:list block)(x:propVar) : Prop :=
match E with
| nil => False
| cons bl E' => bnd_block bl x \/ bnd E' x
end.

Fixpoint bnd_cnt_block (bl:list booleanEquation)(x:propVar): nat :=
match bl with
| nil => 0
| bEqn y _ :: bl' => if (beq_nat x y) then S(bnd_cnt_block bl' x) else bnd_cnt_block bl' x
end.

Fixpoint bnd_cnt (E:list block)(x:propVar) : nat :=
match E with
| nil => 0
| cons bl E' => bnd_cnt_block bl x + bnd_cnt E' x
end.

Fixpoint occ_block (E:list booleanEquation)(x:propVar) : Prop :=
match E with
| nil => False
| cons (bEqn _ f) E' => (uses f x) \/ (occ_block E' x)
end.

Fixpoint occ (E:list block)(x:propVar):Prop:=
match E with
| nil => False
| cons bl E' => occ_block bl x \/ occ E' x
end.

