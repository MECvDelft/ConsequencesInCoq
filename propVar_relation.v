Add LoadPath "somePath".

Require Export cons_dec.

(*----------propVar_relation----------*)

Definition propVar_relation := propVar -> propVar -> Prop.

Definition empty_relation (x y:propVar):Prop := False.

Definition id_rel := fun (x y:propVar) => x=y.

Definition rel_eqv (R1 R2:propVar_relation):=forall x y:nat, R1 x y <-> R2 x y.

Definition rel_union : propVar_relation -> propVar_relation -> propVar_relation :=
let result (R1 R2 : propVar_relation) (x z:propVar) : Prop :=
  (R1 x z) \/ (R2 x z)
in result.

Notation "R1 'U' R2" := (rel_union R1 R2)(at level 50).

Definition rel_minus (R1 R2:propVar_relation):propVar_relation :=
fun (x y:propVar) => R1 x y /\ ~R2 x y.

Definition pair_relation (x y:propVar) : propVar_relation := 
  let result(x' y':propVar) :Prop := (x=x')/\(y=y') in result.

Definition remove_var_left (R:propVar_relation)(a:nat)(x y:nat):Prop :=
if (beq_nat a x) then False else R x y.

Definition remove_var_right (R:propVar_relation)(b:nat)(x y:nat):Prop :=
if (beq_nat b y) then False else R x y.

Definition remPoint (R:propVar_relation)(a b:nat)(x y:nat):Prop :=
if ((beq_nat a x)&&(beq_nat b y)) then False else R x y.

