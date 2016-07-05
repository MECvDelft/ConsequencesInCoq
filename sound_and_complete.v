Add LoadPath "somePath".

Require Export complete.

(*sound & complete*)

Lemma prv_system_sound_and_complete : forall E:BES, forall x y:propVar, bnd E x -> bnd E y -> 
  ((cc_max E) x y <-> prv_tree E (stmt empty_relation (var x) (var y))).
Proof.
split;intro.
apply prv_system_complete;auto.
apply prv_system_sound;auto.
Qed.

