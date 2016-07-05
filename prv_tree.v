Add LoadPath "somePath".

Require Export rel_cc.

(*----------prv_tree----------*)

Inductive statement := stmt : propVar_relation -> propForm -> propForm -> statement.

Notation "G |- f --> g" := (stmt G f g)(at level 50).

Inductive prv_tree (E:BES) : statement -> Prop :=
| AS1 (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (andp a (andp b c)) (andp (andp a b) c)))
| AS2 (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (andp (andp a b) c) (andp a (andp b c))))
| AS3 (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (orp a (orp b c)) (orp (orp a b) c)))
| AS4 (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (orp (orp a b) c) (orp a (orp b c))))

| COM1 (a b:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (andp a b) (andp b a)))
| COM2 (a b:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (orp a b) (orp b a)))

| DS1 (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (orp a (andp b c)) (andp (orp a b) (orp a c))))
| DS2 (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (andp (orp a b) (orp a c)) (orp a (andp b c))))
| DS3 (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (andp a (orp b c)) (orp (andp a b) (andp a c))))
| DS4 (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (orp (andp a b) (andp a c)) (andp a (orp b c))))

| AB1 (a b:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (orp a (andp a b)) a))
| AB2 (a b:propForm)(G:propVar_relation):
  (prv_tree E (stmt G a (orp a (andp a b))))

| ID1 (a:propForm)(G:propVar_relation):
  (prv_tree E (stmt G a (andp a a)))
| ID2 (a:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (orp a a) a))

| SUP (a b:propForm)(G:propVar_relation):
  (prv_tree E (stmt G a (orp a b)))
| INF (a b:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (andp a b) a))

| TOP (a:propForm)(G:propVar_relation):
  (prv_tree E (stmt G a (andp a top)))
| BOT (a:propForm)(G:propVar_relation):
  (prv_tree E (stmt G (orp a bot) a))

| CTX (a b c:propForm)(x:propVar)(G:propVar_relation):
  (prv_tree E (stmt G a b) -> prv_tree E (stmt G (replace c x a) (replace c x b)))
| TRA (a b c:propForm)(G:propVar_relation):
  (prv_tree E (stmt G a b) -> prv_tree E (stmt G b c) -> prv_tree E (stmt G a c))
| REF (a:propForm)(G:propVar_relation):
  (prv_tree E (stmt G a a))

| CC (x y:propVar)(G:propVar_relation):
  (((bnd (bes E) x) /\ (bnd (bes E) y) /\ (rank E x=rank E y)) -> 
    (prv_tree E (stmt (rel_union G (pair_relation x y)) (rhs E x)(rhs E y))) -> 
      (prv_tree E (stmt G (var x) (var y))))
| CNT (x y:propVar)(G:propVar_relation):
  ((G x y) -> (prv_tree E (stmt G (var x) (var y))))
.

