(* The tactics that we have seen so far are:
intro.
elim.
destruct.
simpl.
apply.
split.
induction.
rewrite.
left.
right.
assert (name subgoal).
*)

(* exercises *)
Lemma NNPP : forall A : Prop, A -> ~~A.
Proof.
intro A.
intro H.
intro F.
apply F.
apply H.
Qed.

Lemma TNE : forall A : Prop, ~~~A -> ~A.
Proof.
intros A H F.
apply H.
apply NNPP.
apply F.
Qed.


Parameter D : Set.
Parameter P Q T : D -> Prop.

Theorem example_12 : (exists x, ~ P x) -> ~forall x, P x.
intros.
intro H1.
destruct H as [y H].
 (* this replaces the assumption
       "exists x : D, ~ P x"
    by a fresh variable y :D and a hypothesis H : ~ P y
    also try
       "elim H" and then "intros" and compare
  *)
apply H.
apply H1.
  (* This unifies the "P x" of "H : forall x : D, P x" with the goal "P y"
     and finds the instantiation of y for x in the hypothesis
   *)
Qed.

Theorem pred_015 : ~(forall x : D, P x \/ (Q x -> T x)) -> ~forall x : D, T x.
Proof.
intros H N.
apply H.
intro x.
right.
intro S.
apply N.
Qed.

Theorem pred_023 : ((exists x, P x) -> (forall x, Q x)) -> forall y, P(y) -> Q(y).
Proof.
intros H1 H2 H3.
apply H1.
exists H2.
apply H3.
Qed.

Theorem pred_008 : ~(forall x, P x)  -> ~ forall x, P x /\ Q x.
Proof.
intros H N.
apply H.
intro x.
apply N.
Qed.

(* Note how a binary relation on D is declared in Coq *)
Variable R : D -> D -> Prop.

Theorem pred_031 : (forall x, P x /\ Q x) -> forall x, P x \/ exists y, R x y.
Proof.
intros H x.
left.
apply H.
Qed.

Theorem pred_036 : (exists x, forall y, ~R x y) -> ~forall x, R x x.
Proof.
intros H N.
elim H.
intro S1.
intro S2.
apply (S2 S1).
apply N.
Qed.

Theorem example_14 : forall x y, R y y /\ x = y -> R y x.
intros.
destruct H as [H1 H2].
rewrite H2.
 (* This replaces x by y in the goal
    Also try
      "rewrite <- H2"
    and see what happens
    Also try
      "rewrite <- H2 in H1"
    and see what happens
  *)
assumption.
Qed.

Variable W : D -> D -> D -> Prop.
Theorem example_17 : forall x y, W x x y /\ x = y -> W x y y.
Proof.
intros x y H.
destruct H as [H1 H2].
rewrite <- H2.
rewrite <- H2 in H1.
apply H1.
Qed.

Theorem pred_059 : (forall x:D, forall y, x = y) -> (exists x, P x) -> forall x, P x.
Proof.
intros H1 H2 x.
elim H2.
intro x'.
rewrite (H1 x' x).
intro Q.
assumption.
Qed.

Variable c d e :D.
Theorem pred_058 : (forall x:D, forall y, x = y) /\ P d -> P e.
Proof.
intro H.
destruct H as [H1 H2].
rewrite (H1 e d).
apply H2.
Qed.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
Fixpoint plus (m n : nat) {struct m} : nat :=
  match m with
  | O => n
  | S p => S (plus p n)
  end.
Lemma plus1 : forall n, plus O n = n.
Proof.
induction n.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma plus_succ : forall m n, S (plus m n) = plus m (S n).
Proof.
induction m.
simpl.
reflexivity.
simpl.
intro n.
rewrite (IHm n).
reflexivity.
Qed.

(* State and prove associativity, commutativity *)

(*Lemma plus_0r: forall n, plus O n = n.
induction n.
simpl.
reflexivity.

Lemma plus_comm: forall n m, plus n m = plus m n.
Proof.
induction n.
intro n.
rewrite plus1.
simpl.
Qed.*)

(* State and prove the drinker's paradox *)
Require Import Classical.
(* The new available tactic is "classical." *)

Theorem drinker: forall Person : Set, forall Drink : Person -> Prop,
  (exists p : Person, True) ->
  exists p : Person, Drink p -> forall x, Drink x.
intros Person Drink p1.
elim (classic (forall x, Drink x)).
intro x.
elim p1.
intros p3 _.
exists p3.
intro.
apply x.

intro H.
apply NNPP.
intro N.
apply H.
intro z0.
assert (exists x : Person, ~ Drink x).
elim H.



(* Define multiplication over the naturals and prove distributivity *)
