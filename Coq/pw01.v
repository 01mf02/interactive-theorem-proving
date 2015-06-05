(* comments are written with parentheses and star *)
(* an initial declaration *)
Parameter A B C : Prop.

(* example *)
Lemma example_one : A -> A.
Proof.
intro x.
assumption.
Qed.
Print example_one.

(* example *)
Lemma example_two : A -> B -> A.
Proof.
intro x.
intro y.
assumption.
Qed.
Print example_two.

(* example *)
Lemma example_three : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intro x.
intro y.
intro z.
apply x.
apply z.
apply y.
apply z.
Qed.
Print example_three.

(* The tactics that we have seen so far are:
intro.
elim.
destruct.
simpl.
apply. *)


(* exercises *)
Lemma example : (A -> B) -> (C -> A) -> C -> B.
Proof.
intro x.
intro y.
intro z.
apply x.
apply y.
apply z.
Qed.

Lemma one_a : A -> A -> A.
Proof.
intro x.
intro y.
assumption.
Qed.

(* Lemma one_b : A -> A -> A. *)
Lemma permutation : (A -> B -> C) -> B -> A -> C.
Proof.
intro x.
intro y.
intro z.
apply x.
apply z.
apply y.
Qed.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
intro x.
apply x.
intro y.
apply y.
intro z.
apply x.
intro a.
apply z.
Qed.

Lemma notfalse : ~ False.
Proof.
intro x.
assumption.
Qed.

Lemma exfalso : False -> A.
Proof.
intro x.
elim x.
Qed.

Lemma contrapositive : (A -> B) -> ~ B -> ~ A.
Proof.
intro x.
intro y.
intro z.
apply y.
apply x.
apply z.
Qed.

Lemma intro_and : A -> B -> A /\ B.
Proof.
intros a b.
refine (conj a b).
Qed.

Lemma elim_or : A \/ B -> (A -> C) -> (B -> C) -> C.
intros ab a b.
case ab.
apply a.
apply b.
Qed.

