(* 2.(a) *)
let drei_a = define_type "drei_a = eins | zwei | drei";;

(* 2.(b) *)
let drei_th = prove (`?x. x < 3`, EXISTS_TAC `0` THEN ARITH_TAC);;
let drei_bij = new_type_definition "drei_b" ("mk_drei", "dest_drei") drei_th;;

let DREI_CLAUSES = prove
  (`((!x. P (dest_drei x)) <=> (!x. (x < 3) ==> P x)) /\
    ((?x. P (dest_drei x)) <=> (?x. (x < 3)  /\ P x))`,
  MESON_TAC[drei_bij]);;

let DREI_CLAUSES' = prove
  (`((!x:drei_b. P x) <=> (!x. (x < 3) ==> P x)) /\
    ((?x:drei_b. P x) <=> (?x. (x < 3)  /\ P x))`,
  MESON_TAC[drei_bij]);;


(* 2.(c) *)

g `?x:drei_a y z. ~(x = y) /\ ~(y = z) /\ ~(z = x)`;;
e (EXISTS_TAC `eins`);;
e (EXISTS_TAC `zwei`);;
e (EXISTS_TAC `drei`);;
e (REWRITE_TAC [prove_constructors_distinct (snd drei_a)]);;
(* done *)


g `?x:drei_b y z. ~(x = y) /\ ~(y = z) /\ ~(z = x)`;;
e (EXISTS_TAC `mk_drei 0`);;
e (EXISTS_TAC `mk_drei 1`);;
e (EXISTS_TAC `mk_drei 2`);;
e (REPEAT CONJ_TAC);;
(* TODO *)


g `?x y z. ~(dest_drei x = dest_drei y) /\ ~(dest_drei y = dest_drei z) /\ ~(dest_drei z = dest_drei x)`;;
e (REWRITE_TAC [(CONJUNCT2 DREI_CLAUSES)]);;
e (EXISTS_TAC `0`);;
e (REWRITE_TAC [ARITH_RULE `0 < 3`]);;
e (EXISTS_TAC `1`);;
e (REWRITE_TAC [ARITH_RULE `1 < 3`]);;
e (EXISTS_TAC `2`);;
e (REWRITE_TAC [ARITH_RULE `2 < 3`]);;
e ARITH_TAC;;
(* done *)

