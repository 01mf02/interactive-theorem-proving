let disj_symm = prove
 (`(a:bool) \/ (b:bool) ==> b \/ a`,
  DISCH_TAC THEN
  (FIRST_ASSUM DISJ_CASES_TAC) THENL
  [DISJ2_TAC THEN (FIND_ASSUM ACCEPT_TAC `a:bool`);
   DISJ1_TAC THEN (FIND_ASSUM ACCEPT_TAC `b:bool`)]);;


(* Draft for lukas_ax2:
g `(A ==> B ==> C) ==> (A ==> B) ==> A ==> C`;;
e (REPEAT DISCH_TAC);;
e (SUBGOAL_THEN `B:bool` MP_TAC);;
e (SUBGOAL_THEN `A:bool` MP_TAC);;
e (ACCEPT_TAC (ASSUME `A:bool`));;
e (ACCEPT_TAC (ASSUME `A:bool ==> B:bool`));;
e (SUBGOAL_THEN `A:bool` MP_TAC);;
e (ACCEPT_TAC (ASSUME `A:bool`));;
e (ACCEPT_TAC (ASSUME `A:bool ==> B:bool ==> C:bool`));;
*)

let lukas_ax2 = prove
 (`(A ==> B ==> C) ==> (A ==> B) ==> A ==> C`,
  (REPEAT DISCH_TAC) THEN
  (SUBGOAL_THEN `B:bool` MP_TAC) THENL
  [ (SUBGOAL_THEN `A:bool` MP_TAC) THENL
    [ ACCEPT_TAC (ASSUME `A:bool`)
    ; ACCEPT_TAC (ASSUME `A:bool ==> B:bool`)
    ]
  ; (SUBGOAL_THEN `A:bool` MP_TAC) THENL
    [ ACCEPT_TAC (ASSUME `A:bool`)
    ; ACCEPT_TAC (ASSUME `A:bool ==> B:bool ==> C:bool`)
    ]
  ]
 );;


(* Draft for all_ex:
g `(!x. P x ==> Q x) ==> ((?y. Q y) ==> P a) ==> Q b ==> Q (a : A)`;;
e (REPEAT DISCH_TAC);;
e (SUBGOAL_THEN `(P : A->bool) (a : A)` MP_TAC);;
e (SUBGOAL_THEN `?y. (Q : A->bool) y` MP_TAC);;
e (EXISTS_TAC `b:A`);;
e (ACCEPT_TAC (ASSUME `(Q : A->bool) b`));;
e (ACCEPT_TAC (ASSUME `(?y. (Q : A->bool) y) ==> (P : A->bool) a`));;
e (SPEC_TAC (`a:A`, `x:A`));;
e (ACCEPT_TAC (ASSUME `!x. (P : A->bool) x ==> (Q : A->bool) x`));;
*)

let all_ex = prove
 (`(!x. P x ==> Q x) ==> ((?y. Q y) ==> P a) ==> Q b ==> Q (a : A)`,
  (REPEAT DISCH_TAC) THEN
  (SUBGOAL_THEN `(P : A->bool) (a : A)` MP_TAC) THENL
  [ SUBGOAL_THEN `?y. (Q : A->bool) y` MP_TAC THENL
    [ (EXISTS_TAC `b:A`) THEN (ACCEPT_TAC (ASSUME `(Q : A->bool) b`))
    ; (ACCEPT_TAC (ASSUME `(?y. (Q : A->bool) y) ==> (P : A->bool) a`))
    ]
  ; (SPEC_TAC (`a:A`, `x:A`)) THEN
    (ACCEPT_TAC (ASSUME `!x. (P : A->bool) x ==> (Q : A->bool) x`))
  ]
 );;
