let disj_symm = prove
 (`(a:bool) \/ (b:bool) ==> b \/ a`,
  DISCH_TAC THEN
  (FIRST_ASSUM DISJ_CASES_TAC) THENL
  [DISJ2_TAC THEN (FIND_ASSUM ACCEPT_TAC `a:bool`);
   DISJ1_TAC THEN (FIND_ASSUM ACCEPT_TAC `b:bool`)]);;


g `(A ==> B ==> C) ==> (A ==> B) ==> A ==> C`;;
e (DISCH_THEN (LABEL_TAC "abc"));;
e (DISCH_THEN (LABEL_TAC "ab"));;
e (DISCH_THEN (LABEL_TAC "a"));;
e (SUBGOAL_THEN `B:bool` MP_TAC);;
e (ASM_SIMP_TAC []);;
e (SUBGOAL_THEN `A:bool` MP_TAC);;
e (ASM_SIMP_TAC []);;
e (SUBGOAL_THEN `A:bool` MP_TAC);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;


g `(!x. P x ==> Q x) ==> ((?y. Q y) ==> P a) ==> Q b ==> Q (a : A)`;;
e (DISCH_THEN (LABEL_TAC "all"));;
e (DISCH_THEN (LABEL_TAC "ex"));;
e (DISCH_THEN (LABEL_TAC "qb"));;
e (SUBGOAL_THEN `(P : A->bool) (a : A)` MP_TAC);;
e (SUBGOAL_THEN `?y. (Q : A->bool) y` MP_TAC);;
e (EXISTS_TAC `b:A`);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC []);;
e (SPEC_TAC (`a:A`, `x:A`));;
e (ASM_SIMP_TAC []);;