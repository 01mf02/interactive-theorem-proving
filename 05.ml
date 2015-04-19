let f = new_recursive_definition num_RECURSION `(f 0 = 0) /\ (!n. f (SUC n) = (SUC n) + f(n))`;;


let oneiter = new_definition `oneiter f x = (if x = 0 then 0 else x + f (x-1))`;;


g `!n. f n = (n * (n+1)) DIV 2`;;
e INDUCT_TAC;;
(* base case *)
e (REWRITE_TAC [f; NUM_ADD_CONV `0 + 1`; NUM_MULT_CONV `0 * 1`; NUM_DIV_CONV `0 DIV 2`]);;
(* step case *)
e (REWRITE_TAC [f]);;
e (ASM_REWRITE_TAC[]);;
e (ARITH_TAC);;