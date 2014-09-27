g `!x y. x + y = 1 ==> x * y = 0`;;

e (fix [`m:num`; `n:num`]);;

DISCH_THEN;;

(* 
 the following does fail since we do check the antecendent 
 of the implication of the given theorem
 *)
e (assume "*" `x + y = 1`);;

e (assume "*" `m + n = 1`);;

let th = ASSUME
 `(fib3 0 = 1) /\
  (fib3 1 = 1) /\
  (!n. fib3 (n) = fib3(n-1) + fib3(n - 2))`;;

CONJUNCT1 th;;

let toward_false = CONJ (CONJUNCT1 th) (SPEC `0` (CONJUNCT2 (CONJUNCT2 th)));;

mk_eq (concl toward_false, `F`);;

EQ_MP (ARITH_RULE (mk_eq (concl toward_false, `F`))) toward_false;;


g `fusc 0 = 0 /\
   fusc 1 = 1 /\
   fusc (2 * n) = fusc(n) /\
   fusc (2 * n + 1) = fusc(n) + fusc(n + 1)`;;

e (REWRITE_TAC[fusc_def]) ;;

e COND_CASES_TAC;; 

e (ASM_REWRITE_TAC[]) ;;

e (MP_TAC(INST [`0`,`n:num`] fusc_def));;

e ARITH_TAC;;

e (SIMP_TAC [(INST [`0`, `n:num`] fusc_def)]);;


g `!n k. n < k ==> (binom(n,k) = 0)`;;

e  INDUCT_TAC ;;

e  INDUCT_TAC ;;

e (REWRITE_TAC[binom]);;

e (REWRITE_TAC[ARITH]);;

e (REWRITE_TAC[LT_SUC]);;

e (REWRITE_TAC[LT]);;

e (REWRITE_TAC[binom; ARITH; LT_SUC; LT]);;

e ( ASM_SIMP_TAC[ARITH_RULE `n < k ==> n < SUC(k)`; ARITH]);;


g (`!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)`);;

e INDUCT_TAC ;;

e (REWRITE_TAC[FACT; ADD_CLAUSES; MULT_CLAUSES; BINOM_REFL]);;

e (INDUCT_TAC THEN REWRITE_TAC[FACT; ADD_CLAUSES; MULT_CLAUSES; BINOM_REFL]);;

e INDUCT_TAC;;

e (INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT; MULT_CLAUSES; binom]);;

e (FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`));;

e (POP_ASSUM MP_TAC);; 

e (REWRITE_TAC[ADD_CLAUSES; FACT; binom] THEN CONV_TAC NUM_RING);;


(* end *)








