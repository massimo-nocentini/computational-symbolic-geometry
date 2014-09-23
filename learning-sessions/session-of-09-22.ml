
num_WF;;

g (concl num_WF);;

e STRIP_TAC;;

e STRIP_TAC;;

SUBGOAL_THEN;;

e (SUBGOAL_THEN `(!n m. m < n ==> P m)` ASSUME_TAC);;

LT

e INDUCT_TAC;;

e (ASM_MESON_TAC [LT]);;

e (ASM_MESON_TAC [LT]);;

e (ASM_MESON_TAC []);;

(* Irrationality of 2 *)
g `!p q. p * p = 2 * q * q ==> q = 0`;;

num_WF;;

(* We'll prove it by wellfounded induction on `p`: *)
e (MATCH_MP_TAC num_WF);;

e (REWRITE_TAC [RIGHT_IMP_FORALL_THM]);;

e (REPEAT STRIP_TAC);;

AP_TERM;;

e (FIRST_ASSUM (MP_TAC o AP_TERM `EVEN`));;

(* 
 Toward a goal such that establishes the even-ness of `p`.
 Here it is very interesting because Harrison in the tutorial 
 wrotes: 'We've got the fact that `p` is even' when it cames to
 the goal `EVEN p ==> q = 0` saying that about `p` while it is
 an antecedent of implication.
 *)
e (REWRITE_TAC [EVEN_MULT; ARITH]);;

EVEN_EXISTS;;

e (REWRITE_TAC [EVEN_EXISTS]);;

e (DISCH_THEN (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC));;

e (FIRST_X_ASSUM (MP_TAC o SPECL [`q:num`; `m:num`]));;

e(ASM_REWRITE_TAC[ARITH_RULE
    `q < 2 * m ==> q * q = 2 * m * m ==> m = 0 <=>
    (2 * m) * 2 * m = 2 * q * q ==> 2 * m <= q`]);;

e(ASM_MESON_TAC[LE_MULT2; MULT_EQ_0; ARITH_RULE `2 * x <= x <=> x = 0`]);;

WF;;

WF_IND;;
