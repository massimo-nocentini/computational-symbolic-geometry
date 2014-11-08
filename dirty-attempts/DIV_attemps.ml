
ASM_REWRITE_TAC[]

FIRST_X_ASSUM (MP_TAC o (MP (DISCH `~(2 = 0)` (SYM (UNDISCH (SPECL [`2`;`n:num`] DIV_MULT))))))
DISCH_TAC
ASM_REWRITE_TAC []



REWRITE_TAC[DIVISION]
(* DIV_MULT is an implication *)
`!n m. n * (m DIV n) = m`
dest_comb `3+4 DIV 2`
REWR_CONV ADD_ASSOC `(a+b) + ((c + d) + e) + f + g + h`;;
REWR_CONV ADD_ASSOC `((a + b) + (c + d) + e) + f + g + h`;;
REWR_CONV ADD_ASSOC `(((a + b) + (c + d) + e) + f) + g + h`;;
(* the following causes error, since ADD_ASSOC cannot be applied *)
REWR_CONV ADD_ASSOC `((((a + b) + (c + d) + e) + f) + g) + h`;; 
            

(* Thm: Un numero non dispari e' pari.                                       *)
prove (`!n. ~(DISPARI n) ==> PARI n`,
        REWRITE_TAC [PARI; DISPARI]
        INDUCT_TAC
            STRIP_TAC THEN EXISTS_TAC `0` THEN ARITH_TAC

            (REWRITE_TAC [SUC_INJ; ADD1]) 
            STRIP_TAC
            EXISTS_TAC `(n + 1) DIV 2`
            CONV_TAC (RAND_CONV (fun tm -> let div_comb = mk_comb (`\n. n DIV 2`, tm) in BETA_CONV div_comb))
                            THENC REWR_CONV 
GSYM BETA_THM
            CONV_TAC (REWR_CONV )
SUBGOAL_THEN
            CONV_TAC ( (CONV_RULE (BINOP_CONV BETA_CONV)) o (AP_TERM `\n. n DIV 2`) o ASSUME  ) `n + 1 = 2 * (n + 1) DIV 2` 
MK_COMB (REFL )
            CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC))
            ARITH_TAC
            CONV_RULE
INST


prove (`~(c = 0) ==> (a * b) DIV c = a * (b DIV c)`,
        DISCH_TAC
        MATCH_MP_TAC DIV_UNIQ
        EXISTS_TAC `0`
        STRIP_TAC
        REWRITE_TAC [ADD_0]

CONV_TAC (RAND_CONV (REWR_CONV (GSYM MULT_ASSOC)))
REWRITE_TAC [EQ_MULT_LCANCEL]
DISJ2_TAC 
  (*FIRST_ASSUM (fun th -> STRIP_ASSUME_TAC (SYM (MATCH_MP (SPEC `b:num` (CONJUNCT1 DIVISION_SIMP)) th)))*)
  FIRST_ASSUM (fun th -> STRIP_ASSUME_TAC ((MATCH_MP (SPEC `b:num` DIVISION) th)))
  FIRST_ASSUM ((fun th -> GEN_REWRITE_TAC LAND_CONV [ th]) o check (is_eq o concl))
  (* find something like ADD_ELIM... *)
  ASM_REWRITE_TAC[]

LAND_CONV
(rand o rator) `b = r DIV c * c`

  (* very similar theorem MULT_DIV_LE *)
  
  (SPECL [`b:num`; `c:num`] DIVISION)

CONV_TAC (RAND_CONV (REWR_CONV (GSYM MULT_SYM)))
FIRST_X_ASSUM (fun th -> ASSUME_TAC (SPEC `b:num` (GSYM (MATCH_MP DIV_MULT th (*(ASSUME `~(c = 0)`)*)))))

prove ( `!a b c. ~(c = 0) ==> (a = b <=> a DIV c = b DIV c)`
    REPEAT GEN_TAC
    DISCH_TAC
    EQ_TAC
        DISCH_THEN (fun th -> REWRITE_TAC [th])


GSYM REAL_NOT_LE
ONCE_REWRITE_RULE[GSYM REAL_NOT_LE] (ASSUME `&0 < x * y`)
ASM_REWRITE_TAC []
FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (REWR_CONV (SPEC `b:num` (GSYM (MATCH_MP DIV_MULT th (*(ASSUME `~(c = 0)`)*)))))))

let trivial = prove
    (`!x y:real. &0 < x * y ==> (&0 < x <=> &0 < y)`,
     REPEAT GEN_TAC THEN MP_TAC(SPECL [`--x`; `y:real`] REAL_LE_MUL) THEN
     MP_TAC(SPECL [`x:real`; `--y`] REAL_LE_MUL) THEN REAL_ARITH_TAC);;
     type_of `(--)`

 let trivial = prove
     (`!x y:real. &0 < x * y ==> (&0 < x <=> &0 < y)`,
     MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
     MP_TAC(SPECL [`--x`; `y:real`] REAL_LE_MUL) THEN REAL_ARITH_TAC);;

