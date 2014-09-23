`m..n`;;
type_of it;;
g `(!)(\n. nsum(1..n) (\i. i) = (n * (n+1)) DIV 2)`;;
num_INDUCTION;;
e (MATCH_MP_TAC num_INDUCTION);;
NSUM_CLAUSES_NUMSEG;;

e (REWRITE_TAC [NSUM_CLAUSES_NUMSEG]);;
help "REWRITE_TAC";;
b();;
e (SIMP_TAC [NSUM_CLAUSES_NUMSEG]);;
e ARITH_TAC;;
let gauss_sum_of_nums_th = top_thm();;

(* another attempt, using a more dedicated tactic about NUM induction *)
help "INDUCT_TAC";;
g `(!)(\n. nsum(1..n) (\i. i) = (n * (n+1)) DIV 2)`;;
e INDUCT_TAC;;
e (REWRITE_TAC [NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

(*
OBSERVATION: John Harrison wrote, at page 54, about solving:

val it : goalstack = 1 subgoal (1 total)

  0 [`nsum (1..n) (\i. i) = (n * (n + 1)) DIV 2`]

`nsum (1..SUC n) (\i. i) = (SUC n * (SUC n + 1)) DIV 2`

Once again, almost the same proof works, except that because the
inductive hypothesis is now in our conclusion list we need to use
the ‘ASM ’ variants of the rewrite tactics, either ASM_SIMP_TAC or
ASM_REWRITE_TAC.Since we now don’t need to get the rewrite from the
context, it’s slightly more efficient to use the latter.

What I've learned from this little explanation is that every SIMP_
tactic use the context, ie information contained in the subgoal's term
itself, useful to do some rewritings, as done in the previous attempt:
val it : goalstack = 1 subgoal (1 total)

`nsum (1..0) (\i. i) = (0 * (0 + 1)) DIV 2 /\
 (!n. nsum (1..n) (\i. i) = (n * (n + 1)) DIV 2
      ==> nsum (1..SUC n) (\i. i) = (SUC n * (SUC n + 1)) DIV 2)`

# e (SIMP_TAC [NSUM_CLAUSES_NUMSEG]);;;;
val it : goalstack = 1 subgoal (1 total)

`(if 1 = 0 then 0 else 0) = (0 * (0 + 1)) DIV 2 /\
 (!n. nsum (1..n) (\i. i) = (n * (n + 1)) DIV 2
      ==> (if 1 <= SUC n
      (* from the context, it is possible to rewrite `nsum (1..n)
           (\i. i)` with `(n * (n + 1))` since they are equal*)
           then (n * (n + 1)) DIV 2 + SUC n 
           else (n * (n + 1)) DIV 2) =
          (SUC n * (SUC n + 1)) DIV 2)`

*)
e (ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

(* NUMBER SYSTEMS *)
REAL_ARITH
`!x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11:real.
x3 = abs(x2) - x1 /\
x4 = abs(x3) - x2 /\
x5 = abs(x4) - x3 /\
x6 = abs(x5) - x4 /\
x7 = abs(x6) - x5 /\
x8 = abs(x7) - x6 /\
x9 = abs(x8) - x7 /\
x10 = abs(x9) - x8 /\
x11 = abs(x10) - x9
==> x1 = x10 /\ x2 = x11`;;

`--`;;
type_of it;;
`-- &3`;;

let E_RULES, E_INDUCT, E_CASES = 
   new_inductive_definition `E 0 /\ (!) (\n. E n ==> E (n+2))`;;
g `(!)(\n. E n ==> ?m. n = 2 * m)`;;
e (MATCH_MP_TAC E_INDUCT);;
e (REPEAT STRIP_TAC);;
e (EXISTS_TAC `0` THEN ARITH_TAC);;
e (ASM_REWRITE_TAC []);;
e (EXISTS_TAC `m+1` THEN ARITH_TAC);;
let simple = top_thm();;