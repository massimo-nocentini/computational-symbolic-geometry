
(*demonstration of  MOVE_INVARIANT theorem *)
g (`!p p'. move p p' ==> oriented_area p = oriented_area p'`);;

e (REWRITE_TAC [FORALL_PAIR_THM; 
                    move; 
                    oriented_area] )  ;;   



e (REWRITE_TAC [FORALL_PAIR_THM] );;
e (REWRITE_TAC [move] );;
e (REWRITE_TAC [oriented_area] );;

e (CONV_TAC REAL_RING);;

(* REACHABLE invariant *)

g (`!p p'. reachable p p' ==> oriented_area p = oriented_area p'`);;
e (MATCH_MP_TAC reachable_INDUCT);;
e (MESON_TAC[MOVE_INVARIANT]);;

e (REWRITE_TAC [move]);;


g `~(reachable ((&0,&0),(&3,&0),(&0,&3)) ((&0,&0),(&0,&3),(&3,&0)))`;;

(* the following two lines can be used interchangeably with (A) *)
e  STRIP_TAC;;

e (FIRST_ASSUM(MP_TAC o MATCH_MP REACHABLE_INVARIANT));;

(* 
 It is sufficient REWRITE_TAC since we do not need any information
 from the context.
 *)
e (REWRITE_TAC[oriented_area]);;

e REAL_ARITH_TAC;;

let _ = GSYM CONTRAPOS_THM;;
let _ = ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] REACHABLE_INVARIANT;;

(* (A) The following is another way to prove the same theorem *)
e (MATCH_MP_TAC(ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] REACHABLE_INVARIANT));;


g (`!init invariant transition P.
        (!s. init s ==> invariant s) /\
        (!s s'. invariant s /\ transition s s' ==> invariant s') /\
        (!s. invariant s ==> P s)
        ==> !s s':A. init s /\ RTC transition s s' ==> P s'`);;

e ( REPEAT GEN_TAC);;
EQ_SYM_EQ;;
ISPECL [`transition:A->A->bool`; `\s s':A. invariant s ==> invariant s'`] RTC_INDUCT;;

e ( MP_TAC(ISPECL [`transition:A->A->bool`; `\s s':A. invariant s ==> invariant s'`] RTC_INDUCT));;
    
e (MESON_TAC[]);;






g (`!s s'. init s /\ RTC trans s s' ==> mutex s'`);;

e (MATCH_MP_TAC INDUCTIVE_INVARIANT);;
EXISTS
HINT_EXISTS_TAC
e (EXISTS_TAC `indinv`);;

e (REWRITE_TAC[init; trans; indinv; mutex; FORALL_PAIR_THM; PAIR_EQ]);; 

e ARITH_TAC;;




