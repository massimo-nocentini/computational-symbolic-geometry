
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
