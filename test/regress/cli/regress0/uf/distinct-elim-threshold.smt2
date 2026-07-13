; COMMAND-LINE: --distinct-elim-threshold=0
; COMMAND-LINE: --distinct-elim-threshold=8
; COMMAND-LINE: --distinct-elim-threshold=2
; EXPECT: sat
; Exercises the distinct-elim preprocessing pass, which eagerly blasts distinct
; terms with at most N children (0 means no limit) into pairwise disequalities.
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(declare-fun f () Int)
(declare-fun g () Int)
(assert (distinct a b c d e f g))
(assert (or (= a b) (distinct b c d)))
(check-sat)
