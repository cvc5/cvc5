; COMMAND-LINE: --dump-proofs --proof-format-mode=lfsc 
; EXIT: 0
; SCRUBBER: grep -v -E '.*' 
(set-logic QF_UF)
(set-info :category "crafted")

(declare-sort U 0)
(declare-fun f1 () U)
(declare-fun f2 () U)
(declare-fun f3 () U)
(declare-fun f4 () U)
(declare-fun p (U) Bool)
(assert (not (= f1 f2)))
(assert (and (p f1) (or (= f1 f2) (distinct f3 f4 f2)) (p f3)))
(assert (= f3 f4))
(check-sat)
(exit)
