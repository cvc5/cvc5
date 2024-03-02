; COMMAND-LINE: --strings-exp -q
; EXPECT: unsat
;; introduces STRINGS_OCCUR_INDEX Skolem
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(declare-fun a () String)
(declare-fun b () String)
(assert (= 1 (* (str.len (str.replace_all a a b)) (- (str.len (str.from_code (str.len b))) 1))))
(check-sat)
