; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Mismatched parentheses in SMT-LIBv2 term"
; EXPECT: Mismatched parentheses in SMT-LIBv2 term
; EXIT: 1
(set-logic ALL)
(assert (let ((f1153) (and (< (concat (_ bv0 2) (_ bv1 2)) (concat ((_ extract 1 1) bv2_0) ((_ extract 1 1) bv2_0) ((_ extract 1 1) bv2_0) bv2_0))) (bvsle (bvmul (_ bv15594 15) bv15_1) (concat (_ bv0 13) (ite (= bv14_1 (_ bv6 14)) (_ bv1 1) (_ bv0 1)))) (and (= ((_ extract 14 bv2_0) (_ bv0 1)) (= ((_ extract 4 2) bv2_0) (_ bv0 3)))))))
