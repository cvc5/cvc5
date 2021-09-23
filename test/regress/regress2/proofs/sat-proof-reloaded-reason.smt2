; COMMAND-LINE: --produce-proofs
; EXPECT: sat
;
; This is a benchmark exercising a dangerous behavior in SAT proofs
; where while eliminating redundant literals new clauses are added to
; the SAT solver and the reference to the reason of a literal could be
; lost.

(set-logic QF_SLIA)
(declare-const x Int)
(declare-const x2 Int)
(declare-const x22 Int)
(declare-const x1 Int)
(declare-fun s () String)
(assert (not (= "0" (str.substr s (+ 1 1 1 1) 1))))
(assert (not (= 1 (str.len (str.substr s (+ 1 1 1 1) (+ 1 1))))))
(assert (ite (str.prefixof "-" (str.substr s (+ 1 1 1 1 1) (- (str.len s) (+ 1 1 1 1 1)))) (and (> (str.len (str.substr s (+ 1 1 1) (str.len s))) 1) (ite (= (- 1) (str.to_int (str.substr (str.substr s (+ 1 1 1 1 1) (- (str.len s) 1)) 1 1))) false true)) (= 1 (str.to_int (str.substr s x22 1)))))
(assert (ite (str.prefixof "-" (str.substr s (+ 1 1) 1)) (ite (= (- 1) (str.to_int (str.substr (str.substr s (+ 1 1) (+ 1 1)) 1 (- (str.len (str.substr s 0 (+ 1 1))) 1)))) false true) (= 0 (str.to_int (str.substr s (+ 1 1) (+ 1 1))))))
(assert (<= (ite (str.prefixof "-" (str.substr s 0 1)) (str.to_int (str.substr (str.substr s (+ 1 1 1) (+ 1 1 1)) 1 (- (str.len (str.substr s (+ 1 1 1) (+ 1 1 1))) 1))) (str.to_int (str.substr s 0 x2))) 0))
(assert (ite (str.prefixof "-" (str.substr s 0 1)) (and (> (str.len (str.substr s 0 (+ 1 1))) 1) (= 0 (str.to_int (str.substr (str.substr s 0 (+ 1 1)) 1 (- (str.len (str.substr s 0 (+ 1 1))) 1))))) true))
(assert (not (= 1 (str.len (str.substr s (+ 1 1 1 1 1) (- (str.len s) (+ 1 1 1 1 1)))))))
(assert (ite (str.prefixof "-" (str.substr s (+ 1 1 1 1) (- (str.len s) (+ 1 1 1 1)))) true (= 1 (str.to_int (str.substr s (+ 1 1 1 1) 1)))))
(assert (= 1 (str.len (str.substr s (+ 1 1 1) 1))))
(assert (not (= 1 (str.len (str.substr s 1 (+ 1 1 1))))))
(assert (> (- (str.len s) 1 (+ 1 1) (+ 1 1)) 0))
(assert (= "0" (str.substr s 1 1)))
(assert (not (<= (str.to_int (str.substr s x x1)) 0)))
(assert (not (= 1 (str.len (str.substr s (+ 1 1) (- (+ 1 1 1) 1))))))
(assert (str.in_re s (re.+ (re.range "0" "9"))))
(assert (not (<= (ite (str.prefixof "-" (str.substr s (+ 1 1 1 1) 1)) (- (str.to_int (str.substr (str.substr s (+ 1 1 1 1) (+ 1 1)) 1 (- (str.len (str.substr s (+ 1 1) (+ 1 1))) 1)))) (str.to_int (str.substr s (+ 1 1 1 1) (+ 1 1)))) 1)))
(check-sat)
