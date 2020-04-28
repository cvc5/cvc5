; COMMAND-LINE: --lang=smt2.6
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
(set-option :incremental true)
(set-logic QF_SLIA)
(declare-const s String)
(declare-const t String)
(declare-const n Int)

(push)
(assert (not (= (str.to_code (str.from_code (str.to_code s))) (str.to_code s))))
(check-sat)
(pop)

(push)
(assert (not (= (str.from_code (str.to_code s)) s)))
(assert (<= (str.len s) 1))
(check-sat)
(pop)

(push)
(assert (not (= (str.from_code (str.to_code s)) s)))
(check-sat)
(pop)

(push)
(assert (not (= (str.from_code (str.to_code (str.from_code n))) (str.from_code n))))
(check-sat)
(pop)

(push)
(assert (not (= (str.to_code (str.from_code n)) n)))
(assert (>= n 0))
(check-sat)
(pop)

(push)
(assert (not (= (str.to_code (str.from_code n)) n)))
(assert (and (>= n 0) (< n 50)))
(check-sat)
(pop)

(push)
(assert (not (= (str.to_code (str.from_code n)) n)))
(check-sat)
(pop)

(push)
(assert (= (str.to_code s) (str.to_code t)))
(assert (= (str.len s) 1))
(assert (= (str.len t) 1))
(assert (not (= (str.from_code (str.to_code s)) (str.from_code (str.to_code t)))))
(check-sat)
(pop)

(push)
(assert (or
  (not (= (str.from_code (- 1)) ""))
  (not (= (str.from_code 100000000000000000000000) ""))
  (not (= (str.from_code 65) "A"))))
(check-sat)
(pop)
