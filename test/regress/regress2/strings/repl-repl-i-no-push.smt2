; COMMAND-LINE: --strings-exp --strings-fmf --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
(set-logic SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)

(assert (not (= (str.replace (str.replace x "B" x) x "AB") (str.replace (str.replace x "B" "AB") x "AB"))))
(check-sat)

(push 1)
(assert (not (= (str.replace (str.replace x "B" x) x "A") (str.replace (str.replace x "B" "A") x "A"))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= (str.replace (str.replace x z x) x y) (str.replace (str.replace x z y) x y))))
(check-sat)
(pop 1)

(assert (not (= (str.replace (str.replace x z x) x y) (str.replace (str.replace x z y) x y))))
(assert (<= (str.len y) (str.len z)))
(check-sat)
