; DISABLE-TESTER: alethe
; EXPECT: unsat
; Regression for MACRO_STR_CTN_CONST_SPLIT, which is elaborated by splitting
; one character at a time.
(set-logic ALL)
(declare-const x String)
(declare-const n Int)
(assert (not (= (str.contains "abcab" (str.substr x n 1))
                (or (= "" (str.substr x n 1)) (= "a" (str.substr x n 1))
                    (= "b" (str.substr x n 1)) (= "c" (str.substr x n 1))))))
(check-sat)
