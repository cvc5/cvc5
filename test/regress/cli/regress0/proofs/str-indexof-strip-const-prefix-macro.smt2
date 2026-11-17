; DISABLE-TESTER: alethe
; EXPECT: unsat
; Regression for MACRO_STR_INDEXOF_STRIP_CONST_PREFIX, which is elaborated by
; stripping one character at a time.
(set-logic ALL)
(declare-const x String)
(assert (not (= (str.indexof (str.++ "abcab" x "d") "d" 0)
                (+ 5 (str.indexof (str.++ x "d") "d" 0)))))
(check-sat)
