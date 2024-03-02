; COMMAND-LINE: --sort-inference
; EXPECT: unsat
; DISABLE-TESTER: alf
;; Datatypes are not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-datatypes ((Data 1)) ((par (T) ((data)))))
(declare-fun p2 () (Data Bool))
(declare-fun p3 () (Data Bool))
(assert (not (= p2 p3)))
(check-sat)
