; DISABLE-TESTER: dump
; COMMAND-LINE:
; COMMAND-LINE: --strict-parsing
; COMMAND-LINE: --no-strict-parsing
; SCRUBBER: grep -o "Symbol 'is-C' not declared as a variable"
; EXPECT: Symbol 'is-C' not declared as a variable
; EXIT: 1
(set-logic QF_DT)
(declare-datatype T ((C) (D)))
(assert (is-C C))
(check-sat)
