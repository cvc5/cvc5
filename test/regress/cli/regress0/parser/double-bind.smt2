; EXPECT: (error "Cannot bind x to symbol of type Bool, maybe the symbol has already been defined?")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(declare-const x Bool)
(declare-const x Bool)
(assert (= x x))
(check-sat)
