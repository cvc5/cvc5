; COMMAND-LINE: --no-fresh-declarations
; EXPECT: (error "Cannot bind x to symbol of type Int, maybe the symbol has already been defined?")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(declare-fun x () Int)
(declare-fun x () Int)
(check-sat)
