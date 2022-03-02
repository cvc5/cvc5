; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --strict-parsing
; SCRUBBER: grep -o "Symbol 'div' not declared as a variable"
; EXPECT: Symbol 'div' not declared as a variable
; EXIT: 1
(set-option :incremental false)
(set-info :status sat)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(check-sat-assuming ( (and (= z 0) (>= (+ (- (div 2 x) (* 2 y)) z) 1)) ))
