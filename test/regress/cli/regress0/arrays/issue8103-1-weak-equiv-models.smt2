; COMMAND-LINE: --produce-models --arrays-weak-equiv
; SCRUBBER: grep -o "Cannot use arrays-weak-equiv with model generation"
; EXPECT: Cannot use arrays-weak-equiv with model generation
; EXIT: 1
(set-logic ALL)
(declare-const  a (Array (_ BitVec 64) (_ BitVec 64))) 
(declare-const  b (_ BitVec 64)) 
(assert (= (store a #x1111111111111111 b) 
        (store a b #x1111111111111111))) 
(check-sat)
