; COMMAND-LINE: --lang=smt2.6
; EXPECT: sat
(set-logic SLIA)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (= x (_ char #x0D4)))
(assert (= x "\u00d4"))


(assert (= y (_ char #x1)))
(assert (= y "\u0001"))

(assert (= z (_ char #xAF)))
(assert (= z (_ char #x0af)))
(assert (= z "\u{af}"))
(assert (= z "\u00af"))

(check-sat)
