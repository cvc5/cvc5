; DISABLE-TESTER: dump
; SCRUBBER: grep -o 'Expected unicode string whose characters are less than code point'
; EXPECT: Expected unicode string whose characters are less than code point
; EXIT: 1
(set-logic ALL)
(declare-const x String)
(assert (= (str.++ x "T") (_ char #x93A83)))
(check-sat)
