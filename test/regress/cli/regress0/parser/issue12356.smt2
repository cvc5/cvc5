; DISABLE-TESTER: dump
; SCRUBBER: grep -o "Unexpected string for hexadecimal character"
; EXPECT: Unexpected string for hexadecimal character
; EXIT: 1
(set-logic ALL)
(define-fun s () String (_ char #x10FFFF))