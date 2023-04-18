; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; EXPECT: (error "Parse Error:
; EXIT: 1
(set-logic ALL)
(assert (not ((_ to_fp 1))))
