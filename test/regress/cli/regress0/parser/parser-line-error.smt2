; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error: parser-line-error.smt2:8'
; EXPECT: (error "Parse Error: parser-line-error.smt2:8
; EXIT: 1
(set-info :source |abc
def
ghi|)
misplaced text
