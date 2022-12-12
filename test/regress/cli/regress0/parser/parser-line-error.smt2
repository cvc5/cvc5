; DISABLE-TESTER: dump
; EXIT: 1
; SCRUBBER: grep -o "(error "Parse Error: parser-line-error.smt2:7"
; EXPECT "(error "Parse Error: parser-line-error.smt2:7"
(set-info :source |abc
def
ghi|)
misplaced text
