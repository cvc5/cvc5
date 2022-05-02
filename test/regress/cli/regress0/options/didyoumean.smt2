; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --input-agnuage
; ERROR-SCRUBBER: grep -o "--[a-zA-Z-]+"
; ERROR-EXPECT: --input-language
; EXIT: 1