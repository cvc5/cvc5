; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --input-agnuage
; SCRUBBER: grep -o "[a-zA-Z-]+"
; EXPECT: --input-language
; EXIT: 1
