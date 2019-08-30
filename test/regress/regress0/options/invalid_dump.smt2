; REQUIRES: dumping
; COMMAND-LINE: --dump invalidDumpTag
; ERROR-SCRUBBER: grep -o "unknown option for --dump"
; EXPECT-ERROR: unknown option for --dump
; EXIT: 1
