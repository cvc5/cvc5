; EXPECT: stdout
; EXPECT: stderr
; EXPECT: stdin
; EXPECT-ERROR: stderr
; EXPECT-ERROR: stdout
; EXPECT-ERROR: stdin

(get-option :regular-output-channel)
(get-option :diagnostic-output-channel)
(get-option :in)

(set-option :regular-output-channel "stderr")
(set-option :diagnostic-output-channel "stdout")
(set-option :in "stdin")

(get-option :regular-output-channel)
(get-option :diagnostic-output-channel)
(get-option :in)
