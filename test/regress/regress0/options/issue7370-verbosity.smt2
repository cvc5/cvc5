; EXPECT: 0
; EXPECT: 1
; EXPECT: 0

(get-option :verbosity)
(set-option :verbosity 1)
(get-option :verbosity)
(set-option :verbosity -1)
(get-option :verbosity)
