; EXPECT: ((* 2))
; EXPECT: ((check-sat 1) (* 1))
; EXPECT: true
; EXPECT: false
; EXPECT: 15
; EXPECT: none

(get-option :command-verbosity)
(set-option :command-verbosity (* 1))
(set-option :command-verbosity (check-sat 1))
(get-option :command-verbosity)
(set-option :check-models true)
(get-option :check-models)
(set-option :check-models false)
(get-option :check-models)
(set-option :dag-thresh 15)
(get-option :dag-thresh)
(set-option :simplification none)
(get-option :simplification)
