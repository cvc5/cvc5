; EXPECT: 0
; EXPECT: 1
; EXPECT: 0
; EXPECT: 2
; EXPECT: sat
; EXPECT: 0
; EXPECT: (error "Invalid call to 'setOption' for option 'random-seed', solver is already fully initialized")
; EXIT: 1

(get-option :verbosity)
(set-option :verbosity 1)
(get-option :verbosity)
(set-option :verbosity 0)
(get-option :random-seed)
(set-option :random-seed 2)
(get-option :random-seed)

(set-logic QF_UF)
(declare-fun x () Bool)
(assert (or x (not x)))
(check-sat)

(set-option :verbosity 0)
(get-option :verbosity)
(set-option :random-seed 1)