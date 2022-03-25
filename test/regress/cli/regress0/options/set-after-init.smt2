; EXPECT: 0
; EXPECT: 1
; EXPECT: 0
; EXPECT: 2
; EXPECT: sat
; EXPECT: 0
; EXPECT: (error "Invalid call to 'setOption' for option 'sat-random-seed', solver is already fully initialized")
; EXIT: 1

(get-option :verbosity)
(set-option :verbosity 1)
(get-option :verbosity)
(set-option :verbosity 0)
(get-option :sat-random-seed)
(set-option :sat-random-seed 2)
(get-option :sat-random-seed)

(set-logic QF_UF)
(declare-fun x () Bool)
(assert (or x (not x)))
(check-sat)

(set-option :verbosity 0)
(get-option :verbosity)
(set-option :sat-random-seed 1)
