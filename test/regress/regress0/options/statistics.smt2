; REQUIRES: statistics
; EXPECT: false
; EXPECT: false
; EXPECT: false
; EXPECT: false
; EXPECT: true
; EXPECT: true
; EXPECT: false
; EXPECT: false
; EXPECT: false
; EXPECT: false
; EXPECT: false
; EXPECT: false
; EXPECT: true
; EXPECT: false
; EXPECT: false
; EXPECT: true
(set-logic QF_UF)
(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-expert)

(set-option :stats-all true)

(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-expert)

(set-option :stats false)

(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-expert)

(set-option :stats-expert true)

(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-expert)