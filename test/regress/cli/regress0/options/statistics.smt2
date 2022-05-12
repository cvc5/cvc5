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
; EXPECT: false
; EXPECT: false
; EXPECT: false
; EXPECT: false
(set-logic QF_UF)
(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-internal)

(set-option :stats-all true)

(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-internal)

(set-option :stats false)

(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-internal)

(set-option :stats-internal true)

(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-internal)

(set-option :stats false)

(get-option :stats)
(get-option :stats-all)
(get-option :stats-every-query)
(get-option :stats-internal)