; EXPECT: true
; EXPECT: false
; EXPECT: 15
; EXPECT: none

(set-option :check-models true)
(get-option :check-models)
(set-option :check-models false)
(get-option :check-models)
(set-option :dag-thresh 15)
(get-option :dag-thresh)
(set-option :simplification none)
(get-option :simplification)
