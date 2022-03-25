; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-logic AUFNIA)
(declare-fun _substvar_298_ () (Array Int Bool))
(declare-fun _substvar_379_ () (Array Bool (Array Int Bool)))
(declare-fun _substvar_400_ () (Array Bool (Array Int Bool)))
(declare-fun i0 () Int)
(declare-fun arr--325748303185799905_1467848600759014513-0 () (Array Int Bool))
(declare-fun arr-1467848600759014513_3143370635870088364-0 () (Array Bool (Array Int Bool)))
(assert (= _substvar_400_ (store arr-1467848600759014513_3143370635870088364-0 false (store (store arr--325748303185799905_1467848600759014513-0 776 true) i0 true)) (store arr-1467848600759014513_3143370635870088364-0 (>= i0 776) _substvar_298_) _substvar_379_))
(check-sat)
