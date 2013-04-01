(benchmark ConstantRewrite
:logic QF_LRA
:status sat
:extrafuns ((v0 Real))
:formula
(and
 (not (<= v0 0))
 (not (iff (= v0 0)
           (= v0 (/ 1 2))))
 )
)

