(benchmark fuzzsmt
:logic QF_UFLRA
:extrapreds ((p0 Real))
:extrafuns ((v0 Real))
:status sat
:formula
(and
     (p0 v0)
     (< v0 0)
     (not (p0 (- 1)))
))
