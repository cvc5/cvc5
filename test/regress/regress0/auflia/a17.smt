(benchmark fuzzsmt
:logic QF_AUFLIA
:extrafuns ((a Array))
:extrafuns ((x1 Int))
:extrafuns ((y1 Int))
:extrafuns ((z0 Int))
:extrapreds ((p Array))
:status sat
:formula
(and
     (>= (select (store a (+ x1 z0) 1) x1) 1)
     (p a)
     (p (store a (+ x1 z0) 1))
     (p (store (store a (+ x1 z0) 1) y1 1))
     (>= x1 1)
     (>= z0 0)
     (<= z0 0)
     (<= y1 1)
     (>= y1 1)
)
)
