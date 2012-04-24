(benchmark mathsat
:logic QF_UFLRA
:status unsat 
:category { crafted } 
:extrafuns ((f Real Real))
:extrafuns ((x Real))
:extrafuns ((y Real))
:formula
(and (or (= x 3) (= x 5))
     (or (= y 3) (= y 5))
     (not (= (f x) (f y)))
     (implies (= (f 3) (f x)) (= (f 5) (f x)))
     (implies (= (f 3) (f y)) (= (f 5) (f y)))
)
)