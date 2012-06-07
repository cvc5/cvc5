(benchmark test
:logic QF_UFLIA
:extrafuns ((f Int Int))
:extrafuns ((x1 Int))
:extrafuns ((y1 Int))
:extrafuns ((x2 Int))
:extrafuns ((y2 Int))

:extrafuns ((a Int))
:extrafuns ((b Int))

:assumption (= x1 x2)
:assumption (= y1 y2) 

:assumption (= x2 1)
:assumption (= y2 2)

:assumption (= (f x1) (f y1))

:formula true
)
