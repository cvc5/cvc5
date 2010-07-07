(benchmark symmetric
:status unsat
:logic QF_UF
:extrapreds ((p U U))
:extrafuns ((x U) (y U))
:assumption (implies (p x y) (p y x))
:assumption (p x y)
:formula (not (p y x))
)
