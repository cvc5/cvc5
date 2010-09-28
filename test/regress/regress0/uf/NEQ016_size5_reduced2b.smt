(benchmark NEQ016_size5.smt
:logic QF_UF
:extrapreds ((p4 U))
:extrafuns ((c_4 U))
:extrafuns ((c7 U))
:extrafuns ((c_0 U))
:status unsat
:formula
(and
(not (p4 c_0))
(p4 c7)
(= c_0 c7)
)
)
