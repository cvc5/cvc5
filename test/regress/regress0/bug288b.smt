(benchmark delta
:logic QF_LIA
:extrafuns ((x Int))
:extrafuns ((y Int))
:status sat
:formula
 (>= (* 2 (- x y)) 1)
)
