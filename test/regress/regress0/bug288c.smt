(benchmark delta
:logic QF_LIA
:extrafuns ((x Int))
:extrafuns ((y Int))
:extrafuns ((z Int))
:status sat
:formula
  (and (= z 0) (>= (+ (- (* 2 x) (* 2 y)) z) 1))
)
