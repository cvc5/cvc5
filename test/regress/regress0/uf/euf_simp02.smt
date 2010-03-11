
(benchmark euf_simp2.smt
:status unsat
:logic QF_UF
:category { crafted }

:extrafuns ((x U))
:extrafuns ((y U))
:extrafuns ((z U))
:extrafuns ((f U U))
:extrafuns ((g U U))
:extrafuns ((H U U U))
:extrafuns ((J U U U))



:formula
(and
 (not (= x y))
 (= (f x) (f z))
 (= (g y) (g z))
 (= (g y) (g z))
 (= (g y) y)
 (= (f x) x)
 (= (f z) z)
 (= (g z) z)
 (or (not (= x z)) (not (= y z)))
 )
)