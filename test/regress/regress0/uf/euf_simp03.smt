
(benchmark euf_simp3.smt
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
 (= (f (f x)) (f (f (f x))))
 (= (f (f x)) y)
 (= (f (f (f (f x)))) z)
 (= (f x) z)
 (not (= (f x) y))
 )
)