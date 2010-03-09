(benchmark eq_diamond1
:source{
Generating minimum transitivity constraints in P-time for deciding Equality Logic,
Ofer Strichman and Mirron Rozanov,
SMT Workshop 2005.

Translator: Leonardo de Moura. }
:status unsat
:category { crafted }
:logic QF_UF
:difficulty { 0 }
:extrafuns ((x0 U) (y0 U) (z0 U)
)
:formula (and 
(not (= x0 x0))))
