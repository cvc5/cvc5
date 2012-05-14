(benchmark swap
  :source {
Benchmarks used in the followin paper:
Big proof engines as little proof engines: new results on rewrite-based satisfiability procedure
Alessandro Armando, Maria Paola Bonacina, Silvio Ranise, Stephan Schulz. 
PDPAR'05
http://www.ai.dist.unige.it/pdpar05/


}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_AX
  :extrafuns ((a1 Array))
  :extrafuns ((i0 Index))
  :extrafuns ((i1 Index))
  :extrafuns ((i2 Index))
  :extrafuns ((i3 Index))
  :extrafuns ((i4 Index))
  :formula
(let (?cvc_4 (select a1 i4)) (let (?cvc_5 (select a1 i2)) (let (?cvc_0 (store (store a1 i4 ?cvc_5) i2 ?cvc_4)) (let (?cvc_1 (store (store ?cvc_0 i0 (select ?cvc_0 i3)) i3 (select ?cvc_0 i0))) (let (?cvc_2 (store (store ?cvc_1 i2 (select ?cvc_1 i1)) i1 (select ?cvc_1 i2))) (let (?cvc_3 (store (store ?cvc_2 i4 (select ?cvc_2 i3)) i3 (select ?cvc_2 i4))) (let (?cvc_6 (store (store a1 i2 ?cvc_4) i4 ?cvc_5)) (let (?cvc_7 (store (store ?cvc_6 i0 (select ?cvc_6 i3)) i3 (select ?cvc_6 i0))) (let (?cvc_8 (store (store ?cvc_7 i1 (select ?cvc_7 i2)) i2 (select ?cvc_7 i1))) (let (?cvc_9 (store (store ?cvc_8 i3 (select ?cvc_8 i4)) i4 (select ?cvc_8 i3))) (not (= (store (store ?cvc_3 i3 (select ?cvc_3 i2)) i2 (select ?cvc_3 i3)) (store (store ?cvc_9 i2 (select ?cvc_9 i3)) i3 (select ?cvc_9 i2))))))))))))))
)
