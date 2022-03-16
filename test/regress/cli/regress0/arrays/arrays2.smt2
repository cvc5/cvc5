(set-logic QF_AX)
(set-info :source |
Benchmarks used in the followin paper:
Big proof engines as little proof engines: new results on rewrite-based satisfiability procedure
Alessandro Armando, Maria Paola Bonacina, Silvio Ranise, Stephan Schulz. 
PDPAR'05
http://www.ai.dist.unige.it/pdpar05/


|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun i0 () Index)
(declare-fun i1 () Index)
(assert (let ((?v_0 (select a1 i1))) (let ((?v_1 (store (store a1 i1 ?v_0) i1 ?v_0))) (let ((?v_2 (select ?v_1 i0))) (not (= (store (store ?v_1 i0 (select ?v_1 i1)) i1 ?v_2) (store (store ?v_1 i0 ?v_2) i0 ?v_2)))))))
(check-sat)
(exit)
