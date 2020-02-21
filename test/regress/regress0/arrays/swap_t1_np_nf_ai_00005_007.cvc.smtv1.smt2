(set-option :incremental false)
(set-info :source "Benchmarks used in the followin paper:
Big proof engines as little proof engines: new results on rewrite-based satisfiability procedure
Alessandro Armando, Maria Paola Bonacina, Silvio Ranise, Stephan Schulz. 
PDPAR'05
http://www.ai.dist.unige.it/pdpar05/")
(set-info :status unsat)
(set-info :difficulty "0")
(set-info :category "crafted")
(set-logic QF_AUF)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun i0 () Index)
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun i3 () Index)
(declare-fun i4 () Index)
(check-sat-assuming ( (let ((_let_0 (store (store a1 i4 (select a1 i2)) i2 (select a1 i4)))) (let ((_let_1 (store (store _let_0 i0 (select _let_0 i3)) i3 (select _let_0 i0)))) (let ((_let_2 (store (store _let_1 i2 (select _let_1 i1)) i1 (select _let_1 i2)))) (let ((_let_3 (store (store _let_2 i4 (select _let_2 i3)) i3 (select _let_2 i4)))) (let ((_let_4 (store (store a1 i2 (select a1 i4)) i4 (select a1 i2)))) (let ((_let_5 (store (store _let_4 i0 (select _let_4 i3)) i3 (select _let_4 i0)))) (let ((_let_6 (store (store _let_5 i1 (select _let_5 i2)) i2 (select _let_5 i1)))) (let ((_let_7 (store (store _let_6 i3 (select _let_6 i4)) i4 (select _let_6 i3)))) (not (= (store (store _let_3 i3 (select _let_3 i2)) i2 (select _let_3 i3)) (store (store _let_7 i2 (select _let_7 i3)) i3 (select _let_7 i2)))))))))))) ))
