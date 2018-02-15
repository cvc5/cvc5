; COMMAND-LINE: --nl-ext --nl-ext-tplanes
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (let ((?v_0 (* skoY skoY))) (and (<= (* skoY (+ (/ 11722184772546574330443595776 12341362258596589055135468582520347) (* pi (/ (- 20000116509245440) 3119868895908289175433)))) (* pi (- 20))) (and (<= 0 skoY) (and (not (<= (/ 31415927 10000000) pi)) (and (not (<= pi (/ 15707963 5000000))) (and (= ?v_0 (+ 277555600 (* skoX (* skoX (+ 15328072984 (* skoX (* skoX (+ 129098541721 (* skoX (* skoX (+ 21404723599 (* skoX (* skoX (+ 1024027285 (* skoX (* skoX 15132100)))))))))))))))) (= ?v_0 (+ 277555600 (* (/ 265 128) (* (/ 265 128) (+ 15328072984 (* (/ 265 128) (* (/ 265 128) (+ 129098541721 (* (/ 265 128) (* (/ 265 128) (+ 21404723599 (* (/ 265 128) (* (/ 265 128) (+ 1024027285 (* (/ 265 128) (* (/ 265 128) 15132100)))))))))))))))))))))))
(check-sat)
(exit)
