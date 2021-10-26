Output tags
===========

cvc5 supports printing information about certain aspects of the solving process
that is intended for regular users. These can be enabled using the
:ref:`-o <lbl-option-output>` command line flag.

As of now, the following output tags are supported:


Quantifier instantiations (``-o inst``)
---------------------------------------

With ``-o inst``, cvc5 prints information about quantifier instantions for
individual quantifers.

.. code:: text

  $ cvc5 -o inst test/regress/regress1/quantifiers/qid-debug-inst.smt2 
  (num-instantiations myQuant1 1)
  (num-instantiations myQuant2 1)


Raw benchmark printing (``-o raw-benchmark``)
---------------------------------------------

With ``-o raw_benchmark`, cvc5 prints the benchmark back just as it has been
parsed.

.. code:: text
  
  $ cvc5 -o raw-benchmark test/regress/regress0/datatypes/datatype-dump.cvc.smt2 
  (set-option :incremental false)
  (set-logic ALL)
  (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
  (declare-fun x () nat)
  (check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))


SyGuS solving (``-o sygus``)
----------------------------

With ``-o sygus``, cvc5 prints information about the internal SyGuS solver
including enumerated terms and generated candidates.

.. code:: text
  
  $ cvc5 -o raw-benchmark test/regress/regress0/sygus/print-debug.sy 
  (set-option :incremental false)
  (set-logic LIA)
  (synth-fun f () Int
  
  ((Start Int) )
  ((Start Int (0 1 ))
  ))
  (constraint (not (= f 0)))
  (check-synth)
  (
  (define-fun f () Int 1)
  )


Quantifier triggers (``-o trigger``)
------------------------------------

With ``-o trigger``, cvc5 prints the selected triggers when solving a quantified
formula.

.. code:: text

  $ cvc5 -o trigger test/regress/regress1/quantifiers/qid-debug-inst.smt2 
  (trigger myQuant1 ((not (= (R x) false))))
  (trigger myQuant1 ((not (= (P x) true))))
  (trigger myQuant2 ((not (= (P x) false))))
  (trigger myQuant2 ((not (= (Q x) true))))
