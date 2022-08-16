; EXPECT: unsat
(set-logic ALL)
(set-option :global-declarations true)
(assert (! false :named x!1))
(assert x!1)
(check-sat)
