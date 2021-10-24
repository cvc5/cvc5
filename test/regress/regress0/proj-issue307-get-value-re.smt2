; SCRUBBER: grep -v -E '\(error'
; EXPECT: sat
(set-logic ALL)
(reset)
(set-option :produce-models true)
(check-sat)
(get-value ((re.opt re.allchar)))
