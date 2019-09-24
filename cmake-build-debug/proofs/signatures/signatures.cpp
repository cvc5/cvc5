namespace CVC4 {
namespace proof {

extern const char *const plf_signatures;
const char *const plf_signatures = "\
\n\
(declare bool type)\n\
(declare tt bool)\n\
(declare ff bool)\n\
\n\
(declare var type)\n\
\n\
(declare lit type)\n\
(declare pos (! x var lit))\n\
(declare neg (! x var lit))\n\
\n\
; Flip the polarity of the literal\n\
(program lit_flip ((l lit)) lit\n\
         (match l\n\
                ((pos v) (neg v))\n\
                ((neg v) (pos v))))\n\
\n\
(declare clause type)\n\
(declare cln clause)\n\
(declare clc (! x lit (! c clause clause)))\n\
\n\
; A list of clauses, CNF if interpretted as a formula,\n\
; but also sometimes just a list\n\
(declare cnf type)\n\
(declare cnfn cnf)\n\
(declare cnfc (! h clause (! t cnf cnf)))\n\
\n\
; constructs for general clauses for R, Q, satlem\n\
\n\
(declare concat_cl (! c1 clause (! c2 clause clause)))\n\
(declare clr (! l lit (! c clause clause)))\n\
\n\
; code to check resolutions\n\
\n\
(program clause_append ((c1 clause) (c2 clause)) clause\n\
  (match c1 (cln c2) ((clc l c1') (clc l (clause_append c1' c2)))))\n\
\n\
; we use marks as follows:\n\
; -- mark 1 to record if we are supposed to remove a positive occurrence of the variable.\n\
; -- mark 2 to record if we are supposed to remove a negative occurrence of the variable.\n\
; -- mark 3 if we did indeed remove the variable positively\n\
; -- mark 4 if we did indeed remove the variable negatively\n\
(program simplify_clause ((c clause)) clause\n\
  (match c\n\
    (cln cln)\n\
    ((clc l c1)\n\
      (match l\n\
        ; Set mark 1 on v if it is not set, to indicate we should remove it.\n\
        ; After processing the rest of the clause, set mark 3 if we were already\n\
        ; supposed to remove v (so if mark 1 was set when we began).  Clear mark3\n\
        ; if we were not supposed to be removing v when we began this call.\n\
        ((pos v)\n\
          (let m (ifmarked v tt (do (markvar v) ff))\n\
          (let c' (simplify_clause c1)\n\
            (match m\n\
              (tt (do (ifmarked3 v v (markvar3 v)) c'))\n\
              (ff (do (ifmarked3 v (markvar3 v) v) (markvar v) (clc l c')))))))\n\
        ; the same as the code for tt, but using different marks.\n\
        ((neg v)\n\
          (let m (ifmarked2 v tt (do (markvar2 v) ff))\n\
          (let c' (simplify_clause c1)\n\
            (match m\n\
              (tt (do (ifmarked4 v v (markvar4 v)) c'))\n\
              (ff (do (ifmarked4 v (markvar4 v) v) (markvar2 v) (clc l c')))))))))\n\
    ((concat_cl c1 c2) (clause_append (simplify_clause c1) (simplify_clause c2)))\n\
    ((clr l c1)\n\
      (match l\n\
        ; set mark 1 to indicate we should remove v, and fail if\n\
        ; mark 3 is not set after processing the rest of the clause\n\
        ; (we will set mark 3 if we remove a positive occurrence of v).\n\
        ((pos v)\n\
            (let m (ifmarked v tt (do (markvar v) ff))\n\
            (let m3 (ifmarked3 v (do (markvar3 v) tt) ff)\n\
            (let c' (simplify_clause c1)\n\
              (ifmarked3 v (do (match m3 (tt v) (ff (markvar3 v)))\n\
                                (match m (tt v) (ff (markvar v))) c')\n\
                          (fail clause))))))\n\
        ; same as the tt case, but with different marks.\n\
        ((neg v)\n\
            (let m2 (ifmarked2 v tt (do (markvar2 v) ff))\n\
            (let m4 (ifmarked4 v (do (markvar4 v) tt) ff)\n\
            (let c' (simplify_clause c1)\n\
              (ifmarked4 v (do (match m4 (tt v) (ff (markvar4 v)))\n\
                                (match m2 (tt v) (ff (markvar2 v))) c')\n\
                          (fail clause))))))\n\
   ))))\n\
\n\
\n\
; resolution proofs\n\
\n\
(declare holds (! c clause type))\n\
\n\
(declare R (! c1 clause (! c2 clause\n\
           (! u1 (holds c1)\n\
           (! u2 (holds c2)\n\
           (! n var\n\
            (holds (concat_cl (clr (pos n) c1)\n\
                     (clr (neg n) c2)))))))))\n\
\n\
(declare Q (! c1 clause (! c2 clause\n\
           (! u1 (holds c1)\n\
           (! u2 (holds c2)\n\
           (! n var\n\
            (holds (concat_cl (clr (neg n) c1)\n\
                     (clr (pos n) c2)))))))))\n\
\n\
(declare satlem_simplify\n\
                (! c1 clause\n\
                (! c2 clause\n\
                (! c3 clause\n\
                (! u1 (holds c1)\n\
                (! r (^ (simplify_clause c1) c2)\n\
                (! u2 (! x (holds c2) (holds c3))\n\
                   (holds c3))))))))\n\
\n\
(declare satlem\n\
  (! c clause\n\
  (! c2 clause\n\
  (! u (holds c)\n\
  (! u2 (! v (holds c) (holds c2))\n\
    (holds c2))))))\n\
\n\
\n\
; Returns a copy of `c` with any duplicate literals removed.\n\
; Never fails.\n\
; Uses marks 3 & 4. Expects them to be clear before hand, and leaves them clear\n\
; afterwards.\n\
(program clause_dedup ((c clause)) clause\n\
         (match c\n\
                (cln cln)\n\
                ((clc l rest)\n\
                 (match l\n\
                        ((pos v) (ifmarked3\n\
                                   v\n\
                                   (clause_dedup rest)\n\
                                   (do (markvar3 v)\n\
                                     (let result (clc (pos v) (clause_dedup rest))\n\
                                       (do (markvar3 v) result)))))\n\
                        ((neg v) (ifmarked4\n\
                                   v\n\
                                   (clause_dedup rest)\n\
                                   (do (markvar4 v)\n\
                                     (let result (clc (neg v) (clause_dedup rest))\n\
                                       (do (markvar4 v) result)))))))))\n\
\n\
(declare cnf_holds (! c cnf type))\n\
(declare cnfn_proof (cnf_holds cnfn))\n\
(declare cnfc_proof\n\
         (! c clause\n\
         (! deduped_c clause\n\
            (! rest cnf\n\
               (! proof_c (holds c)\n\
                  (! proof_rest (cnf_holds rest)\n\
                     (! sc (^ (clause_dedup c) deduped_c)\n\
                        (cnf_holds (cnfc c rest)))))))))\n\
\n\
; A little example to demonstrate simplify_clause.\n\
; It can handle nested clr's of both polarities,\n\
; and correctly cleans up marks when it leaves a\n\
; clr or clc scope.  Uncomment and run with\n\
; --show-runs to see it in action.\n\
;\n\
; (check\n\
;   (% v1 var\n\
;   (% u1 (holds (concat_cl (clr (neg v1) (clr (pos v1) (clc (pos v1) (clr (pos v1) (clc (pos v1) (clc (neg v1) cln))))))\n\
;                    (clc (pos v1) (clc (pos v1) cln))))\n\
;    (satlem _ _ _ u1 (\\ x x))))))\n\
\n\
\n\
;(check\n\
;   (% v1 var\n\
;   (% u1 (holds (clr (neg v1) (concat_cl (clc (neg v1) cln)\n\
;                                      (clr (neg v1) (clc (neg v1) cln)))))\n\
;    (satlem _ _ _ u1 (\\ x x))))))\n\
\n\
; Depends on sat.plf\n\
\n\
; This file exists to support the **definition introduction** (or **extension**)\n\
; rule in the paper:\n\
;  \"Extended Resolution Simulates DRAT\"\n\
; which can be found at http://www.cs.utexas.edu/~marijn/publications/ijcar18.pdf\n\
;\n\
; The core idea of extended resolution is that given **any** formula f\n\
; involving the variables from some SAT problem, one can introduce the\n\
; constraint\n\
;\n\
;    new <=> f\n\
;\n\
; without changing satisfiability, where \"new\" is a fresh variable.\n\
;\n\
; This signature does not provide axioms for facilitating full use of this\n\
; idea. Instead, this signature facilitates use of one specific kind of\n\
; extension, that of the form:\n\
;\n\
;     new <=> old v (~l_1 ^ ~l_2 ^ ... ^ ~l_n)\n\
;\n\
; which translates into the clauses:\n\
;\n\
;                      new v l_1 v l_2 v ... v l_n\n\
;                      new v ~old\n\
;     for each i <= n: l_i v ~new v old\n\
;\n\
; This kind of extension is (a) sufficient to simulate DRAT proofs and (b) easy\n\
; to convert to clauses, which is why we use it.\n\
\n\
; A definition witness value for:\n\
;              new <=> old v (~others_1 ^ ~others_2 ^ ... ^ ~others_n)\n\
; It witnesses the fact that new was fresh when it was defined by the above.\n\
;\n\
; Thus it witnesses that the above, when added to the formula consisting of the\n\
; conjunction all the already-proven clauses, produces an equisatisfiable\n\
; formula.\n\
(declare definition (! new var (! old lit (! others clause type))))\n\
\n\
; Given `old` and `others`, this takes a continuation which expects\n\
;      1. a fresh variable `new`\n\
;      2. a definition witness value for:\n\
;              new <=> old v (~others_1 ^ ~others_2 ^ ... ^ ~others_n)\n\
;\n\
; Aside:\n\
;    In programming a **continuation** of some computation is a function that\n\
;    takes the results of that computation as arguments to produce a final\n\
;    result.\n\
;\n\
;    In proof-construction a **continuation** of some reasoning is a function\n\
;    that takes the results of that reasoning as arguments to proof a final\n\
;    result.\n\
;\n\
; That definition witness value can be clausified using the rule below.\n\
;\n\
; There need to be two different rules because the side-condition for\n\
; clausification needs access to the new variable, which doesn't exist except\n\
; inside the continuation, which is out-of-scope for any side-condition\n\
; associated with this rule.\n\
(declare decl_definition\n\
         (! old lit\n\
            (! others clause ; List of vars\n\
               (! pf_continuation (! new var (! def (definition new old others)\n\
                                           (holds cln)))\n\
                  (holds cln)))))\n\
\n\
; Takes a `list` of literals and a clause, `suffix`, adds the suffix to each\n\
; literal and returns a list of clauses as a `cnf`.\n\
(program clause_add_suffix_all ((list clause) (suffix clause)) cnf\n\
         (match list\n\
                (cln cnfn)\n\
                ((clc l rest) (cnfc (clc l suffix)\n\
                                    (clause_add_suffix_all rest suffix)))))\n\
\n\
; This translates a definition witness value for the def:\n\
;\n\
;    new <=> old v (~l_1 ^ ~l_2 ^ ... ^ ~l_n)\n\
;\n\
; into the clauses:\n\
;\n\
;                      new v l_1 v l_2 v ... v l_n\n\
;                      new v ~old\n\
;     for each i <= n: l_i v ~new v old              (encoded as (cnf_holds ...))\n\
(declare clausify_definition\n\
         (! new var\n\
         (! old lit\n\
         (! others clause\n\
         ; Given a definition { new <-> old v (~l_1 ^ ~l_2 ^ ... ^ ~l_n) }\n\
         (! def (definition new old others)\n\
         (! negOld lit\n\
         (! mkNegOld (^ (lit_flip old) negOld)\n\
         (! provenCnf cnf\n\
         (! mkProvenCnf (^ (clause_add_suffix_all\n\
                             others\n\
                             (clc (neg new) (clc old cln))) provenCnf)\n\
         ; If you can prove bottom from its clausal representation\n\
         (! pf_continuation\n\
            ; new v l_1 v l_2 v ... v l_n\n\
            (! pf_c1 (holds (clc (pos new) others))\n\
               ; new v ~old\n\
               (! pf_c2 (holds (clc (pos new) (clc negOld cln)))\n\
                  ; for each i <= n: l_i v ~new v old\n\
                  (! pf_cs (cnf_holds provenCnf)\n\
                     (holds cln))))\n\
         ; Then you've proven bottom\n\
         (holds cln)))))))))))\n\
\n\
; This axiom is useful for converting a proof of some CNF formula (a value of\n\
; type (cnf_holds ...)) into proofs of the constituent clauses (many values of\n\
; type (holds ...)).\n\
; Given\n\
;    1. a proof of some cnf, first ^ rest, and\n\
;    2. a proof continuation that\n\
;       a. takes in proofs of\n\
;          i. first and\n\
;          ii. rest and\n\
;       b. proceeds to prove bottom,\n\
; proves bottom.\n\
(declare cnfc_unroll_towards_bottom\n\
         (! first clause\n\
            (! rest cnf\n\
               (! pf (cnf_holds (cnfc first rest))\n\
                  (! pf_continuation (! r1 (holds first) (! r2 (cnf_holds rest) (holds cln)))\n\
                    (holds cln))))))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;\n\
; SMT syntax and semantics (not theory-specific)\n\
;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
; depends on sat.plf\n\
\n\
(declare formula type)\n\
(declare th_holds (! f formula type))\n\
\n\
; standard logic definitions\n\
(declare true formula)\n\
(declare false formula)\n\
\n\
(define formula_op1\n\
	(! f formula\n\
	formula))\n\
\n\
(define formula_op2\n\
	(! f1 formula\n\
	(! f2 formula\n\
	   formula)))\n\
\n\
(define formula_op3\n\
	(! f1 formula\n\
	(! f2 formula\n\
	(! f3 formula\n\
	   formula))))\n\
\n\
(declare not formula_op1)\n\
(declare and formula_op2)\n\
(declare or formula_op2)\n\
(declare impl formula_op2)\n\
(declare iff formula_op2)\n\
(declare xor formula_op2)\n\
(declare ifte formula_op3)\n\
\n\
; terms\n\
(declare sort type)\n\
(declare term (! t sort type))	; declared terms in formula\n\
\n\
; standard definitions for =, ite, let and flet\n\
(declare = (! s sort\n\
           (! x (term s)\n\
           (! y (term s)\n\
             formula))))\n\
(declare ite (! s sort\n\
             (! f formula\n\
             (! t1 (term s)\n\
             (! t2 (term s)\n\
               (term s))))))\n\
(declare let (! s sort\n\
             (! t (term s)\n\
             (! f (! v (term s) formula)\n\
               formula))))\n\
(declare flet (! f1 formula\n\
              (! f2 (! v formula formula)\n\
                formula)))\n\
\n\
; We view applications of predicates as terms of sort \"Bool\".\n\
; Such terms can be injected as atomic formulas using \"p_app\".\n\
(declare Bool sort)				; the special sort for predicates\n\
(declare p_app (! x (term Bool) formula))	; propositional application of term\n\
\n\
; boolean terms\n\
(declare t_true (term Bool))\n\
(declare t_false (term Bool))\n\
(declare t_t_neq_f\n\
 (th_holds (not (= Bool t_true t_false))))\n\
(declare pred_eq_t\n\
 (! x (term Bool)\n\
 (! u (th_holds (p_app x))\n\
   (th_holds (= Bool x t_true)))))\n\
\n\
(declare pred_eq_f\n\
 (! x (term Bool)\n\
 (! u (th_holds (not (p_app x)))\n\
   (th_holds (= Bool x t_false)))))\n\
\n\
(declare f_to_b\n\
  (! f formula\n\
    (term Bool)))\n\
\n\
(declare true_preds_equal\n\
  (! x1 (term Bool)\n\
  (! x2 (term Bool)\n\
  (! u1 (th_holds (p_app x1))\n\
  (! u2 (th_holds (p_app x2))\n\
    (th_holds (= Bool x1 x2)))))))\n\
\n\
(declare false_preds_equal\n\
  (! x1 (term Bool)\n\
  (! x2 (term Bool)\n\
  (! u1 (th_holds (not (p_app x1)))\n\
  (! u2 (th_holds (not (p_app x2)))\n\
    (th_holds (= Bool x1 x2)))))))\n\
\n\
(declare pred_refl_pos\n\
  (! x1 (term Bool)\n\
  (! u1 (th_holds (p_app x1))\n\
    (th_holds (= Bool x1 x1)))))\n\
\n\
(declare pred_refl_neg\n\
  (! x1 (term Bool)\n\
  (! u1 (th_holds (not (p_app x1)))\n\
    (th_holds (= Bool x1 x1)))))\n\
\n\
(declare pred_not_iff_f\n\
  (! x (term Bool)\n\
  (! u (th_holds (not (iff false (p_app x))))\n\
    (th_holds (= Bool t_true x)))))\n\
\n\
(declare pred_not_iff_f_2\n\
  (! x (term Bool)\n\
  (! u (th_holds (not (iff (p_app x) false)))\n\
    (th_holds (= Bool x t_true)))))\n\
\n\
(declare pred_not_iff_t\n\
  (! x (term Bool)\n\
  (! u (th_holds (not (iff true (p_app x))))\n\
    (th_holds (= Bool t_false x)))))\n\
\n\
(declare pred_not_iff_t_2\n\
  (! x (term Bool)\n\
  (! u (th_holds (not (iff (p_app x) true)))\n\
    (th_holds (= Bool x t_false)))))\n\
\n\
(declare pred_iff_f\n\
  (! x (term Bool)\n\
  (! u (th_holds (iff false (p_app x)))\n\
    (th_holds (= Bool t_false x)))))\n\
\n\
(declare pred_iff_f_2\n\
  (! x (term Bool)\n\
  (! u (th_holds (iff (p_app x) false))\n\
    (th_holds (= Bool x t_false)))))\n\
\n\
(declare pred_iff_t\n\
  (! x (term Bool)\n\
  (! u (th_holds (iff true (p_app x)))\n\
    (th_holds (= Bool t_true x)))))\n\
\n\
(declare pred_iff_t_2\n\
  (! x (term Bool)\n\
  (! u (th_holds (iff (p_app x) true))\n\
    (th_holds (= Bool x t_true)))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;\n\
; CNF Clausification\n\
;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
; binding between an LF var and an (atomic) formula\n\
\n\
(declare atom (! v var (! p formula type)))\n\
\n\
; binding between two LF vars\n\
(declare bvatom (! sat_v var (! bv_v var type)))\n\
\n\
(declare decl_atom\n\
  (! f formula\n\
  (! u (! v var\n\
       (! a (atom v f)\n\
         (holds cln)))\n\
    (holds cln))))\n\
\n\
;; declare atom enhanced with mapping\n\
;; between SAT prop variable and BVSAT prop variable\n\
(declare decl_bvatom\n\
  (! f formula\n\
  (! u (! v var\n\
       (! bv_v var\n\
       (! a (atom v f)\n\
       (! bva (atom bv_v f)\n\
       (! vbv (bvatom v bv_v)\n\
         (holds cln))))))\n\
    (holds cln))))\n\
\n\
\n\
; clausify a formula directly\n\
(declare clausify_form\n\
  (! f formula\n\
  (! v var\n\
  (! a (atom v f)\n\
  (! u (th_holds f)\n\
    (holds (clc (pos v) cln)))))))\n\
\n\
(declare clausify_form_not\n\
  (! f formula\n\
  (! v var\n\
  (! a (atom v f)\n\
  (! u (th_holds (not f))\n\
    (holds (clc (neg v) cln)))))))\n\
\n\
(declare clausify_false\n\
  (! u (th_holds false)\n\
    (holds cln)))\n\
\n\
(declare th_let_pf\n\
  (! f formula\n\
  (! u (th_holds f)\n\
  (! u2 (! v (th_holds f) (holds cln))\n\
    (holds cln)))))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;\n\
; Natural deduction rules : used for CNF\n\
;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
;; for eager bit-blasting\n\
(declare iff_symm\n\
	(! f formula\n\
	   (th_holds (iff f f))))\n\
\n\
\n\
;; contradiction\n\
\n\
(declare contra\n\
  (! f formula\n\
  (! r1 (th_holds f)\n\
  (! r2 (th_holds (not f))\n\
    (th_holds false)))))\n\
\n\
; truth\n\
(declare truth (th_holds true))\n\
\n\
;; not not\n\
\n\
(declare not_not_intro\n\
  (! f formula\n\
  (! u (th_holds f)\n\
    (th_holds (not (not f))))))\n\
\n\
(declare not_not_elim\n\
  (! f formula\n\
  (! u (th_holds (not (not f)))\n\
    (th_holds f))))\n\
\n\
;; or elimination\n\
\n\
(declare or_elim_1\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u1 (th_holds (not f1))\n\
  (! u2 (th_holds (or f1 f2))\n\
    (th_holds f2))))))\n\
\n\
(declare or_elim_2\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u1 (th_holds (not f2))\n\
  (! u2 (th_holds (or f1 f2))\n\
    (th_holds f1))))))\n\
\n\
(declare not_or_elim\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u2 (th_holds (not (or f1 f2)))\n\
    (th_holds (and (not f1) (not f2)))))))\n\
\n\
;; and elimination\n\
\n\
(declare and_elim_1\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u (th_holds (and f1 f2))\n\
    (th_holds f1)))))\n\
\n\
(declare and_elim_2\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u (th_holds (and f1 f2))\n\
    (th_holds f2)))))\n\
\n\
(declare not_and_elim\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u2 (th_holds (not (and f1 f2)))\n\
    (th_holds (or (not f1) (not f2)))))))\n\
\n\
;; impl elimination\n\
\n\
(declare impl_intro (! f1 formula\n\
                    (! f2 formula\n\
                    (! i1 (! u (th_holds f1)\n\
                              (th_holds f2))\n\
                      (th_holds (impl f1 f2))))))\n\
\n\
(declare impl_elim\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u2 (th_holds (impl f1 f2))\n\
    (th_holds (or (not f1) f2))))))\n\
\n\
(declare not_impl_elim\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u (th_holds (not (impl f1 f2)))\n\
    (th_holds (and f1 (not f2)))))))\n\
\n\
;; iff elimination\n\
\n\
(declare iff_elim_1\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u1 (th_holds (iff f1 f2))\n\
    (th_holds (or (not f1) f2))))))\n\
\n\
(declare iff_elim_2\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u1 (th_holds (iff f1 f2))\n\
    (th_holds (or f1 (not f2)))))))\n\
\n\
(declare not_iff_elim\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u2 (th_holds (not (iff f1 f2)))\n\
    (th_holds (iff f1 (not f2)))))))\n\
\n\
; xor elimination\n\
\n\
(declare xor_elim_1\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u1 (th_holds (xor f1 f2))\n\
    (th_holds (or (not f1) (not f2)))))))\n\
\n\
(declare xor_elim_2\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u1 (th_holds (xor f1 f2))\n\
    (th_holds (or f1 f2))))))\n\
\n\
(declare not_xor_elim\n\
  (! f1 formula\n\
  (! f2 formula\n\
  (! u2 (th_holds (not (xor f1 f2)))\n\
    (th_holds (iff f1 f2))))))\n\
\n\
;; ite elimination\n\
\n\
(declare ite_elim_1\n\
  (! a formula\n\
  (! b formula\n\
  (! c formula\n\
  (! u2 (th_holds (ifte a b c))\n\
    (th_holds (or (not a) b)))))))\n\
\n\
(declare ite_elim_2\n\
  (! a formula\n\
  (! b formula\n\
  (! c formula\n\
  (! u2 (th_holds (ifte a b c))\n\
    (th_holds (or a c)))))))\n\
\n\
(declare ite_elim_3\n\
  (! a formula\n\
  (! b formula\n\
  (! c formula\n\
  (! u2 (th_holds (ifte a b c))\n\
    (th_holds (or b c)))))))\n\
\n\
(declare not_ite_elim_1\n\
  (! a formula\n\
  (! b formula\n\
  (! c formula\n\
  (! u2 (th_holds (not (ifte a b c)))\n\
    (th_holds (or (not a) (not b))))))))\n\
\n\
(declare not_ite_elim_2\n\
  (! a formula\n\
  (! b formula\n\
  (! c formula\n\
  (! u2 (th_holds (not (ifte a b c)))\n\
    (th_holds (or a (not c))))))))\n\
\n\
(declare not_ite_elim_3\n\
  (! a formula\n\
  (! b formula\n\
  (! c formula\n\
  (! u2 (th_holds (not (ifte a b c)))\n\
    (th_holds (or (not b) (not c))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;\n\
; For theory lemmas\n\
; - make a series of assumptions and then derive a contradiction (or false)\n\
; - then the assumptions yield a formula like \"v1 -> v2 -> ... -> vn -> false\"\n\
; - In CNF, it becomes a clause: \"~v1, ~v2, ..., ~vn\"\n\
;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(declare ast\n\
  (! v var\n\
  (! f formula\n\
  (! C clause\n\
  (! r (atom v f)       ;this is specified\n\
  (! u (! o (th_holds f)\n\
         (holds C))\n\
    (holds (clc (neg v) C))))))))\n\
\n\
(declare asf\n\
  (! v var\n\
  (! f formula\n\
  (! C clause\n\
  (! r (atom v f)\n\
  (! u (! o (th_holds (not f))\n\
         (holds C))\n\
    (holds (clc (pos v) C))))))))\n\
\n\
;; Bitvector lemma constructors to assume\n\
;; the unit clause containing the assumptions\n\
;; it also requires the mapping between bv_v and v\n\
;; The resolution proof proving false will use bv_v as the definition clauses use bv_v\n\
;; but the Problem clauses in the main SAT solver will use v so the learned clause is in terms of v\n\
(declare bv_asf\n\
  (! v var\n\
  (! bv_v var\n\
  (! f formula\n\
  (! C clause\n\
  (! r (atom v f) ;; passed in\n\
  (! x (bvatom v bv_v) ; establishes the equivalence of v to bv_\n\
  (! u (! o (holds (clc (neg bv_v) cln)) ;; l binding to be used in proof\n\
         (holds C))\n\
    (holds (clc (pos v) C))))))))))\n\
\n\
(declare bv_ast\n\
  (! v var\n\
  (! bv_v var\n\
  (! f formula\n\
  (! C clause\n\
  (! r (atom v f)       ; this is specified\n\
  (! x (bvatom v bv_v) ; establishes the equivalence of v to bv_v\n\
  (! u (! o (holds (clc (pos bv_v) cln))\n\
         (holds C))\n\
    (holds (clc (neg v) C))))))))))\n\
\n\
;; Numeric primitives\n\
\n\
(program mpz_sub ((x mpz) (y mpz)) mpz\n\
	 (mp_add x (mp_mul (~1) y)))\n\
\n\
(program mp_ispos ((x mpz)) formula\n\
	 (mp_ifneg x false true))\n\
\n\
(program mpz_eq ((x mpz) (y mpz)) formula\n\
    (mp_ifzero (mpz_sub x y) true false))\n\
\n\
(program mpz_lt ((x mpz) (y mpz)) formula\n\
    (mp_ifneg (mpz_sub x y) true false))\n\
\n\
(program mpz_lte ((x mpz) (y mpz)) formula\n\
    (mp_ifneg (mpz_sub x y) true (mpz_eq x y)))\n\
\n\
;; Example:\n\
;;\n\
;; Given theory literals (F1....Fn), and an input formula A of the form (th_holds (or F1 (or F2 .... (or F{n-1} Fn))))).\n\
;;\n\
;; We introduce atoms (a1,...,an) to map boolean literals (v1,...,vn) top literals (F1,...,Fn).\n\
;; Do this at the beginning of the proof:\n\
;;\n\
;; (decl_atom F1 (\\ v1 (\\ a1\n\
;; (decl_atom F2 (\\ v2 (\\ a2\n\
;; ....\n\
;; (decl_atom Fn (\\ vn (\\ an\n\
;;\n\
;;  A is then clausified by the following proof:\n\
;;\n\
;;(satlem _ _\n\
;;(asf _ _ _ a1 (\\ l1\n\
;;(asf _ _ _ a2 (\\ l2\n\
;;...\n\
;;(asf _ _ _ an (\\ ln\n\
;;(clausify_false\n\
;;\n\
;;   (contra _\n\
;;      (or_elim_1 _ _ l{n-1}\n\
;;	...\n\
;;      (or_elim_1 _ _ l2\n\
;; 	(or_elim_1 _ _ l1 A))))) ln)\n\
;;\n\
;;))))))) (\\ C\n\
;;\n\
;; We now have the free variable C, which should be the clause (v1 V ... V vn).\n\
;;\n\
;; Polarity of literals should be considered, say we have A of the form (th_holds (or (not F1) (or F2 (not F3)))).\n\
;; Where necessary, we use \"ast\" instead of \"asf\", introduce negations by \"not_not_intro\" for pattern matching, and flip\n\
;; the arguments of contra:\n\
;;\n\
;;(satlem _ _\n\
;;(ast _ _ _ a1 (\\ l1\n\
;;(asf _ _ _ a2 (\\ l2\n\
;;(ast _ _ _ a3 (\\ l3\n\
;;(clausify_false\n\
;;\n\
;;   (contra _ l3\n\
;;      (or_elim_1 _ _ l2\n\
;; 	(or_elim_1 _ _ (not_not_intro l1) A))))\n\
;;\n\
;;))))))) (\\ C\n\
;;\n\
;; C should be the clause (~v1 V v2 V ~v3 )\n\
\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;\n\
; Theory of Equality and Congruence Closure\n\
;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
; depends on : smt.plf\n\
\n\
; sorts :\n\
\n\
(declare arrow (! s1 sort (! s2 sort sort)))	; function constructor\n\
\n\
; functions :\n\
\n\
(declare apply (! s1 sort\n\
               (! s2 sort\n\
               (! t1 (term (arrow s1 s2))\n\
               (! t2 (term s1)\n\
                (term s2))))))\n\
\n\
\n\
; inference rules :\n\
\n\
(declare trust (th_holds false))	; temporary\n\
(declare trust_f (! f formula (th_holds f)))  ; temporary\n\
\n\
(declare refl\n\
  (! s sort\n\
  (! t (term s)\n\
    (th_holds (= s t t)))))\n\
\n\
(declare symm (! s sort\n\
              (! x (term s)\n\
              (! y (term s)\n\
              (! u (th_holds (= _ x y))\n\
                (th_holds (= _ y x)))))))\n\
\n\
(declare trans (! s sort\n\
               (! x (term s)\n\
               (! y (term s)\n\
               (! z (term s)\n\
               (! u (th_holds (= _ x y))\n\
               (! u (th_holds (= _ y z))\n\
                 (th_holds (= _ x z)))))))))\n\
\n\
(declare negsymm (! s sort\n\
              	 (! x (term s)\n\
              	 (! y (term s)\n\
              	 (! u (th_holds (not (= _ x y)))\n\
                   (th_holds (not (= _ y x))))))))\n\
\n\
(declare negtrans1 (! s sort\n\
                   (! x (term s)\n\
              	   (! y (term s)\n\
               	   (! z (term s)\n\
               	   (! u (th_holds (not (= _ x y)))\n\
               	   (! u (th_holds (= _ y z))\n\
                     (th_holds (not (= _ x z))))))))))\n\
\n\
(declare negtrans2 (! s sort\n\
                   (! x (term s)\n\
              	   (! y (term s)\n\
               	   (! z (term s)\n\
               	   (! u (th_holds (= _ x y))\n\
               	   (! u (th_holds (not (= _ y z)))\n\
                     (th_holds (not (= _ x z))))))))))\n\
\n\
(declare cong (! s1 sort\n\
              (! s2 sort\n\
              (! a1 (term (arrow s1 s2))\n\
              (! b1 (term (arrow s1 s2))\n\
              (! a2 (term s1)\n\
              (! b2 (term s1)\n\
              (! u1 (th_holds (= _ a1 b1))\n\
              (! u2 (th_holds (= _ a2 b2))\n\
                (th_holds (= _ (apply _ _ a1 a2) (apply _ _ b1 b2))))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
; Examples\n\
\n\
; an example of \"(p1 or p2(0)) and t1=t2(1)\"\n\
;(! p1 (term Bool)\n\
;(! p2 (term (arrow Int Bool))\n\
;(! t1 (term Int)\n\
;(! t2 (term (arrow Int Int))\n\
;(! F (th_holds (and (or (p_app p1) (p_app (apply _ _ p2 0)))\n\
;                    (= _ t1 (apply _ _ t2 1))))\n\
;  ...\n\
\n\
; another example of \"p3(a,b)\"\n\
;(! a (term Int)\n\
;(! b (term Int)\n\
;(! p3 (term (arrow Int (arrow Int Bool)))	; arrow is right assoc.\n\
;(! F (th_holds (p_app (apply _ _ (apply _ _ p3 a) b))) ; apply is left assoc.\n\
;  ...\n\
\n\
; LRAT Proof signature\n\
; LRAT format detailed in \"Efficient Certified RAT Verification\"\n\
; Link: https://www.cs.utexas.edu/~marijn/publications/lrat.pdf\n\
; Author: aozdemir\n\
; Depends On: sat.plf, smt.plf\n\
\n\
\n\
; A general note about the design of the side conditions:\n\
;  Some side-conditions make use of a _global assignment_ encoded in\n\
;  0 (true) / 1 (false) marks on variables.\n\
\n\
; Unit (https://en.wikipedia.org/wiki/Unit_type)\n\
; For functions that don't return anything\n\
(declare Unit type) ; The type with only one value (like `void` in C)\n\
(declare unit Unit) ; That value\n\
\n\
; Boolean operator (not short-circuiting)\n\
(program bool_or ((l bool) (r bool)) bool (match l (ff r) (tt tt)))\n\
(program bool_and ((l bool) (r bool)) bool (match l (tt r) (ff ff)))\n\
(program bool_not ((b bool)) bool (match b (tt ff) (ff tt)))\n\
(program bool_eq ((l bool) (r bool)) bool\n\
         (match l\n\
                (tt (match r\n\
                           (tt tt)\n\
                           (ff ff)))\n\
                (ff (match r\n\
                           (tt ff)\n\
                           (ff tt)))))\n\
\n\
; =================== ;\n\
; Working CNF formula ;\n\
; =================== ;\n\
\n\
; Represents a CNF formula as a map from clause indices to clauses\n\
; Should be sorted ascending, always!\n\
; Here, and for all collections, the suffix \"n\" denotes the empty collection and\n\
; the suffix \"c\" denotes the constructor for the collection in the style of lisp's\n\
; \"cons cells\"\n\
(declare CMap type)\n\
(declare CMapn CMap)\n\
(declare CMapc (! i mpz (! c clause (! r CMap CMap))))\n\
\n\
; ================= ;\n\
; LRAT Proof Format ;\n\
; ================= ;\n\
\n\
; CI lists are lists of clause indices.\n\
; They represent clauses to delete.\n\
; They must be sorted.\n\
(declare CIList type)\n\
(declare CIListn CIList)\n\
(declare CIListc (! z mpz (! zs CIList CIList)))\n\
\n\
; Traces are a list of clause indices into the working CNF formula\n\
; They represent the clauses that will be unit in a unit propegation to bottom\n\
; Thus their elements are *not* in value order.\n\
(declare Trace type)\n\
(declare Tracen Trace)\n\
(declare Tracec (! z mpz (! zs Trace Trace)))\n\
\n\
; RAT Hint list\n\
; Each hint is\n\
;   * An index indicating a clause in the working CNF formula to resolve with\n\
;   * A trace indicating how UP should be done after that resolution\n\
(declare RATHints type)\n\
(declare RATHintsn RATHints)\n\
(declare RATHintsc\n\
         (! target mpz\n\
            (! trace Trace\n\
               (! rest RATHints\n\
                  RATHints))))\n\
\n\
; LRAT proof\n\
(declare LRATProof type)\n\
(declare LRATProofn LRATProof)\n\
; Deletion (includes a list of clause indices to delete)\n\
(declare LRATProofd (! cis CIList (! rest LRATProof LRATProof)))\n\
; Addition: a clause index, a clause, RUP trace for that clause, and hints for\n\
; what resolutions should happen then, and how those resolutions imply bottom\n\
; via UP.\n\
; If the list of hints is empty, then bottom is already implied.\n\
(declare LRATProofa\n\
         (! ci mpz\n\
            (! c clause\n\
               (! t Trace\n\
                  (! h RATHints\n\
                     (! rest LRATProof\n\
                        LRATProof))))))\n\
\n\
; ========================================== ;\n\
; Functional programs for manipulating types ;\n\
; ========================================== ;\n\
\n\
; Are two literal equal?\n\
(program lit_eq ((l1 lit) (l2 lit)) bool\n\
         (match l1\n\
                ((pos v1) (match l2\n\
                                 ((pos v2) (ifequal v1 v2 tt ff))\n\
                                 ((neg v2) ff)))\n\
                ((neg v1) (match l2\n\
                                 ((pos v2) ff)\n\
                                 ((neg v2) (ifequal v1 v2 tt ff))))))\n\
\n\
; Remove **all** occurences of a literal from clause\n\
(program clause_remove_all ((l lit) (c clause)) clause\n\
         (match c\n\
                (cln cln)\n\
                ((clc l' c')\n\
                 (let rest_res (clause_remove_all l c')\n\
                   (match (lit_eq l l')\n\
                          (tt rest_res)\n\
                          (ff (clc l' rest_res)))))))\n\
\n\
; Return the clause's first  literal\n\
; fails on an empty clause\n\
(program clause_head ((c clause)) lit\n\
         (match c\n\
                (cln (fail lit))\n\
                ((clc l c') l)))\n\
\n\
; Does a clause contain some literal?\n\
(program clause_contains_lit ((c clause) (l lit)) bool\n\
         (match c\n\
                ((clc l' c') (match (lit_eq l l')\n\
                                    (tt tt)\n\
                                    (ff (clause_contains_lit c' l))))\n\
                (cln ff)))\n\
\n\
; Append two traces\n\
(program Trace_concat ((t1 Trace) (t2 Trace)) Trace\n\
         (match t1\n\
                (Tracen t2)\n\
                ((Tracec h1 r1) (Tracec h1 (Trace_concat r1 t2)))))\n\
\n\
; Return whether a list of RAT hits is empty\n\
(program RATHints_is_empty ((h RATHints)) bool\n\
         (match h\n\
                (RATHintsn tt)\n\
                ((RATHintsc a b c) ff)))\n\
\n\
; Insert into a CMap, preserving order\n\
(program CMap_insert ((i mpz) (c clause) (cs CMap)) CMap\n\
         (match cs\n\
                (CMapn (CMapc i c CMapn))\n\
                ((CMapc i' c' r)\n\
                 (mp_ifneg (mpz_sub i i')\n\
                        (CMapc i c cs)\n\
                        (CMapc i' c' (CMap_insert i c r))))))\n\
\n\
; Get from a CMap\n\
(program CMap_get ((i mpz) (cs CMap)) clause\n\
         (match cs\n\
                (CMapn (fail clause))\n\
                ((CMapc i' c r)\n\
                 (mp_ifzero (mpz_sub i i')\n\
                        c\n\
                        (CMap_get i r)))))\n\
\n\
; Remove from CMap. Only removes one element.\n\
(program CMap_remove ((i mpz) (cs CMap)) CMap\n\
         (match cs\n\
                (CMapn CMapn)\n\
                ((CMapc i' c r)\n\
                 (mp_ifzero (mpz_sub i i')\n\
                        r\n\
                        (CMapc i' c (CMap_remove i r))))))\n\
\n\
; Remove many indices from a CMap. Asuumes the input list is sorted.\n\
(program CMap_remove_many ((is CIList) (cs CMap)) CMap\n\
         (match\n\
           is\n\
           (CIListn cs)\n\
           ((CIListc i is')\n\
            (match\n\
              cs\n\
              (CMapn (fail CMap)) ; All deletion indices must be valid!\n\
              ((CMapc ci c cs')\n\
               (mp_ifzero (mpz_sub i ci)\n\
                       (CMap_remove_many is' cs')\n\
                       (CMapc ci c (CMap_remove_many is cs'))))))))\n\
\n\
; Given a map of clauses and a literal, return all indices in the map\n\
; corresponsing to clauses that could resolve against that literal. i.e. for x,\n\
; return the indices of all clauses containing x.\n\
(program collect_resolution_targets_w_lit ((cs CMap) (l lit)) CIList\n\
         (match cs\n\
                (CMapn CIListn)\n\
                ((CMapc i c cs')\n\
                 (let rest_solution (collect_resolution_targets_w_lit cs' l)\n\
                   (match (clause_contains_lit c l)\n\
                        (tt (CIListc i rest_solution))\n\
                        (ff rest_solution))))))\n\
\n\
; Given a clause and a maps of clauses, return all indices in the map\n\
; corresponding to clauses which could resolve with this one on its first\n\
; literal\n\
(program collect_resolution_targets ((cs CMap) (c clause)) CIList\n\
         (collect_resolution_targets_w_lit cs (lit_flip (clause_head c))))\n\
\n\
; Is this clause a tautology?\n\
; Internally uses mark 5 to flag variables that occur (+)\n\
; and mark 6 to flag variables that occur (-)\n\
(program is_t ((c clause)) bool\n\
         (match\n\
           c\n\
           (cln ff)\n\
           ((clc l c') (match\n\
                         l\n\
                         ((pos v)\n\
                          (ifmarked5\n\
                            v\n\
                            (is_t c')\n\
                            (ifmarked6\n\
                              v\n\
                              tt\n\
                              (do\n\
                                (markvar5 v)\n\
                                (let r (is_t c') (do (markvar5 v) r))))))\n\
                         ((neg v)\n\
                          (ifmarked6\n\
                            v\n\
                            (is_t c')\n\
                            (ifmarked5\n\
                              v\n\
                              tt\n\
                              (do\n\
                                (markvar6 v)\n\
                                (let r (is_t c') (do (markvar6 v) r))))))))))\n\
\n\
; ===================================================================== ;\n\
; Programs for manipulating and querying the global variable assignment ;\n\
; ===================================================================== ;\n\
\n\
; This assignment marks values of type `var`.\n\
; It marks a variable with 1 if that variable is true\n\
; It marks a variable with 2 if that variable is false\n\
; A variable should not be marked with both!\n\
; A variable may be marked with neither, indicating that variable is presently\n\
; unassigned, which we call \"floating\".\n\
\n\
; Mark the variable within to satisfy this literal.\n\
; fails if the literal is already UNSAT\n\
(program lit_mk_sat ((l lit)) Unit\n\
         (match l\n\
                ((pos v) (ifmarked2 v\n\
                                    (fail Unit)\n\
                                    (ifmarked1 v unit (do (markvar1 v) unit))))\n\
                ((neg v) (ifmarked1 v\n\
                                    (fail Unit)\n\
                                    (ifmarked2 v unit (do (markvar2 v) unit))))))\n\
\n\
; Mark the variable within to falsify this literal.\n\
; fails is the literal is already SAT\n\
(program lit_mk_unsat ((l lit)) Unit\n\
         (match l\n\
                ((neg v) (ifmarked2 v\n\
                                    (fail Unit)\n\
                                    (ifmarked1 v unit (do (markvar1 v) unit))))\n\
                ((pos v) (ifmarked1 v\n\
                                    (fail Unit)\n\
                                    (ifmarked2 v unit (do (markvar2 v) unit))))))\n\
\n\
; Unmarks the variable within a satified literal to render it neither satified nor falsified\n\
; fails if the literal is not already satisfied\n\
(program lit_un_mk_sat ((l lit)) Unit\n\
         (match l\n\
                ((pos v) (ifmarked1 v (do (markvar1 v) unit) (fail Unit)))\n\
                ((neg v) (ifmarked2 v (do (markvar2 v) unit) (fail Unit)))))\n\
\n\
; Unmarks the variable within a falsified literal to render it neither satified nor falsified\n\
; fails if the literal is not already falsified\n\
(program lit_un_mk_unsat ((l lit)) Unit\n\
         (match l\n\
                ((pos v) (ifmarked2 v (do (markvar2 v) unit) (fail Unit)))\n\
                ((neg v) (ifmarked1 v (do (markvar1 v) unit) (fail Unit)))))\n\
\n\
;  Is a literal presently satisfied?\n\
(program lit_is_sat ((l lit)) bool\n\
         (match l\n\
                ((pos v) (ifmarked1 v tt ff))\n\
                ((neg v) (ifmarked2 v tt ff))))\n\
\n\
;  Is a literal presently falsified?\n\
(program lit_is_unsat ((l lit)) bool\n\
         (match l\n\
                ((pos v) (ifmarked2 v tt ff))\n\
                ((neg v) (ifmarked1 v tt ff))))\n\
\n\
;  Is a  literal presently neither satisfied nor falsified?\n\
(program lit_is_floating ((l lit)) bool\n\
         (bool_not (bool_or (lit_is_sat l) (lit_is_unsat l))))\n\
\n\
; Does this clause contain a floating literal?\n\
(program clause_has_floating ((c clause)) bool\n\
         (match c\n\
                (cln ff)\n\
                ((clc l c') (match (lit_is_floating l)\n\
                                   (tt tt)\n\
                                   (ff (clause_has_floating c'))))))\n\
\n\
; Is this clause falsified? i.e. are all its clauses falsified?\n\
(program clause_is_unsat ((c clause)) bool\n\
         (match c\n\
                (cln tt)\n\
                ((clc l c') (match (lit_is_unsat l)\n\
                                   (tt (clause_is_unsat c'))\n\
                                   (ff ff)))))\n\
\n\
; Is this clause presently satisfied?\n\
(program clause_is_sat ((c clause)) bool\n\
         (match c\n\
                (cln ff)\n\
                ((clc l c') (match (lit_is_sat l)\n\
                                   (tt tt)\n\
                                   (ff (clause_is_sat c'))))))\n\
\n\
; Falsify **all** contained literals.\n\
; Fails on a tautological clause\n\
(program clause_mk_all_unsat ((c clause)) Unit\n\
         (match c\n\
                (cln unit)\n\
                ((clc l c') (do\n\
                              (lit_mk_unsat l)\n\
                              (clause_mk_all_unsat c')))))\n\
\n\
; Unfalsifies **all** contained literals\n\
; Fails on a clause with duplicate literals\n\
(program clause_un_mk_all_unsat ((c clause)) Unit\n\
         (match c\n\
                (cln unit)\n\
                ((clc l c') (do\n\
                              (lit_un_mk_unsat l)\n\
                              (clause_un_mk_all_unsat c')))))\n\
\n\
; Get the first floating literal out of this clause.\n\
; fails if there are no floating literals\n\
(program clause_first_floating ((c clause)) lit\n\
         (match c\n\
                (cln (fail lit))\n\
                ((clc l c') (match (lit_is_floating l)\n\
                                   (tt l)\n\
                                   (ff (clause_first_floating c'))))))\n\
\n\
; ===================================== ;\n\
; High-Level Programs for LRAT Checking ;\n\
; ===================================== ;\n\
\n\
; The return type for verifying that a clause is unit and modifying the global\n\
; assignment to satisfy it\n\
(declare MarkResult type)\n\
; The clause is unit, and this is the (previoiusly floating) literal that is now satified.\n\
(declare MRUnit (! l lit MarkResult))\n\
; The clause was unsat!\n\
(declare MRUnsat MarkResult)\n\
; The clauss was already satisfied.\n\
(declare MRSat MarkResult)\n\
; The clause had multiple floating literals.\n\
(declare MRNotUnit MarkResult)\n\
\n\
; Determine wether this clause is sat, unsat, unit, or not unit, and if it is\n\
; unit, it modifies the global assignment to satisfy the clause, and returns\n\
; the literal that was made SAT by the new mark.\n\
;\n\
; If `c` is a tautology, reports `MRSat`, since it is (trivially) satisfied.\n\
(program clause_check_unit_and_maybe_mark ((c clause)) MarkResult\n\
         (match (clause_is_sat c)\n\
                (tt MRSat)\n\
                (ff (match (clause_is_unsat c)\n\
                           (tt MRUnsat)\n\
                           (ff (match (is_t c)\n\
                                      (tt MRSat)\n\
                                      (ff ; Dedent\n\
         (match (clause_has_floating c)\n\
                (tt (let first (clause_first_floating c)\n\
                      (do (lit_mk_sat first)\n\
                        (match (clause_has_floating c)\n\
                               (tt (do (lit_un_mk_sat first) MRNotUnit))\n\
                                      (ff (MRUnit first))))))\n\
                ; Unreachable. If clause is not floating it must have been SAT or UNSAT.\n\
                (ff (fail MarkResult))\n\
                ))))))))\n\
\n\
; The return type for the process of Trace-guided unit propegation\n\
(declare UPResult type)\n\
; The trace guided unit propegation correctly, but that unit propegation did not end in an empty clause\n\
(declare UPR_Ok UPResult)\n\
; The trace guided unit propegation correctly to an empty clause\n\
(declare UPR_Bottom UPResult)\n\
; The trace was malformed,\n\
;; i.e. at some point indicates that a non-unit, non-empty clause should be examined\n\
(declare UPR_Broken UPResult)\n\
\n\
; Execute the unit propegation indicated by the trace. Report whether that\n\
; unit propegation succeeds and produces bottom, fails, or succeeds but does\n\
; not produce bottom.\n\
;\n\
; If the trace tries to propegate through a TAUT clause, fails.\n\
(program do_up ((cs CMap) (t Trace)) UPResult\n\
         (match\n\
           t\n\
           (Tracen UPR_Ok)\n\
           ((Tracec i r) (match (clause_check_unit_and_maybe_mark (CMap_get i cs))\n\
                                ((MRUnit l)\n\
                                 (let res (do_up cs r)\n\
                                   (do (lit_un_mk_sat l) res)))\n\
                                (MRUnsat UPR_Bottom)\n\
                                (MRSat UPR_Broken)\n\
                                (MRNotUnit UPR_Broken)))))\n\
\n\
\n\
; Determine whether a list of indices agrees with the list of indices latent in\n\
; a list of hints. Both lists should be sorted.\n\
(program resolution_targets_match (\n\
                                   (computed CIList)\n\
                                   (given RATHints)) bool\n\
         (match given\n\
                (RATHintsn\n\
                  (match computed\n\
                         (CIListn tt)\n\
                         ((CIListc a b) ff)))\n\
                ((RATHintsc hint_idx t given')\n\
                 (match computed\n\
                        ((CIListc comp_idx computed')\n\
                         (mp_ifzero (mpz_sub hint_idx comp_idx)\n\
                                    (resolution_targets_match computed' given')\n\
                                    (ff)))\n\
                        (CIListn ff)))))\n\
\n\
\n\
; Determines whether `t` is a witness that `c` is an Assymetric Tautology in `cs`.\n\
;\n\
; Does unit propegation in the formula `cs`, beginning by falsifying\n\
; all literals in `c`, and then looking at the clauses indicated by `t`.\n\
; Assumes no marks, and cleans up marks afterwards.\n\
;\n\
; Fails if `c` has duplicates\n\
(program is_at_trace ((cs CMap) (c clause) (t Trace)) UPResult\n\
         (match (is_t c)\n\
                (ff\n\
                  (do\n\
                    (clause_mk_all_unsat c)\n\
                    (let result (do_up cs t)\n\
                      (do (clause_un_mk_all_unsat c) result))))\n\
                (tt\n\
                  UPR_Bottom)))\n\
\n\
\n\
\n\
; List of (clause, trace) pairs\n\
(declare CTPairs type)\n\
(declare CTPn CTPairs)\n\
(declare CTPc (! c clause (! t Trace (! rest CTPairs CTPairs))))\n\
\n\
; For each RAT hint, construct the pseudo-resolvant for that hint, and the net\n\
; trace for that hint. Return a list of these.\n\
;\n\
; Pseudo resolvant: if l v C is the clause, and D is another clause containing\n\
; ~l, then l v C v (D \\ ~l) is the pseudo-resolvant, which is the actual\n\
; resolant, plut l, which would be implied by UP.\n\
;\n\
; The net trace is the global trace (`t`), plut the trace for that specific\n\
; resolvant.\n\
(program construct_ct_pairs (\n\
                             (cs CMap)\n\
                             (c clause)\n\
                             (t Trace)\n\
                             (hints RATHints)\n\
                            ) CTPairs\n\
         (match hints\n\
                (RATHintsn CTPn)\n\
                ((RATHintsc i ht hints')\n\
                 (CTPc\n\
                   (clause_dedup (clause_append c\n\
                                  (clause_remove_all (lit_flip (clause_head c))\n\
                                                     (CMap_get i cs))))\n\
                   (Trace_concat t ht)\n\
                   (construct_ct_pairs cs c t hints')))))\n\
\n\
; Goes through a list of clause, trace pairs and verifies that each clause is\n\
; an AT via that trace.\n\
; Fails if any putative AT is a TAUT or contains duplicates\n\
(program are_all_at_trace (\n\
                     (cs CMap)\n\
                     (l CTPairs)\n\
                    ) UPResult\n\
         (match l\n\
                (CTPn UPR_Bottom)\n\
                ((CTPc c t l')\n\
                 (match (is_at_trace cs c t)\n\
                        (UPR_Ok UPR_Ok)\n\
                        (UPR_Broken UPR_Broken)\n\
                        (UPR_Bottom (are_all_at_trace cs l'))))))\n\
\n\
; Is this trace, and list of hints, proof that `c` is an Resolution Assymeytic\n\
; Tautology?\n\
; Fails is the hints are empty (which means `c` should  be AT) and `c` contains\n\
; duplicates)\n\
(program is_rat_trace ((cs CMap) (c clause) (t Trace) (hints RATHints)) UPResult\n\
         (match\n\
           (RATHints_is_empty hints)\n\
           (tt ; Empty RAT hints -- the clause must be AT\n\
             (is_at_trace cs c t))\n\
           (ff ; Ew -- we must verify this is a RAT\n\
             (match (resolution_targets_match\n\
                      (collect_resolution_targets cs c)\n\
                      hints)\n\
                    (ff ; Resolution targets disagree with hints.\n\
                      UPR_Broken)\n\
                    (tt\n\
                      (are_all_at_trace cs (construct_ct_pairs cs c t hints)))))))\n\
\n\
; Is this proof an LRAT proof of bottom?\n\
; Fails if any added AT is a TAUT or contains duplicates OR if any added RAT\n\
; produces pseudo-resolvants which are TAUT or contain duplicates\n\
(program is_lrat_proof_of_bottom ((f CMap) (proof LRATProof)) bool\n\
         (match proof\n\
                ((LRATProofd indices rest)\n\
                 (is_lrat_proof_of_bottom\n\
                   (CMap_remove_many indices f)\n\
                   rest))\n\
                ((LRATProofa idx c trace hints rest)\n\
                 (match (is_rat_trace f c trace hints)\n\
                    (UPR_Bottom\n\
                      (match\n\
                        c\n\
                        (cln tt)\n\
                        ((clc a b)\n\
                         (is_lrat_proof_of_bottom (CMap_insert idx c f) rest))))\n\
                    (UPR_Ok ff)\n\
                    (UPR_Broken ff)))\n\
                (LRATProofn ff))\n\
         )\n\
\n\
\n\
; Proof of a CMap from clause proofs.\n\
; The idx is unelidable b/c it is unspecified.\n\
;  Robust against clauses with duplicat literals, but not against tautological\n\
;  clauses.\n\
(declare CMap_holds (! c CMap type))\n\
(declare CMapn_proof (CMap_holds CMapn))\n\
(declare CMapc_proof\n\
         (! idx mpz ; Not elidable!\n\
            (! c clause\n\
               (! deduped_c clause\n\
                  (! rest CMap\n\
                     (! proof_c (holds c)\n\
                        (! proof_rest (CMap_holds rest)\n\
                            (! sc (^ (clause_dedup c) deduped_c)\n\
                               (CMap_holds (CMapc idx deduped_c rest))))))))))\n\
\n\
(define bottom (holds cln))\n\
(declare lrat_proof_of_bottom\n\
         (! cm CMap\n\
            (! proof_cm (CMap_holds cm)\n\
               (! proof LRATProof\n\
                  (! sc (^ (is_lrat_proof_of_bottom cm proof) tt)\n\
                     bottom)))))\n\
\n\
\n\
; TODO(aozdemir) Reducing the amount of checking that resides in side-conditions.\n\
; Steps\n\
;  1. Unroll the traversal of is_lrat_proof_of_bottom into a serialized\n\
;     sequence of axiom applications.\n\
;     The axioms would likely correspond to DELETE, IS T, IS AT, IS RAT.\n\
;     They would manipulate a CMap by way of side-conditions.\n\
;  2. Unroll AT checks by manifesting the assignment in data rather than marks,\n\
;     and having axioms like IS_UNSAT, IS_UNIT_ON_LITERAL.\n\
;  3. Unroll RAT checks in a similar fashion, although more painfully.\n\
\n\
; Depends on lrat.plf\n\
;\n\
; Implementation of DRAT checking.\n\
;\n\
; Unfortunately, there are **two** different notions of DRAT floating around in\n\
; the world:\n\
;   * Specified   DRAT : This is a reasonable proof format\n\
;   * Operational DRAT : This is a variant of specified DRAT warped by the\n\
;                        details of common SAT solver architectures.\n\
;\n\
; Both are detailed in this paper, along with their differences:\n\
;   http://fmv.jku.at/papers/RebolaPardoBiere-POS18.pdf\n\
;\n\
; This signature checks **Specified DRAT**.\n\
\n\
; A DRAT proof itself: a list of addition or deletion instructions.\n\
(declare DRATProof type)\n\
(declare DRATProofn DRATProof)\n\
(declare DRATProofa (! c clause (! p DRATProof DRATProof)))\n\
(declare DRATProofd (! c clause (! p DRATProof DRATProof)))\n\
\n\
; ==================== ;\n\
; Functional  Programs ;\n\
; ==================== ;\n\
\n\
; Are two clauses equal (in the set sense)\n\
;\n\
; Assumes that marks 1,2,3,4 are clear for the constituent variables, and\n\
; leaves them clear afterwards.\n\
;\n\
; Since clauses are sets, it is insufficient to do list equality.\n\
; We could sort them, but that would require defining an order on our variables,\n\
; and incurring the cost of sorting.\n\
;\n\
;\n\
; Instead, we do the following:\n\
;  1. Sweep the first clause, marking variables with flags 1,3 (pos) and 2,4 (neg)\n\
;  2. Sweep the second clause, erasing marks 1,2. Returning FALSE if no mark 3,4.\n\
;  3. Unsweep the first clause, returning FALSE on marks 1,2.\n\
;     Also unmarking 3,4, and 1,2 if needed\n\
;\n\
; So the mark 1 means (seen as + in c1, but not yet in c2)\n\
;    the mark 3 means (seen as + in c1)\n\
;    the mark 2 means (seen as - in c1, but not yet in c2)\n\
;    the mark 4 means (seen as - in c1)\n\
;\n\
; This implementation is robust to literal order, repeated literals, and\n\
; literals of opposite polarity in the same clause. It is true equality on sets\n\
; literals.\n\
;\n\
; TODO(aozdemir) This implementation could be further optimized b/c once c1 is\n\
; drained, we need not continue to pattern match on it.\n\
(program clause_eq ((c1 clause) (c2 clause)) bool\n\
         (match\n\
           c1\n\
           (cln (match\n\
                  c2\n\
                  (cln tt)\n\
                  ((clc c2h c2t) (match\n\
                                   c2h\n\
                                   ((pos v)\n\
                                    (ifmarked1\n\
                                      v\n\
                                      (do (markvar1 v)\n\
                                        (clause_eq c1 c2t))\n\
                                      (ifmarked3\n\
                                        v\n\
                                        (clause_eq c1 c2t)\n\
                                        ff)))\n\
                                   ((neg v)\n\
                                    (ifmarked2\n\
                                      v\n\
                                      (do (markvar2 v)\n\
                                        (clause_eq c1 c2t))\n\
                                      (ifmarked4\n\
                                        v\n\
                                        (clause_eq c1 c2t)\n\
                                        ff)))))))\n\
           ((clc c1h c1t) (match\n\
                            c1h\n\
                            ((pos v)\n\
                             (ifmarked3\n\
                               v\n\
                               (clause_eq c1t c2)\n\
                               (do (markvar3 v)\n\
                                 (do (markvar1 v)\n\
                                   (let res (clause_eq c1t c2)\n\
                                     (do (markvar3 v)\n\
                                       (ifmarked1\n\
                                         v\n\
                                         (do (markvar1 v) ff)\n\
                                         res)))))))\n\
                            ((neg v)\n\
                             (ifmarked4\n\
                               v\n\
                               (clause_eq c1t c2)\n\
                               (do (markvar4 v)\n\
                                 (do (markvar2 v)\n\
                                   (let res (clause_eq c1t c2)\n\
                                     (do (markvar4 v)\n\
                                       (ifmarked2\n\
                                         v\n\
                                         (do (markvar2 v) ff)\n\
                                         res)))))))))))\n\
\n\
\n\
; Does this formula contain bottom as one of its clauses?\n\
(program cnf_has_bottom ((cs cnf)) bool\n\
         (match cs\n\
                (cnfn ff)\n\
                ((cnfc c rest) (match c\n\
                                      (cln tt)\n\
                                      ((clc l c') (cnf_has_bottom rest))))))\n\
\n\
; Return a new cnf with one copy of this clause removed.\n\
; If the clause is absent, returns the original cnf.\n\
(program cnf_remove_clause ((c clause) (cs cnf)) cnf\n\
         (match cs\n\
                (cnfn cnfn)\n\
                ((cnfc c' cs')\n\
                 (match (clause_eq c c')\n\
                        (tt cs')\n\
                        (ff (cnfc c' (cnf_remove_clause c cs')))))))\n\
\n\
; return (c1 union (c2 \\ ~l))\n\
; Significant for how a RAT is defined.\n\
(program clause_pseudo_resolvent ((c1 clause) (c2 clause)) clause\n\
         (clause_dedup (clause_append c1\n\
                                      (clause_remove_all\n\
                                        (lit_flip (clause_head c1)) c2))))\n\
\n\
; Given a formula, `cs` and a clause `c`, return all pseudo resolvents, i.e. all\n\
;     (c union (c' \\ ~head(c)))\n\
;   for c' in cs, where c' contains ~head(c)\n\
(program collect_pseudo_resolvents ((cs cnf) (c clause)) cnf\n\
         (match cs\n\
                (cnfn cnfn)\n\
                ((cnfc c' cs')\n\
                 (let rest_of_resolvents (collect_pseudo_resolvents cs' c)\n\
                   (match (clause_contains_lit c' (lit_flip (clause_head c)))\n\
                          (tt (cnfc (clause_pseudo_resolvent\n\
                                      c\n\
                                      c')\n\
                                    rest_of_resolvents))\n\
                          (ff rest_of_resolvents))))))\n\
\n\
; =============================================================== ;\n\
; Unit Propegation implementation (manipulates global assignment) ;\n\
; =============================================================== ;\n\
; See the lrat file for a description of the global assignment.\n\
\n\
; The result of search for a unit clause in\n\
(declare UnitSearchResult type)\n\
; There was a unit, and\n\
;    this is the (previously floating) literal that is now satisfied.\n\
;    this is a version of the input cnf with satisfied clauses removed.\n\
(declare USRUnit (! l lit (! f cnf UnitSearchResult)))\n\
; There was an unsat clause\n\
(declare USRBottom UnitSearchResult)\n\
; There was no unit.\n\
(declare USRNoUnit UnitSearchResult)\n\
\n\
; If a UnitSearchResult is a Unit, containing a cnf, adds this clause to that\n\
; cnf. Otherwise, returns the UnitSearchResult unmodified.\n\
(program USR_add_clause ((c clause) (usr UnitSearchResult)) UnitSearchResult\n\
         (match usr\n\
                ((USRUnit l f) (USRUnit l (cnfc c f)))\n\
                (USRBottom USRBottom)\n\
                (USRNoUnit USRNoUnit)))\n\
\n\
; Searches through the clauses, looking for a unit clause.\n\
; Reads the global assignment. Possibly assigns one variable.\n\
;  Returns\n\
;    USRBottom     if there is an unsat clause\n\
;    (USRUnit l f) if there is a unit, with lit l, and\n\
;                  f is the cnf with some SAT clauses removed.\n\
;    USRNoUnit     if there is no unit\n\
(program unit_search ((f cnf)) UnitSearchResult\n\
         (match f\n\
                (cnfn USRNoUnit)\n\
                ((cnfc c f')\n\
                 (match (clause_check_unit_and_maybe_mark c)\n\
                        (MRSat (unit_search f'))\n\
                        ((MRUnit l) (USRUnit l f'))\n\
                        (MRUnsat USRBottom)\n\
                        (MRNotUnit (USR_add_clause c (unit_search f')))))))\n\
\n\
\n\
; Given the current global assignment, does the formula `f` imply bottom via\n\
; unit propegation? Leaves the global assignment in the same state that it was\n\
; initially.\n\
(program unit_propegates_to_bottom ((f cnf)) bool\n\
         (match (unit_search f)\n\
                (USRBottom tt)\n\
                ((USRUnit l f') (let result (unit_propegates_to_bottom f')\n\
                               (do (lit_un_mk_sat l)\n\
                                 result)))\n\
                (USRNoUnit ff)))\n\
\n\
; ================================== ;\n\
; High-Level DRAT checking functions ;\n\
; ================================== ;\n\
\n\
; Is this clause an AT?\n\
(program is_at ((cs cnf) (c clause)) bool\n\
         (match (is_t c)\n\
                (tt tt)\n\
                (ff (do (clause_mk_all_unsat c)\n\
                      (let r (unit_propegates_to_bottom cs)\n\
                        (do (clause_un_mk_all_unsat c)\n\
                          r))))))\n\
\n\
; Are all of these clauses ATs?\n\
(program are_all_at ((cs cnf) (clauses cnf)) bool\n\
         (match clauses\n\
                (cnfn tt)\n\
                ((cnfc c clauses')\n\
                 (match (is_at cs c)\n\
                        (tt (are_all_at cs clauses'))\n\
                        (ff ff)))))\n\
\n\
; Is the clause `c` a RAT for the formula `cs`?\n\
(program is_rat ((cs cnf) (c clause)) bool\n\
         (match (is_t c)\n\
                (tt tt)\n\
                (ff (match (is_at cs c)\n\
                           (tt tt)\n\
                           (ff (match c\n\
                                      (cln ff)\n\
                                      ((clc a b) (are_all_at ; dedent\n\
                                 cs\n\
                                 (collect_pseudo_resolvents cs c)))))))))\n\
\n\
; Is this proof a valid DRAT proof of bottom?\n\
(program is_specified_drat_proof ((f cnf) (proof DRATProof)) bool\n\
         (match proof\n\
                (DRATProofn (cnf_has_bottom f))\n\
                ((DRATProofa c p) (match\n\
                                    (is_rat f c)\n\
                                    (tt (is_specified_drat_proof (cnfc c f) p))\n\
                                    (ff ff)))\n\
                ((DRATProofd c p)\n\
                 (is_specified_drat_proof (cnf_remove_clause c f) p))))\n\
\n\
\n\
; =============================== ;\n\
; Operational DRAT implementation ;\n\
; =============================== ;\n\
\n\
; Operation DRAT is defined in the paper \"Two Flavors of DRAT\".\n\
; Below is an extension of the DRAT signature to handle it.\n\
\n\
; Notes on types.\n\
; For operational DRAT it is useful to manifest partial assignments in values\n\
; (although we still use the global assignment in some places). To this end,\n\
; literals are used to represent single-variable assignments ((pos v) denotes\n\
; {v maps to true}) and clauses are partial assignments by way of being\n\
; literal lists.\n\
\n\
; Copy the partial assignment represented by a clause into the global\n\
; assignment. Fails if that clause represents an inconsistent partial\n\
; assignment (e.g. v is both true and false)\n\
(program clause_into_global ((a clause)) Unit\n\
         (match a\n\
                (cln unit)\n\
                ((clc l rest)\n\
                 (do (lit_mk_sat l) (clause_into_global rest)))))\n\
\n\
; Remove the partial assignment represented by c from the global assignment\n\
(program clause_undo_into_global ((a clause)) Unit\n\
         (match a\n\
                (cln unit)\n\
                ((clc l rest)\n\
                 (do (lit_un_mk_sat l) (clause_undo_into_global rest)))))\n\
\n\
; Does this clause have no floating literals w.r.t. the global assignment?\n\
(program clause_no_floating ((c clause)) bool\n\
         (match c\n\
                (cln tt)\n\
                ((clc l rest) (match (lit_is_floating l)\n\
                                    (tt ff)\n\
                                    (ff (clause_no_floating rest))))))\n\
\n\
; Does this clause have no sat literals w.r.t. the global assignment?\n\
(program clause_no_sat ((c clause)) bool\n\
         (match c\n\
                (cln tt)\n\
                ((clc l rest) (match (lit_is_sat l)\n\
                                    (tt ff)\n\
                                    (ff (clause_no_sat rest))))))\n\
\n\
; Does this clause have one sat literal w.r.t. the global assignment?\n\
(program clause_one_sat ((c clause)) bool\n\
         (match c\n\
                (cln ff)\n\
                ((clc l rest) (match (lit_is_sat l)\n\
                                    (tt (clause_no_sat rest))\n\
                                    (ff (clause_one_sat rest))))))\n\
\n\
; Is this clause a unit clause w.r.t. the global assignment?\n\
; This notion is defined as:\n\
;    * A clause where no literals are floating, and exactly one is sat.\n\
(program clause_is_unit_wrt_up_model ((c clause) (up_model clause)) bool\n\
         (let c' (clause_dedup c)\n\
         (do (clause_into_global up_model)\n\
           (let result (match (clause_no_floating c')\n\
                              (tt (clause_one_sat c'))\n\
                              (ff ff))\n\
             (do (clause_undo_into_global up_model)\n\
               result)))))\n\
\n\
; Result from constructing a UP model (defined in \"Two Flavors of DRAT\")\n\
; Technically, we're constructing the shared UP model -- the intersection of all\n\
; UP models.\n\
; Informally, this is just the partial assignment implied by UP.\n\
;\n\
; This type is necessary, because constructing a UP model can reveal an\n\
; inconsistent UP model -- one which assigns some variable to true and false.\n\
; This would break our machinery, so we special case it.\n\
(declare UPConstructionResult type)\n\
; An actual model\n\
(declare UPCRModel (! up_model clause UPConstructionResult))\n\
; Bottom is implied!\n\
(declare UPCRBottom UPConstructionResult)\n\
\n\
\n\
; Do unit propagation on `f`, constructing a UP model for it.\n\
(program build_up_model ((f cnf)) UPConstructionResult\n\
         (match (unit_search f)\n\
                (USRBottom UPCRBottom)\n\
                (USRNoUnit (UPCRModel cln))\n\
                ((USRUnit l f')\n\
                 (let result (build_up_model f')\n\
                   (do (lit_un_mk_sat l)\n\
                     (match result\n\
                            (UPCRBottom UPCRBottom)\n\
                            ((UPCRModel model) (UPCRModel (clc l model)))))))))\n\
\n\
; Given some starting assignment (`up_model`), continue UP to construct a larger\n\
; model.\n\
(program extend_up_model ((f cnf) (up_model clause)) UPConstructionResult\n\
         (do (clause_into_global up_model)\n\
           (let result (build_up_model f)\n\
             (do (clause_undo_into_global up_model)\n\
               (match result\n\
                      (UPCRBottom UPCRBottom)\n\
                      ((UPCRModel up_model')\n\
                       (UPCRModel (clause_append up_model up_model'))))))))\n\
\n\
; Helper for `is_operational_drat_proof` which takes a UP model for the working\n\
; formula. The UP model is important for determining which clause deletions\n\
; actually are executed in operational DRAT. Passing the UP model along\n\
; prevents it from being fully recomputed everytime.\n\
(program is_operational_drat_proof_h ((f cnf) (up_model clause) (pf DRATProof)) bool\n\
         (match pf\n\
                (DRATProofn (cnf_has_bottom f))\n\
                ((DRATProofd c pf')\n\
                 (match (clause_is_unit_wrt_up_model c up_model)\n\
                        (tt (is_operational_drat_proof_h f up_model pf'))\n\
                        (ff (is_operational_drat_proof_h\n\
                              (cnf_remove_clause c f) up_model pf'))))\n\
                ((DRATProofa c pf')\n\
                 (let f' (cnfc c f)\n\
                   (match (is_rat f c)\n\
                          (tt (match (extend_up_model f' up_model)\n\
                                     (UPCRBottom tt)\n\
                                     ((UPCRModel up_model')\n\
                                      (is_operational_drat_proof_h f' up_model' pf'))))\n\
                          (ff ff))))))\n\
\n\
; Is this an operational DRAT proof of bottom for this formula?\n\
(program is_operational_drat_proof ((f cnf) (pf DRATProof)) bool\n\
         (match (build_up_model f)\n\
                (UPCRBottom tt)\n\
                ((UPCRModel model) (is_operational_drat_proof_h f model pf))))\n\
\n\
; Is this a specified or operational DRAT proof of bottom for this formula?\n\
(program is_drat_proof ((f cnf) (pf DRATProof)) bool\n\
         (match (is_specified_drat_proof f pf)\n\
                (tt tt)\n\
                (ff (is_operational_drat_proof f pf))))\n\
\n\
(declare drat_proof_of_bottom\n\
         (! f cnf\n\
            (! proof_of_formula (cnf_holds f)\n\
               (! proof DRATProof\n\
                  (! sc (^ (is_drat_proof f proof) tt)\n\
                     bottom)))))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;\n\
; Theory of Arrays\n\
;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
; depends on : th_base.plf\n\
\n\
; sorts\n\
\n\
(declare Array (! s1 sort (! s2 sort sort)))	; s1 is index, s2 is element\n\
\n\
; functions\n\
(declare write (! s1 sort\n\
               (! s2 sort\n\
                 (term (arrow (Array s1 s2)\n\
                       (arrow s1\n\
                       (arrow s2 (Array s1 s2))))))))\n\
\n\
(declare read (! s1 sort\n\
              (! s2 sort\n\
              	(term (arrow (Array s1 s2)\n\
               	      (arrow s1 s2))))))\n\
\n\
; inference rules\n\
\n\
; read( a[i] = b, i ) == b\n\
(declare row1 (! s1 sort\n\
              (! s2 sort\n\
              (! t1 (term (Array s1 s2))\n\
              (! t2 (term s1)\n\
              (! t3 (term s2)\n\
              	(th_holds (= _\n\
		(apply _ _ (apply _ _ (read s1 s2) (apply _ _ (apply _ _ (apply _ _ (write s1 s2) t1) t2) t3)) t2) t3))))))))\n\
\n\
; read( a[i] = b, j ) == read( a, j ) if i != j\n\
(declare row (! s1 sort\n\
             (! s2 sort\n\
             (! t2 (term s1)\n\
             (! t3 (term s1)\n\
             (! t1 (term (Array s1 s2))\n\
             (! t4 (term s2)\n\
             (! u (th_holds (not (= _ t2 t3)))\n\
               (th_holds (= _ (apply _ _ (apply _ _ (read s1 s2) (apply _ _ (apply _ _ (apply _ _ (write s1 s2) t1) t2) t4)) t3)\n\
               		      (apply _ _ (apply _ _ (read s1 s2) t1) t3)))))))))))\n\
\n\
; i == j if read( a, j ) != read( a[i] = b, j )\n\
(declare negativerow (! s1 sort\n\
                     (! s2 sort\n\
                     (! t2 (term s1)\n\
                     (! t3 (term s1)\n\
                     (! t1 (term (Array s1 s2))\n\
                     (! t4 (term s2)\n\
		     (! u (th_holds (not (= _\n\
                        (apply _ _ (apply _ _ (read s1 s2) (apply _ _ (apply _ _ (apply _ _ (write s1 s2) t1) t2) t4)) t3)\n\
                        (apply _ _ (apply _ _ (read s1 s2) t1) t3))))\n\
                     (th_holds (= _ t2 t3))))))))))\n\
\n\
(declare ext (! s1 sort\n\
             (! s2 sort\n\
             (! t1 (term (Array s1 s2))\n\
             (! t2 (term (Array s1 s2))\n\
             (! u1 (! k (term s1)\n\
                   (! u2 (th_holds (or (= _ t1 t2) (not (= _ (apply _ _ (apply _ _ (read s1 s2) t1) k) (apply _ _ (apply _ _ (read s1 s2) t2) k)))))\n\
                     (holds cln)))\n\
               (holds cln)))))))\n\
\n\
;;;; TEMPORARY:\n\
\n\
(declare trust-bad (th_holds false))\n\
\n\
; helper stuff\n\
\n\
(program mpz_ ((x mpz) (y mpz)) formula\n\
    (mp_ifzero (mpz_sub x y) true false))\n\
\n\
\n\
; \"bitvec\" is a term of type \"sort\"\n\
; (declare BitVec sort)\n\
(declare BitVec (!n mpz sort))\n\
\n\
; bit type\n\
(declare bit type)\n\
(declare b0 bit)\n\
(declare b1 bit)\n\
\n\
; bit vector type used for constants\n\
(declare bv type)\n\
(declare bvn bv)\n\
(declare bvc (! b bit (! v bv bv)))\n\
\n\
; calculate the length of a bitvector\n\
;; (program bv_len ((v bv)) mpz\n\
;;   (match v\n\
;;     (bvn 0)\n\
;;     ((bvc b v') (mp_add (bv_len v') 1))))\n\
\n\
\n\
; a bv constant term\n\
(declare a_bv\n\
	 (! n mpz\n\
	 (! v bv\n\
	    (term (BitVec n)))))\n\
\n\
(program bv_constants_are_disequal ((x bv) (y bv)) formula\n\
  (match x\n\
      (bvn (fail formula))\n\
      ((bvc bx x')\n\
        (match y\n\
          (bvn (fail formula))\n\
          ((bvc by y') (match bx\n\
                             (b0 (match by (b0 (bv_constants_are_disequal x' y')) (b1 (true))))\n\
                             (b1 (match by (b0 (true)) (b1 (bv_constants_are_disequal x' y'))))\n\
          ))\n\
      ))\n\
))\n\
\n\
(declare bv_disequal_constants\n\
	 (! n mpz\n\
	 (! x bv\n\
	 (! y bv\n\
	 (! c (^ (bv_constants_are_disequal x y) true)\n\
  	   (th_holds (not (= (BitVec n) (a_bv n x) (a_bv n y)))))))))\n\
\n\
; a bv variable\n\
(declare var_bv type)\n\
; a bv variable term\n\
(declare a_var_bv\n\
	 (! n mpz\n\
	 (! v var_bv\n\
	    (term (BitVec n)))))\n\
\n\
; bit vector binary operators\n\
(define bvop2\n\
	(! n mpz\n\
	(! x (term (BitVec n))\n\
        (! y (term (BitVec n))\n\
             	   (term (BitVec n))))))\n\
\n\
(declare bvand bvop2)\n\
(declare bvor bvop2)\n\
(declare bvor bvop2)\n\
(declare bvxor bvop2)\n\
(declare bvnand bvop2)\n\
(declare bvnor bvop2)\n\
(declare bvxnor bvop2)\n\
(declare bvmul bvop2)\n\
(declare bvadd bvop2)\n\
(declare bvsub bvop2)\n\
(declare bvudiv bvop2)\n\
(declare bvurem bvop2)\n\
(declare bvsdiv bvop2)\n\
(declare bvsrem bvop2)\n\
(declare bvsmod bvop2)\n\
(declare bvshl bvop2)\n\
(declare bvlshr bvop2)\n\
(declare bvashr bvop2)\n\
(declare concat bvop2)\n\
\n\
; bit vector unary operators\n\
(define bvop1\n\
	(! n mpz\n\
	(! x (term (BitVec n))\n\
             	   (term (BitVec n)))))\n\
\n\
\n\
(declare bvneg bvop1)\n\
(declare bvnot bvop1)\n\
(declare rotate_left  bvop1)\n\
(declare rotate_right bvop1)\n\
\n\
(declare bvcomp\n\
	 (! n mpz\n\
 	 (! t1 (term (BitVec n))\n\
	 (! t2 (term (BitVec n))\n\
	    (term (BitVec 1))))))\n\
\n\
\n\
(declare concat\n\
	 (! n mpz\n\
	 (! m mpz\n\
	 (! m' mpz\n\
	 (! t1 (term (BitVec m))\n\
	 (! t2 (term (BitVec m'))\n\
	    (term (BitVec n))))))))\n\
\n\
;; side-condition fails in signature only??\n\
;;	 (! s (^ (mp_add m m') n)\n\
\n\
;; (declare repeat bvopp)\n\
\n\
(declare extract\n\
	 (! n mpz\n\
	 (! i mpz\n\
	 (! j mpz\n\
	 (! m mpz\n\
	 (! t2 (term (BitVec m))\n\
	    (term (BitVec n))))))))\n\
\n\
(declare zero_extend\n\
	 (! n mpz\n\
	 (! i mpz\n\
	 (! m mpz\n\
	 (! t2 (term (BitVec m))\n\
	    (term (BitVec n)))))))\n\
\n\
(declare sign_extend\n\
	 (! n mpz\n\
	 (! i mpz\n\
	 (! m mpz\n\
	 (! t2 (term (BitVec m))\n\
	    (term (BitVec n)))))))\n\
\n\
(declare repeat\n\
	 (! n mpz\n\
	 (! i mpz\n\
	 (! m mpz\n\
	 (! t2 (term (BitVec m))\n\
	    (term (BitVec n)))))))\n\
\n\
\n\
\n\
;; TODO: add checks for valid typing for these operators\n\
;; (! c1 (^ (mpz_lte i j)\n\
;; (! c2 (^ (mpz_lt i n) true)\n\
;; (! c3 (^ (mp_ifneg i false true) true)\n\
;; (! c4 (^ (mp_ifneg j false true) true)\n\
;; (! s (^ (mp_add (mpz_sub i j) 1) m)\n\
\n\
\n\
; bit vector predicates\n\
(define bvpred\n\
	(! n mpz\n\
	(! x (term (BitVec n))\n\
	(! y (term (BitVec n))\n\
	           formula))))\n\
\n\
(declare bvult bvpred)\n\
(declare bvule bvpred)\n\
(declare bvugt bvpred)\n\
(declare bvuge bvpred)\n\
(declare bvslt bvpred)\n\
(declare bvsle bvpred)\n\
(declare bvsgt bvpred)\n\
(declare bvsge bvpred)\n\
\n\
; bit blasted terms as list of formulas\n\
(declare bblt type)\n\
(declare bbltn bblt)\n\
(declare bbltc (! f formula (! v bblt bblt)))\n\
\n\
; calculate the length of a bit-blasted term\n\
(program bblt_len ((v bblt)) mpz\n\
  (match v\n\
    (bbltn 0)\n\
    ((bbltc b v') (mp_add (bblt_len v') 1))))\n\
\n\
\n\
; (bblast_term x y) means term y corresponds to bit level interpretation x\n\
(declare bblast_term\n\
	 (! n mpz\n\
	 (! x (term (BitVec n))\n\
	 (! y bblt\n\
	    type))))\n\
\n\
; FIXME: for unsupported bit-blast terms\n\
(declare trust_bblast_term\n\
	 (! n mpz\n\
	 (! x (term (BitVec n))\n\
	 (! y bblt\n\
	    (bblast_term n x y)))))\n\
\n\
\n\
; Binds a symbol to the bblast_term to be used later on.\n\
(declare decl_bblast\n\
	 (! n mpz\n\
	 (! b bblt\n\
	 (! t (term (BitVec n))\n\
	 (! bb (bblast_term n t b)\n\
	 (! s (^ (bblt_len b) n)\n\
	 (! u (! v (bblast_term n t b) (holds cln))\n\
		   (holds cln))))))))\n\
\n\
(declare decl_bblast_with_alias\n\
	 (! n mpz\n\
	 (! b bblt\n\
	 (! t (term (BitVec n))\n\
	 (! a (term (BitVec n))\n\
	 (! bb (bblast_term n t b)\n\
	 (! e (th_holds (= _ t a))\n\
	 (! s (^ (bblt_len b) n)\n\
	 (! u (! v (bblast_term n a b) (holds cln))\n\
		   (holds cln))))))))))\n\
\n\
; a predicate to represent the n^th bit of a bitvector term\n\
(declare bitof\n\
	 (! x var_bv\n\
	 (! n mpz formula)))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;;\n\
;;           BITBLASTING RULES\n\
;;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST CONSTANT\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_const ((v bv) (n mpz)) bblt\n\
  (mp_ifneg n (match v (bvn bbltn)\n\
                       (default (fail bblt)))\n\
              (match v ((bvc b v') (bbltc (match b (b0 false) (b1 true)) (bblast_const v' (mp_add n (~ 1)))))\n\
                       (default (fail bblt)))))\n\
\n\
(declare bv_bbl_const (! n mpz\n\
                      (! f bblt\n\
                      (! v bv\n\
                      (! c (^ (bblast_const v (mp_add n (~ 1))) f)\n\
                           (bblast_term n (a_bv n v) f))))))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST VARIABLE\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_var ((x var_bv) (n mpz)) bblt\n\
  (mp_ifneg n bbltn\n\
              (bbltc (bitof x n) (bblast_var x (mp_add n (~ 1))))))\n\
\n\
(declare bv_bbl_var (! n mpz\n\
                    (! x var_bv\n\
                    (! f bblt\n\
                    (! c (^ (bblast_var x (mp_add n (~ 1))) f)\n\
                         (bblast_term n (a_var_bv n x) f))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST CONCAT\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_concat ((x bblt) (y bblt)) bblt\n\
  (match x\n\
    (bbltn (match y ((bbltc by y') (bbltc by (bblast_concat x y')))\n\
    	   	    (bbltn bbltn)))\n\
    ((bbltc bx x') (bbltc bx (bblast_concat x' y)))))\n\
\n\
(declare bv_bbl_concat (! n mpz\n\
	 	       (! m mpz\n\
		       (! m1 mpz\n\
                       (! x (term (BitVec m))\n\
		       (! y (term (BitVec m1))\n\
		       (! xb bblt\n\
		       (! yb bblt\n\
		       (! rb bblt\n\
		       (! xbb (bblast_term m x xb)\n\
		       (! ybb (bblast_term m1 y yb)\n\
                       (! c (^ (bblast_concat xb yb ) rb)\n\
                           (bblast_term n (concat n m m1 x y) rb)))))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST EXTRACT\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_extract_rec ((x bblt) (i mpz) (j mpz) (n mpz)) bblt\n\
  (match x\n\
    ((bbltc bx x') (mp_ifneg (mpz_sub (mpz_sub j n) 1)\n\
    	       	   	     (mp_ifneg (mpz_sub (mpz_sub n i) 1)\n\
			    	  	  (bbltc bx (bblast_extract_rec x' i j (mpz_sub n 1)))\n\
					  (bblast_extract_rec x' i j (mpz_sub n 1)))\n\
\n\
			     bbltn))\n\
   (bbltn bbltn)))\n\
\n\
(program bblast_extract ((x bblt) (i mpz) (j mpz) (n mpz)) bblt\n\
 (bblast_extract_rec x i j (mpz_sub n 1)))\n\
\n\
(declare bv_bbl_extract (! n mpz\n\
			(! i mpz\n\
			(! j mpz\n\
			(! m mpz\n\
                       	(! x (term (BitVec m))\n\
		       	(! xb bblt\n\
		       	(! rb bblt\n\
		       	(! xbb (bblast_term m x xb)\n\
			(! c ( ^ (bblast_extract xb i j m) rb)\n\
                           (bblast_term n (extract n i j m x) rb)))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST ZERO/SIGN EXTEND\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program extend_rec ((x bblt) (i mpz) (b formula)) bblt\n\
  (mp_ifneg i x\n\
  	    (bbltc b (extend_rec x (mpz_sub i 1) b)))))\n\
\n\
(program bblast_zextend ((x bblt) (i mpz)) bblt\n\
 (extend_rec x (mpz_sub i 1) false))\n\
\n\
(declare bv_bbl_zero_extend (! n mpz\n\
			(! k mpz\n\
			(! m mpz\n\
                       	(! x (term (BitVec m))\n\
		       	(! xb bblt\n\
		       	(! rb bblt\n\
		       	(! xbb (bblast_term m x xb)\n\
			(! c ( ^ (bblast_zextend xb k m) rb)\n\
                           (bblast_term n (zero_extend n k m x) rb))))))))))\n\
\n\
(program bblast_sextend ((x bblt) (i mpz)) bblt\n\
 (match x (bbltn (fail bblt))\n\
 	  ((bbltc xb x') (extend_rec x (mpz_sub i 1) xb))))\n\
\n\
(declare bv_bbl_sign_extend (! n mpz\n\
			(! k mpz\n\
			(! m mpz\n\
                       	(! x (term (BitVec m))\n\
		       	(! xb bblt\n\
		       	(! rb bblt\n\
		       	(! xbb (bblast_term m x xb)\n\
			(! c ( ^ (bblast_sextend xb k) rb)\n\
                           (bblast_term n (sign_extend n k m x) rb))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVAND\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_bvand ((x bblt) (y bblt)) bblt\n\
  (match x\n\
    (bbltn (match y (bbltn bbltn) (default (fail bblt))))\n\
    ((bbltc bx x') (match y\n\
                      (bbltn (fail bblt))\n\
                      ((bbltc by y') (bbltc (and bx by) (bblast_bvand x' y')))))))\n\
\n\
(declare bv_bbl_bvand (! n mpz\n\
                      (! x (term (BitVec n))\n\
		      (! y (term (BitVec n))\n\
		      (! xb bblt\n\
		      (! yb bblt\n\
		      (! rb bblt\n\
		      (! xbb (bblast_term n x xb)\n\
		      (! ybb (bblast_term n y yb)\n\
                      (! c (^ (bblast_bvand xb yb ) rb)\n\
                           (bblast_term n (bvand n x y) rb)))))))))))\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVNOT\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_bvnot ((x bblt)) bblt\n\
  (match x\n\
    (bbltn bbltn)\n\
    ((bbltc bx x') (bbltc (not bx) (bblast_bvnot x')))))\n\
\n\
(declare bv_bbl_bvnot (! n mpz\n\
                      (! x (term (BitVec n))\n\
		      (! xb bblt\n\
		      (! rb bblt\n\
		      (! xbb (bblast_term n x xb)\n\
                      (! c (^ (bblast_bvnot xb ) rb)\n\
                           (bblast_term n (bvnot n x) rb))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVOR\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_bvor ((x bblt) (y bblt)) bblt\n\
  (match x\n\
    (bbltn (match y (bbltn bbltn) (default (fail bblt))))\n\
    ((bbltc bx x') (match y\n\
                      (bbltn (fail bblt))\n\
                      ((bbltc by y') (bbltc (or bx by) (bblast_bvor x' y')))))))\n\
\n\
(declare bv_bbl_bvor (! n mpz\n\
                      (! x (term (BitVec n))\n\
		      (! y (term (BitVec n))\n\
		      (! xb bblt\n\
		      (! yb bblt\n\
		      (! rb bblt\n\
		      (! xbb (bblast_term n x xb)\n\
		      (! ybb (bblast_term n y yb)\n\
                      (! c (^ (bblast_bvor xb yb ) rb)\n\
                           (bblast_term n (bvor n x y) rb)))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVXOR\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_bvxor ((x bblt) (y bblt)) bblt\n\
  (match x\n\
    (bbltn (match y (bbltn bbltn) (default (fail bblt))))\n\
    ((bbltc bx x') (match y\n\
                      (bbltn (fail bblt))\n\
                      ((bbltc by y') (bbltc (xor bx by) (bblast_bvxor x' y')))))))\n\
\n\
(declare bv_bbl_bvxor (! n mpz\n\
                      (! x (term (BitVec n))\n\
		      (! y (term (BitVec n))\n\
		      (! xb bblt\n\
		      (! yb bblt\n\
		      (! rb bblt\n\
		      (! xbb (bblast_term n x xb)\n\
		      (! ybb (bblast_term n y yb)\n\
                      (! c (^ (bblast_bvxor xb yb ) rb)\n\
                           (bblast_term n (bvxor n x y) rb)))))))))))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVADD\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
;; return the carry bit after adding x y\n\
;; FIXME: not the most efficient thing in the world\n\
(program bblast_bvadd_carry ((a bblt) (b bblt) (carry formula)) formula\n\
(match a\n\
  ( bbltn (match b (bbltn carry) (default (fail formula))))\n\
  ((bbltc ai a') (match b\n\
  	     	   (bbltn (fail formula))\n\
	 	   ((bbltc bi b') (or (and ai bi) (and (xor ai bi) (bblast_bvadd_carry a' b' carry))))))))\n\
\n\
;; ripple carry adder where carry is the initial carry bit\n\
(program bblast_bvadd ((a bblt) (b bblt) (carry formula)) bblt\n\
(match a\n\
  ( bbltn (match b (bbltn bbltn) (default (fail bblt))))\n\
  ((bbltc ai a') (match b\n\
  	     	   (bbltn (fail bblt))\n\
	 	   ((bbltc bi b') (bbltc (xor (xor ai bi) (bblast_bvadd_carry a' b' carry))\n\
				  	 (bblast_bvadd a' b' carry)))))))\n\
\n\
\n\
(program reverse_help ((x bblt) (acc bblt)) bblt\n\
(match x\n\
       (bbltn acc)\n\
       ((bbltc xi x') (reverse_help x' (bbltc xi acc)))))\n\
\n\
\n\
(program reverseb ((x bblt)) bblt\n\
	 (reverse_help x bbltn))\n\
\n\
\n\
; AJR: use this version?\n\
;(program bblast_bvadd_2h ((a bblt) (b bblt) (carry formula)) bblt\n\
;(match a\n\
;  ( bbltn (match b (bbltn bbltn) (default (fail bblt))))\n\
;  ((bbltc ai a') (match b\n\
;       (bbltn (fail bblt))\n\
;	 	   ((bbltc bi b')\n\
;	 	     (let carry' (or (and ai bi) (and (xor ai bi) carry))\n\
;	 	     (bbltc (xor (xor ai bi) carry)\n\
;				  	    (bblast_bvadd_2h a' b' carry'))))))))\n\
\n\
;(program bblast_bvadd_2 ((a bblt) (b bblt) (carry formula)) bblt\n\
;(let ar (reverseb a) ;; reverse a and b so that we can build the circuit\n\
;(let br (reverseb b) ;; from the least significant bit up\n\
;(let ret (bblast_bvadd_2h ar br carry)\n\
;  (reverseb ret)))))\n\
\n\
(declare bv_bbl_bvadd (! n mpz\n\
                      (! x (term (BitVec n))\n\
		      (! y (term (BitVec n))\n\
		      (! xb bblt\n\
		      (! yb bblt\n\
		      (! rb bblt\n\
		      (! xbb (bblast_term n x xb)\n\
		      (! ybb (bblast_term n y yb)\n\
                      (! c (^ (bblast_bvadd xb yb false) rb)\n\
                           (bblast_term n (bvadd n x y) rb)))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVNEG\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_zero ((n mpz)) bblt\n\
(mp_ifzero n bbltn\n\
	     (bbltc false (bblast_zero (mp_add n (~1))))))\n\
\n\
(program bblast_bvneg ((x bblt) (n mpz)) bblt\n\
  (bblast_bvadd (bblast_bvnot x) (bblast_zero n) true))\n\
\n\
\n\
(declare bv_bbl_bvneg (! n mpz\n\
                      (! x (term (BitVec n))\n\
		      (! xb bblt\n\
		      (! rb bblt\n\
		      (! xbb (bblast_term n x xb)\n\
                      (! c (^ (bblast_bvneg xb n) rb)\n\
                           (bblast_term n (bvneg n x) rb))))))))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVMUL\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
\n\
;; shift add multiplier\n\
\n\
;; (program concat ((a bblt) (b bblt)) bblt\n\
;;   (match a (bbltn b)\n\
;;   	   ((bbltc ai a') (bbltc ai (concat a' b)))))\n\
\n\
\n\
(program top_k_bits ((a bblt) (k mpz)) bblt\n\
  (mp_ifzero k bbltn\n\
  	     (match a (bbltn (fail bblt))\n\
	     	      ((bbltc ai a') (bbltc ai (top_k_bits a' (mpz_sub k 1)))))))\n\
\n\
(program bottom_k_bits ((a bblt) (k mpz)) bblt\n\
 (reverseb (top_k_bits (reverseb a) k)))\n\
\n\
;; assumes the least signigicant bit is at the beginning of the list\n\
(program k_bit ((a bblt) (k mpz)) formula\n\
(mp_ifneg k (fail formula)\n\
(match a (bbltn (fail formula))\n\
         ((bbltc ai a') (mp_ifzero k ai (k_bit a' (mpz_sub k 1)))))))\n\
\n\
(program and_with_bit ((a bblt) (bt formula)) bblt\n\
(match a (bbltn bbltn)\n\
         ((bbltc ai a') (bbltc (and bt ai) (and_with_bit a' bt)))))\n\
\n\
;; a is going to be the current result\n\
;; carry is going to be false initially\n\
;; b is the and of a and b[k]\n\
;; res is going to be bbltn initially\n\
(program mult_step_k_h ((a bblt) (b bblt) (res bblt) (carry formula) (k mpz)) bblt\n\
(match a\n\
  (bbltn (match b (bbltn res) (default (fail bblt))))\n\
  ((bbltc ai a')\n\
    (match b (bbltn (fail bblt))\n\
             ((bbltc bi b')\n\
	     (mp_ifneg (mpz_sub k 1)\n\
	     	         (let carry_out (or (and ai bi) (and (xor ai bi) carry))\n\
			 (let curr (xor (xor ai bi) carry)\n\
			    (mult_step_k_h a' b' (bbltc curr res) carry_out (mpz_sub k 1))))\n\
			 (mult_step_k_h a' b (bbltc ai res) carry (mpz_sub k 1))\n\
))))))\n\
\n\
;; assumes that a, b and res have already been reversed\n\
(program mult_step ((a bblt) (b bblt) (res bblt) (n mpz) (k mpz)) bblt\n\
(let k' (mpz_sub n k )\n\
(let ak (top_k_bits a k')\n\
(let b' (and_with_bit ak (k_bit b k))\n\
 (mp_ifzero (mpz_sub k' 1)\n\
   (mult_step_k_h res b' bbltn false k)\n\
   (let res' (mult_step_k_h res b' bbltn false k)\n\
   (mult_step a b (reverseb res') n (mp_add k 1))))))))\n\
\n\
\n\
(program bblast_bvmul ((a bblt) (b bblt) (n mpz)) bblt\n\
(let ar (reverseb a) ;; reverse a and b so that we can build the circuit\n\
(let br (reverseb b) ;; from the least significant bit up\n\
(let res (and_with_bit ar (k_bit br 0))\n\
     (mp_ifzero (mpz_sub n 1)     ;; if multiplying 1 bit numbers no need to call mult_step\n\
     		res\n\
		(mult_step ar br res n 1))))))\n\
\n\
(declare bv_bbl_bvmul (! n mpz\n\
                      (! x (term (BitVec n))\n\
		      (! y (term (BitVec n))\n\
		      (! xb bblt\n\
		      (! yb bblt\n\
		      (! rb bblt\n\
		      (! xbb (bblast_term n x xb)\n\
		      (! ybb (bblast_term n y yb)\n\
                      (! c (^ (bblast_bvmul xb yb n) rb)\n\
                           (bblast_term n (bvmul n x y) rb)))))))))))\n\
\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST EQUALS\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
; bit blast  x = y\n\
; for x,y of size n, it will return a conjunction (x.0 = y.0 ^ ( ... ^ (x.{n-1} = y.{n-1})))\n\
; f is the accumulator formula that builds the equality in the right order\n\
(program bblast_eq_rec ((x bblt) (y bblt) (f formula)) formula\n\
  (match x\n\
    (bbltn (match y (bbltn f) (default (fail formula))))\n\
    ((bbltc fx x') (match y\n\
                      (bbltn (fail formula))\n\
                      ((bbltc fy y') (bblast_eq_rec x' y' (and (iff fx fy) f)))))\n\
    (default (fail formula))))\n\
\n\
(program bblast_eq ((x bblt) (y bblt)) formula\n\
	 (match x\n\
	 	((bbltc bx x') (match y ((bbltc by y') (bblast_eq_rec x' y' (iff bx by)))\n\
			       	      	(default (fail formula))))\n\
		(default (fail formula))))\n\
\n\
\n\
;; TODO: a temporary bypass for rewrites that we don't support yet. As soon\n\
;; as we do, remove this rule.\n\
\n\
(declare bv_bbl_=_false\n\
	 (! n mpz\n\
	 (! x (term (BitVec n))\n\
         (! y (term (BitVec n))\n\
         (! bx bblt\n\
         (! by bblt\n\
         (! f formula\n\
         (! bbx (bblast_term n x bx)\n\
         (! bby (bblast_term n y by)\n\
         (! c (^ (bblast_eq bx by) f)\n\
            (th_holds (iff (= (BitVec n) x y) false))))))))))))\n\
\n\
(declare bv_bbl_=\n\
	 (! n mpz\n\
	 (! x (term (BitVec n))\n\
         (! y (term (BitVec n))\n\
         (! bx bblt\n\
         (! by bblt\n\
         (! f formula\n\
         (! bbx (bblast_term n x bx)\n\
         (! bby (bblast_term n y by)\n\
         (! c (^ (bblast_eq bx by) f)\n\
            (th_holds (iff (= (BitVec n) x y) f))))))))))))\n\
\n\
(declare bv_bbl_=_swap\n\
	 (! n mpz\n\
	 (! x (term (BitVec n))\n\
         (! y (term (BitVec n))\n\
         (! bx bblt\n\
         (! by bblt\n\
         (! f formula\n\
         (! bbx (bblast_term n x bx)\n\
         (! bby (bblast_term n y by)\n\
         (! c (^ (bblast_eq by bx) f)\n\
            (th_holds (iff (= (BitVec n) x y) f))))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVULT\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_bvult ((x bblt) (y bblt) (n mpz)) formula\n\
(match x\n\
  ( bbltn (fail formula))\n\
  ((bbltc xi x') (match y\n\
  	     	   (bbltn (fail formula))\n\
	 	   ((bbltc yi y') (mp_ifzero n\n\
		                    (and (not xi) yi)\n\
				    (or (and (iff xi yi) (bblast_bvult x' y' (mp_add n (~1)))) (and (not xi) yi))))))))\n\
\n\
(declare bv_bbl_bvult\n\
	 (! n mpz\n\
	 (! x (term (BitVec n))\n\
         (! y (term (BitVec n))\n\
         (! bx bblt\n\
         (! by bblt\n\
         (! f formula\n\
         (! bbx (bblast_term n x bx)\n\
         (! bby (bblast_term n y by)\n\
         (! c (^ (bblast_bvult bx by (mp_add n (~1))) f)\n\
            (th_holds (iff (bvult n x y) f))))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVSLT\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_bvslt ((x bblt) (y bblt) (n mpz)) formula\n\
(match x\n\
  ( bbltn (fail formula))\n\
  ((bbltc xi x') (match y\n\
  	     	   (bbltn (fail formula))\n\
	 	   ((bbltc yi y') (mp_ifzero (mpz_sub n 1)\n\
		   	      	  	     (and xi (not yi))\n\
		   	      		     (or (and (iff xi yi)\n\
					     	      (bblast_bvult x' y' (mpz_sub n 2)))\n\
					     	 (and xi (not yi)))))))))\n\
\n\
(declare bv_bbl_bvslt\n\
	 (! n mpz\n\
	 (! x (term (BitVec n))\n\
         (! y (term (BitVec n))\n\
         (! bx bblt\n\
         (! by bblt\n\
         (! f formula\n\
         (! bbx (bblast_term n x bx)\n\
         (! bby (bblast_term n y by)\n\
         (! c (^ (bblast_bvslt bx by n) f)\n\
            (th_holds (iff (bvslt n x y) f))))))))))))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;; BITBLAST BVCOMP\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
(program bblast_bvcomp ((x bblt) (y bblt) (n mpz)) bblt\n\
  (match x ((bbltc bx x') (match y ((bbltc by y')\n\
  	   	                      (bbltc (bblast_eq_rec x' y' (iff bx by)) bbltn))\n\
                                   (default (fail bblt))))\n\
           (default (fail bblt))\n\
	   ))\n\
\n\
(declare bv_bbl_bvcomp (! n mpz\n\
                       (! x (term (BitVec n))\n\
		       (! y (term (BitVec n))\n\
		       (! xb bblt\n\
		       (! yb bblt\n\
		       (! rb bblt\n\
		       (! xbb (bblast_term n x xb)\n\
		       (! ybb (bblast_term n y yb)\n\
                       (! c (^ (bblast_bvcomp xb yb n) rb)\n\
                              (bblast_term 1 (bvcomp n x y) rb)))))))))))\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;;\n\
;;           BITBLASTING CONNECTORS\n\
;;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
\n\
; bit-blasting connections\n\
\n\
(declare intro_assump_t\n\
	 (! f formula\n\
	 (! v var\n\
	 (! C clause\n\
	 (! h (th_holds f)\n\
	 (! a (atom v f)\n\
	 (! u (! unit (holds (clc (pos v) cln))\n\
	      	 (holds C))\n\
	 (holds C))))))))\n\
\n\
(declare intro_assump_f\n\
	 (! f formula\n\
	 (! v var\n\
	 (! C clause\n\
	 (! h (th_holds (not f))\n\
	 (! a (atom v f)\n\
	 (! u (! unit (holds (clc (neg v) cln))\n\
	      	 (holds C))\n\
	 (holds C))))))))\n\
\n\
\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
;;\n\
;;           REWRITE RULES\n\
;;\n\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\
\n\
\n\
; rewrite rule :\n\
; x + y = y + x\n\
(declare bvadd_symm\n\
	 (! n mpz\n\
	 (! x (term (BitVec n))\n\
	 (! y (term (BitVec n))\n\
	    (th_holds (= (BitVec n) (bvadd _ x y) (bvadd _ y x)))))))\n\
\n\
;; (declare bvcrazy_rewrite\n\
;; 	 (! n mpz\n\
;; 	 (! x (term (BitVec n))\n\
;; 	 (! y (term (BitVec n))\n\
;; 	 (! xn bv_poly\n\
;; 	 (! yn bv_poly\n\
;; 	 (! hxn (bv_normalizes x xn)\n\
;; 	 (! hyn (bv_normalizes y yn)\n\
;; 	 (! s (^ (rewrite_scc xn yn) true)\n\
;; 	 (! u (! x (term (BitVec n)) (holds cln))\n\
;; 	     (holds cln)))))))))))\n\
\n\
;; 	    (th_holds (= (BitVec n) (bvadd x y) (bvadd y x)))))))\n\
\n\
\n\
\n\
; necessary?\n\
;; (program calc_bvand ((a bv) (b bv)) bv\n\
;;   (match a\n\
;;     (bvn (match b (bvn bvn) (default (fail bv))))\n\
;;     ((bvc ba a') (match b\n\
;;                       ((bvc bb b') (bvc (match ba (b0 b0) (b1 bb)) (calc_bvand a' b')))\n\
;;                       (default (fail bv))))))\n\
\n\
;; ; rewrite rule (w constants) :\n\
;; ; a & b = c\n\
;; (declare bvand_const (! c bv\n\
;; 		     (! a bv\n\
;;                      (! b bv\n\
;;                      (! u (^ (calc_bvand a b) c)\n\
;;                         (th_holds (= BitVec (bvand (a_bv a) (a_bv b)) (a_bv c))))))))\n\
\n\
\n\
;; making constant bit-vectors\n\
(program mk_ones ((n mpz)) bv\n\
	(mp_ifzero n bvn (bvc b1 (mk_ones (mpz_sub n 1)))))\n\
\n\
(program mk_zero ((n mpz)) bv\n\
	(mp_ifzero n bvn (bvc b0 (mk_ones (mpz_sub n 1)))))\n\
\n\
\n\
\n\
;; (bvxnor a b) => (bvnot (bvxor a b))\n\
;; (declare bvxnor_elim\n\
;; 	 (! n mpz\n\
;; 	 (! a (term (BitVec n))\n\
;; 	 (! b (term (BitVec n))\n\
;; 	 (! a' (term (BitVec n))\n\
;; 	 (! b' (term (BitVec n))\n\
;; 	 (! rwa (rw_term _ a a')\n\
;; 	 (! rwb (rw_term _ b b')\n\
;; 	 (rw_term n (bvxnor _ a b)\n\
;; 	 	  (bvnot _ (bvxor _ a' b')))))))))))\n\
\n\
\n\
\n\
;; ;; (bvxor a 0) => a\n\
;; (declare bvxor_zero\n\
;; 	 (! n mpz\n\
;; 	 (! zero_bits bv\n\
;; 	 (! sc (^ (mk_zero n)  zero_bits)\n\
;; 	 (! a (term (BitVec n))\n\
;; 	 (! b (term (BitVec n))\n\
;; 	 (! a' (term (BitVec n))\n\
;; 	 (! rwa (rw_term _  a a')\n\
;; 	 (! rwb (rw_term _ b (a_bv _ zero_bits))\n\
;; 	 (rw_term _  (bvxor _ a b)\n\
;; 	 	  a'))))))))))\n\
\n\
;; ;; (bvxor a 11) => (bvnot a)\n\
;; (declare bvxor_one\n\
;; 	 (! n mpz\n\
;; 	 (! one_bits bv\n\
;; 	 (! sc (^ (mk_ones n)  one_bits)\n\
;; 	 (! a (term (BitVec n))\n\
;; 	 (! b (term (BitVec n))\n\
;; 	 (! a' (term (BitVec n))\n\
;; 	 (! rwa (rw_term _  a a')\n\
;; 	 (! rwb (rw_term _  b (a_bv _ one_bits))\n\
;; 	 (rw_term _ (bvxor _ a b)\n\
;; 	 	  (bvnot _ a')))))))))))\n\
\n\
\n\
;; ;; (bvnot (bvnot a)) => a\n\
;; (declare bvnot_idemp\n\
;; 	 (! n mpz\n\
;; 	 (! a (term (BitVec n))\n\
;; 	 (! a' (term (BitVec n))\n\
;; 	 (! rwa (rw_term _  a a')\n\
;; 	 (rw_term _ (bvnot _ (bvnot _ a))\n\
;; 	 	  a'))))))\n\
\n\
;\n\
; Equality swap\n\
;\n\
\n\
(declare rr_bv_eq\n\
	 (! n mpz\n\
	 (! t1 (term (BitVec n))\n\
 	 (! t2 (term (BitVec n))\n\
	     (th_holds (iff (= (BitVec n) t2 t1) (= (BitVec n) t1 t2)))))))\n\
\n\
;\n\
; Additional rules...\n\
;\n\
\n\
;\n\
; Default, if nothing else applied\n\
;\n\
\n\
(declare rr_bv_default\n\
	 (! t1 formula\n\
 	 (! t2 formula\n\
	     (th_holds (iff t1 t2))))))\n\
\n\
; Depends On: th_smt.plf\n\
(declare Real sort)\n\
\n\
(define arithpred_Real (! x (term Real)\n\
                       (! y (term Real)\n\
                         formula)))\n\
\n\
(declare >_Real arithpred_Real)\n\
(declare >=_Real arithpred_Real)\n\
(declare <_Real  arithpred_Real)\n\
(declare <=_Real arithpred_Real)\n\
\n\
(define arithterm_Real (! x (term Real)\n\
                       (! y (term Real)\n\
                         (term Real))))\n\
\n\
(declare +_Real arithterm_Real)\n\
(declare -_Real arithterm_Real)\n\
(declare *_Real arithterm_Real)  ; is * ok to use?\n\
(declare /_Real arithterm_Real)  ; is / ok to use?\n\
\n\
; a constant term\n\
(declare a_real (! x mpq (term Real)))\n\
\n\
(declare >=0_Real (! x (term Real) formula))\n\
(declare =0_Real (! x (term Real) formula))\n\
(declare >0_Real (! x (term Real) formula))\n\
(declare distinct0_Real (! x (term Real) formula))\n\
\n\
; unary negation\n\
(declare u-_Real (! t (term Real) (term Real)))\n\
\n\
(declare Int sort)\n\
\n\
(define arithpred_Int (! x (term Int)\n\
                      (! y (term Int)\n\
                        formula)))\n\
\n\
(declare >_Int arithpred_Int)\n\
(declare >=_Int arithpred_Int)\n\
(declare <_Int  arithpred_Int)\n\
(declare <=_Int arithpred_Int)\n\
\n\
(define arithterm_Int (! x (term Int)\n\
		      (! y (term Int)\n\
		        (term Int))))\n\
\n\
(declare +_Int arithterm_Int)\n\
(declare -_Int arithterm_Int)\n\
(declare *_Int arithterm_Int)  ; is * ok to use?\n\
(declare /_Int arithterm_Int)  ; is / ok to use?\n\
\n\
; a constant term\n\
(declare a_int (! x mpz (term Int)))\n\
\n\
; unary negation\n\
(declare u-_Int (! t (term Int) (term Int)))\n\
\n\
; Depends on th_real.plf, smt.plf, sat.plf\n\
\n\
; LRA proofs have the following interface:\n\
;    * Given predicates between real terms\n\
;    * Prove bottom\n\
;\n\
; However, even though the type of the interface does not express this,\n\
; the predicates are **linear bounds**, not arbitrary real bounds. Thus\n\
; LRA proofs have the following structure:\n\
;\n\
;    1. Prove that the input predicates are equivalent to a set of linear\n\
;       bounds.\n\
;    2. Use the linear bounds to prove bottom using farkas coefficients.\n\
;\n\
; Notice that the distinction between linear bounds (associated in the signature\n\
; with the string \"poly\") and real predicates (which relate \"term Real\"s to one\n\
; another) matters quite a bit. We have certain kinds of axioms for one, and\n\
; other axioms for the other.\n\
\n\
(program mpq_ifpos ((x mpq)) bool\n\
  (mp_ifneg x ff (mp_ifzero x ff tt)))\n\
\n\
; a real variable\n\
(declare var_real type)\n\
; a real variable term\n\
(declare a_var_real (! v var_real (term Real)))\n\
\n\
;; linear polynomials in the form a_1*x_1 + a_2*x_2 .... + a_n*x_n\n\
\n\
(declare lmon type)\n\
(declare lmonn lmon)\n\
(declare lmonc (! c mpq (! v var_real (! l lmon lmon))))\n\
\n\
(program lmon_neg ((l lmon)) lmon\n\
  (match l\n\
    (lmonn l)\n\
    ((lmonc c' v' l') (lmonc (mp_neg c') v' (lmon_neg l')))))\n\
\n\
(program lmon_add ((l1 lmon) (l2 lmon)) lmon\n\
  (match l1\n\
    (lmonn l2)\n\
    ((lmonc c' v' l')\n\
      (match l2\n\
        (lmonn l1)\n\
        ((lmonc c'' v'' l'')\n\
          (compare v' v''\n\
            (lmonc c' v' (lmon_add l' l2))\n\
            (lmonc c'' v'' (lmon_add l1 l''))))))))\n\
\n\
(program lmon_mul_c ((l lmon) (c mpq)) lmon\n\
  (match l\n\
    (lmonn l)\n\
    ((lmonc c' v' l') (lmonc (mp_mul c c') v' (lmon_mul_c l' c)))))\n\
\n\
;; linear polynomials in the form (a_1*x_1 + a_2*x_2 .... + a_n*x_n) + c\n\
\n\
(declare poly type)\n\
(declare polyc (! c mpq (! l lmon poly)))\n\
\n\
(program poly_neg ((p poly)) poly\n\
  (match p\n\
    ((polyc m' p') (polyc (mp_neg m') (lmon_neg p')))))\n\
\n\
(program poly_add ((p1 poly) (p2 poly)) poly\n\
  (match p1\n\
    ((polyc c1 l1)\n\
      (match p2\n\
        ((polyc c2 l2) (polyc (mp_add c1 c2) (lmon_add l1 l2)))))))\n\
\n\
(program poly_sub ((p1 poly) (p2 poly)) poly\n\
  (poly_add p1 (poly_neg p2)))\n\
\n\
(program poly_mul_c ((p poly) (c mpq)) poly\n\
  (match p\n\
    ((polyc c' l') (polyc (mp_mul c' c) (lmon_mul_c l' c)))))\n\
\n\
;; code to isolate a variable from a term\n\
;; if (isolate v l) returns (c,l'), this means l = c*v + l', where v is not in FV(t').\n\
\n\
(declare isol type)\n\
(declare isolc (! r mpq (! l lmon isol)))\n\
\n\
(program isolate_h ((v var_real) (l lmon) (e bool)) isol\n\
  (match l\n\
    (lmonn (isolc 0/1 l))\n\
    ((lmonc c' v' l')\n\
      (ifmarked v'\n\
        (match (isolate_h v l' tt)\n\
          ((isolc ci li) (isolc (mp_add c' ci) li)))\n\
        (match e\n\
          (tt (isolc 0/1 l))\n\
          (ff (match (isolate_h v l' ff)\n\
                ((isolc ci li) (isolc ci (lmonc c' v' li))))))))))\n\
\n\
(program isolate ((v var_real) (l lmon)) isol\n\
  (do (markvar v)\n\
  (let i (isolate_h v l ff)\n\
  (do (markvar v) i))))\n\
\n\
;; determine if a monomial list is constant\n\
\n\
(program is_lmon_zero ((l lmon)) bool\n\
  (match l\n\
    (lmonn tt)\n\
    ((lmonc c v l')\n\
      (match (isolate v l)\n\
        ((isolc ci li)\n\
          (mp_ifzero ci (is_lmon_zero li) ff))))))\n\
\n\
;; return the constant that p is equal to.  If p is not constant, fail.\n\
\n\
(program is_poly_const ((p poly)) mpq\n\
  (match p\n\
    ((polyc c' l')\n\
      (match (is_lmon_zero l')\n\
        (tt c')\n\
        (ff (fail mpq))))))\n\
\n\
;; conversion to use polynomials in term formulas\n\
\n\
\n\
(declare >=0_poly (! x poly formula))\n\
(declare =0_poly (! x poly formula))\n\
(declare >0_poly (! x poly formula))\n\
(declare distinct0_poly (! x poly formula))\n\
\n\
;; create new equality out of inequality\n\
\n\
(declare lra_>=_>=_to_=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! f1 (th_holds (>=0_poly p1))\n\
  (! f2 (th_holds (>=0_poly p2))\n\
  (! i2 (^ (mp_ifzero (is_poly_const (poly_add p1 p2)) tt ff) tt)\n\
    (th_holds (=0_poly p2))))))))\n\
\n\
;; axioms\n\
\n\
(declare lra_axiom_=\n\
   (th_holds (=0_poly (polyc 0/1 lmonn))))\n\
\n\
(declare lra_axiom_>\n\
  (! c mpq\n\
  (! i (^ (mpq_ifpos c) tt)\n\
    (th_holds (>0_poly (polyc c lmonn))))))\n\
\n\
(declare lra_axiom_>=\n\
  (! c mpq\n\
  (! i (^ (mp_ifneg c tt ff) ff)\n\
    (th_holds (>=0_poly (polyc c lmonn))))))\n\
\n\
(declare lra_axiom_distinct\n\
  (! c mpq\n\
  (! i (^ (mp_ifzero c tt ff) ff)\n\
    (th_holds (distinct0_poly (polyc c lmonn))))))\n\
\n\
;; contradiction rules\n\
\n\
(declare lra_contra_=\n\
  (! p poly\n\
  (! f (th_holds (=0_poly p))\n\
  (! i (^ (mp_ifzero (is_poly_const p) tt ff) ff)\n\
    (holds cln)))))\n\
\n\
(declare lra_contra_>\n\
  (! p poly\n\
  (! f (th_holds (>0_poly p))\n\
  (! i2 (^ (mpq_ifpos (is_poly_const p)) ff)\n\
    (holds cln)))))\n\
\n\
(declare lra_contra_>=\n\
  (! p poly\n\
  (! f (th_holds (>=0_poly p))\n\
  (! i2 (^ (mp_ifneg (is_poly_const p) tt ff) tt)\n\
    (holds cln)))))\n\
\n\
(declare lra_contra_distinct\n\
  (! p poly\n\
  (! f (th_holds (distinct0_poly p))\n\
  (! i2 (^ (mp_ifzero (is_poly_const p) tt ff) tt)\n\
    (holds cln)))))\n\
\n\
;; muliplication by a constant\n\
\n\
(declare lra_mul_c_=\n\
  (! p poly\n\
  (! p' poly\n\
  (! c mpq\n\
  (! f (th_holds (=0_poly p))\n\
  (! i (^ (poly_mul_c p c) p')\n\
    (th_holds (=0_poly p'))))))))\n\
\n\
(declare lra_mul_c_>\n\
  (! p poly\n\
  (! p' poly\n\
  (! c mpq\n\
  (! f (th_holds (>0_poly p))\n\
  (! i (^ (mp_ifneg c (fail poly) (mp_ifzero c (fail poly) (poly_mul_c p c))) p')\n\
    (th_holds (>0_poly p'))))))));\n\
\n\
(declare lra_mul_c_>=\n\
  (! p poly\n\
  (! p' poly\n\
  (! c mpq\n\
  (! f (th_holds (>=0_poly p))\n\
  (! i (^ (mp_ifneg c (fail poly) (poly_mul_c p c)) p')\n\
    (th_holds (>=0_poly p'))))))))\n\
\n\
(declare lra_mul_c_distinct\n\
  (! p poly\n\
  (! p' poly\n\
  (! c mpq\n\
  (! f (th_holds (distinct0_poly p))\n\
  (! i (^ (mp_ifzero c (fail poly) (poly_mul_c p c)) p')\n\
    (th_holds (distinct0_poly p'))))))))\n\
\n\
;; adding equations\n\
\n\
(declare lra_add_=_=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (=0_poly p1))\n\
  (! f2 (th_holds (=0_poly p2))\n\
  (! i (^ (poly_add p1 p2) p3)\n\
    (th_holds (=0_poly p3)))))))))\n\
\n\
(declare lra_add_>_>\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (>0_poly p1))\n\
  (! f2 (th_holds (>0_poly p2))\n\
  (! i (^ (poly_add p1 p2) p3)\n\
    (th_holds (>0_poly p3)))))))))\n\
\n\
(declare lra_add_>=_>=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (>=0_poly p1))\n\
  (! f2 (th_holds (>=0_poly p2))\n\
  (! i (^ (poly_add p1 p2) p3)\n\
    (th_holds (>=0_poly p3)))))))))\n\
\n\
(declare lra_add_=_>\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (=0_poly p1))\n\
  (! f2 (th_holds (>0_poly p2))\n\
  (! i (^ (poly_add p1 p2) p3)\n\
    (th_holds (>0_poly p3)))))))))\n\
\n\
(declare lra_add_=_>=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (=0_poly p1))\n\
  (! f2 (th_holds (>=0_poly p2))\n\
  (! i (^ (poly_add p1 p2) p3)\n\
    (th_holds (>=0_poly p3)))))))))\n\
\n\
(declare lra_add_>_>=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (>0_poly p1))\n\
  (! f2 (th_holds (>=0_poly p2))\n\
  (! i (^ (poly_add p1 p2) p3)\n\
    (th_holds (>0_poly p3)))))))))\n\
\n\
(declare lra_add_>=_>\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (>=0_poly p1))\n\
  (! f2 (th_holds (>0_poly p2))\n\
  (! i (^ (poly_add p1 p2) p3)\n\
    (th_holds (>0_poly p3)))))))))\n\
\n\
(declare lra_add_=_distinct\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (=0_poly p1))\n\
  (! f2 (th_holds (distinct0_poly p2))\n\
  (! i (^ (poly_add p1 p2) p3)\n\
    (th_holds (distinct0_poly p3)))))))))\n\
\n\
;; substracting equations\n\
\n\
(declare lra_sub_=_=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (=0_poly p1))\n\
  (! f2 (th_holds (=0_poly p2))\n\
  (! i (^ (poly_sub p1 p2) p3)\n\
    (th_holds (=0_poly p3)))))))))\n\
\n\
(declare lra_sub_>_=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (>0_poly p1))\n\
  (! f2 (th_holds (=0_poly p2))\n\
  (! i (^ (poly_sub p1 p2) p3)\n\
    (th_holds (>0_poly p3)))))))))\n\
\n\
(declare lra_sub_>=_=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (>=0_poly p1))\n\
  (! f2 (th_holds (=0_poly p2))\n\
  (! i (^ (poly_sub p1 p2) p3)\n\
    (th_holds (>=0_poly p3)))))))))\n\
\n\
(declare lra_sub_distinct_=\n\
  (! p1 poly\n\
  (! p2 poly\n\
  (! p3 poly\n\
  (! f1 (th_holds (distinct0_poly p1))\n\
  (! f2 (th_holds (=0_poly p2))\n\
  (! i (^ (poly_sub p1 p2) p3)\n\
    (th_holds (distinct0_poly p3)))))))))\n\
\n\
 ;; converting between terms and polynomials\n\
\n\
(declare poly_norm (! t (term Real) (! p poly type)))\n\
\n\
(declare pn_let\n\
  (! t (term Real)\n\
  (! p poly\n\
  (! pn (poly_norm t p)\n\
\n\
  (! u (! pnt (poly_norm t p)\n\
         (holds cln))\n\
    (holds cln))))))\n\
\n\
(declare pn_const\n\
  (! x mpq\n\
    (poly_norm (a_real x) (polyc x lmonn))))\n\
\n\
(declare pn_var\n\
  (! v var_real\n\
    (poly_norm (a_var_real v) (polyc 0/1 (lmonc 1/1 v lmonn)))))\n\
\n\
\n\
(declare pn_+\n\
  (! x (term Real)\n\
  (! px poly\n\
  (! y (term Real)\n\
  (! py poly\n\
  (! pz poly\n\
  (! pnx (poly_norm x px)\n\
  (! pny (poly_norm y py)\n\
  (! a (^ (poly_add px py) pz)\n\
    (poly_norm (+_Real x y) pz))))))))))\n\
\n\
(declare pn_-\n\
  (! x (term Real)\n\
  (! px poly\n\
  (! y (term Real)\n\
  (! py poly\n\
  (! pz poly\n\
  (! pnx (poly_norm x px)\n\
  (! pny (poly_norm y py)\n\
  (! a (^ (poly_sub px py) pz)\n\
    (poly_norm (-_Real x y) pz))))))))))\n\
\n\
(declare pn_mul_c_L\n\
  (! y (term Real)\n\
  (! py poly\n\
  (! pz poly\n\
  (! x mpq\n\
  (! pny (poly_norm y py)\n\
  (! a (^ (poly_mul_c py x) pz)\n\
    (poly_norm (*_Real (a_real x) y) pz))))))))\n\
\n\
(declare pn_mul_c_R\n\
  (! y (term Real)\n\
  (! py poly\n\
  (! pz poly\n\
  (! x mpq\n\
  (! pny (poly_norm y py)\n\
  (! a (^ (poly_mul_c py x) pz)\n\
    (poly_norm (*_Real y (a_real x)) pz))))))))\n\
\n\
(declare poly_flip_not_>=\n\
  (! p poly\n\
  (! p_negged poly\n\
  (! pf_formula (th_holds (not (>=0_poly p)))\n\
  (! sc (^ (poly_neg p) p_negged)\n\
     (th_holds (>0_poly p_negged)))))))\n\
\n\
\n\
;; for polynomializing other terms, in particular ite's\n\
\n\
(declare term_atom (! v var_real (! t (term Real) type)))\n\
\n\
(declare decl_term_atom\n\
  (! t (term Real)\n\
  (! u (! v var_real\n\
       (! a (term_atom v t)\n\
         (holds cln)))\n\
    (holds cln))))\n\
\n\
(declare pn_var_atom\n\
  (! v var_real\n\
  (! t (term Real)\n\
  (! a (term_atom v t)\n\
    (poly_norm t (polyc 0/1 (lmonc 1/1 v lmonn)))))))\n\
\n\
\n\
;; conversion between term formulas and polynomial formulas\n\
\n\
(declare poly_formula_norm (! ft formula (! fp formula type)))\n\
\n\
; convert between term formulas and polynomial formulas\n\
\n\
(declare poly_form\n\
  (! ft formula\n\
  (! fp formula\n\
  (! p (poly_formula_norm ft fp)\n\
  (! u (th_holds ft)\n\
    (th_holds fp))))))\n\
\n\
(declare poly_form_not\n\
  (! ft formula\n\
  (! fp formula\n\
  (! p (poly_formula_norm ft fp)\n\
  (! u (th_holds (not ft))\n\
    (th_holds (not fp)))))))\n\
\n\
(declare poly_formula_norm_>=\n\
  (! x (term Real)\n\
  (! y (term Real)\n\
  (! p poly\n\
  (! n (poly_norm (-_Real y x) p)\n\
     (poly_formula_norm (>=_Real y x) (>=0_poly p)))))))\n\
\n\
\
";

}  // namespace proof
}  // namespace CVC4
