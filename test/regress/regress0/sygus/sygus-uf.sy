(set-logic LIA)

(declare-fun uf (Int) Int)

(synth-fun f ((x Int) (y Int)) Bool
  ((Start Bool (true false
                (<= IntExpr IntExpr)
                (= IntExpr IntExpr)
                (and Start Start)
                (or Start Start)
                (not Start)))
   (IntExpr Int (0 1 x y
                 (+ IntExpr IntExpr)
                 (- IntExpr IntExpr)))))

(declare-var x Int)

(constraint (f (uf x) (uf x)))

(check-synth)
