(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

(assert (<= (+ (* x x) (* (- 1) (- 5) x) 6) 0))
(assert (or (< (+ (* y y) (* (- 8) x) 1) 0) (< (+ (* y y) (* (- 16) x) 1) 0) ))

(check-sat)
(exit)