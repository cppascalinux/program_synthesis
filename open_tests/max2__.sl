; max3.sl
; Synthesize the maximum of 2 integers, from a purely declarative spec

(set-logic LIA)

(synth-fun max2 ((x Int) (y Int)) Int
    ((Start Int (x
                 y
                 0
                 1
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))

(declare-var a Int)
(declare-var b Int)
(declare-var c Int)

(constraint (>= (max2 (+ a b) c) c))
(constraint (>= (max2 (+ a b) c) (+ a b)))
(constraint (or (= (+ a b) (max2 (+ a b) c))
				(= c (max2 (+ a b) c))))


(check-synth)

