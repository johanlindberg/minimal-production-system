;; Tests for MPS:MODIFY-FACTS
(clear)
(assert-facts #S(foo :bar 1) #S(foo :bar 2))
(modify-facts ((1 (bar 3))))
(facts)

