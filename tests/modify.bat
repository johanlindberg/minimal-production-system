;; doctests for modify-facts functionality
>> (progn
     (unless (equal (package-name *package*) "MPS")
       (in-package :mps))
     NIL)
NIL
>> (clear)
T
>> (defstruct foo bar)
FOO
>> (defparameter *fact* #S(foo :bar 1))
*FACT*
>> *fact*
(#S(FOO :BAR 1))
>> (assert-facts *fact*)
-> |=> FACT: F-1 #S(FOO :BAR 1)|
1
>> (modify-facts (1 (bar 2))) ; F-1
1
>> (facts)
(#S(FOO :BAR 2))
>> *fact*
(#S(FOO :BAR 2))
>> (modify-facts (*fact* (bar 3)))
1
>> (facts)
(#S(FOO :BAR 3))
>> (modify-facts (#S(foo :bar 3) (bar 4)))
1
>> (facts)
(#S(FOO :BAR 4))
