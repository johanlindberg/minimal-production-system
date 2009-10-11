Minimal Production System
=========================

Introduction
------------
The Minimal Production System (MPS) started out as an experiment in Common Lisp
macrology (the idea was to convert a subset of CLIPS syntax into executable
Common Lisp code) but since the | character has special meaning to the Common
Lisp reader it's difficult to implement the or-connective-constraint in
pattern-CE's. So, instead I'll focus on implementing a production system using
Common Lisp syntax instead.

There's a bit more info about the CLIPS expirement on my old blog // comments
are lies! See http://commentsarelies.blogspot.com/search/label/MPS

Current Status
--------------
Currently (2009-09-19) MPS has a small (but growing) set of feature tests (see
/tests) and works, more or less, as it should. The Not-CE can still only handle
one Pattern-CE. I'll try to fix that during autumn. I'm also working on making
MPS ASDF-installable.

Simplest example possible
-------------------------
CL-USER> (in-package :mps)
#<Package "MPS">
MPS> (watch activations code facts rules)
T
MPS> (defstruct foo value)
FOO
MPS> (defrule test
       (foo (value ?value))
       =>
       (print ?value)
       (halt))
(DEFUN ALPHA/TEST-0/FOO (KEY FACT TIMESTAMP)
  (FORMAT *TRACE*
          "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%"
          'ALPHA/TEST-0/FOO
          KEY
          FACT
          TIMESTAMP)
  (WHEN (AND T)
    (STORE KEY FACT 'MEMORY/ALPHA/TEST-0/FOO)
    (PROPAGATE KEY FACT TIMESTAMP 'ALPHA/TEST-0/FOO)))
(ADD-TO-ROOT :TYPE FOO :NODE ALPHA/TEST-0/FOO)
(DEFUN BETA/TEST-0-RIGHT (KEY FACT TIMESTAMP)
  (FORMAT *TRACE*
          "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%"
          'BETA/TEST-0-RIGHT
          KEY
          FACT
          TIMESTAMP)
  (STORE KEY (LIST FACT) 'MEMORY/BETA/TEST-0)
  (PROPAGATE KEY (LIST FACT) TIMESTAMP 'BETA/TEST-0))
(CONNECT-NODES :FROM ALPHA/TEST-0/FOO :TO BETA/TEST-0-RIGHT)
(DEFUN RHS/TEST (ACTIVATION)
  (FORMAT *TRACE* "~&(~A :ACTIVATION ~S)~%" 'RHS/TEST ACTIVATION)
  (LET* ((TOKEN (ACTIVATION-TOKEN ACTIVATION))
         (#:G874 (NTH 0 TOKEN))
         (?VALUE (FOO-VALUE #:G874)))
    (PRINT ?VALUE)
    (HALT)))
(DEFUN PRODUCTION/TEST (KEY TOKEN TIMESTAMP)
  (FORMAT *TRACE*
          "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%"
          'PRODUCTION/TEST
          KEY
          TOKEN
          TIMESTAMP)
  (IF (EQ KEY '+)
      (FORMAT *ACTIVATIONS* "~&=> ACTIVATION: ~A ~S~%" 'TEST TOKEN)
      (FORMAT *ACTIVATIONS* "~&<= ACTIVATION: ~A ~S~%" 'TEST TOKEN))
  (STORE-ACTIVATION
    KEY
    (MAKE-ACTIVATION
      :RULE
      'TEST
      :SALIENCE
      0
      :TOKEN
      TOKEN
      :TIMESTAMP
      TIMESTAMP
      :RHS-FUNCTION
      #'RHS/TEST
      :PRODUCTION-MEMORY
      'MEMORY/PRODUCTION/TEST)
    'MEMORY/PRODUCTION/TEST))
(CONNECT-NODES :FROM BETA/TEST-0 :TO PRODUCTION/TEST)
(ADD-TO-PRODUCTION-NODES :NODE PRODUCTION/TEST)
TEST
MPS> (assert-facts #S(foo :value 1) #S(foo :value 2) #S(foo :value 3))
=> FACT: F-1 #S(FOO :VALUE 1)
=> ACTIVATION: TEST (#S(FOO :VALUE 1))
=> FACT: F-2 #S(FOO :VALUE 2)
=> ACTIVATION: TEST (#S(FOO :VALUE 2))
=> FACT: F-3 #S(FOO :VALUE 3)
=> ACTIVATION: TEST (#S(FOO :VALUE 3))
3
MPS> (pprint (agenda))

(#S(ACTIVATION :RULE TEST :SALIENCE 0 :TOKEN (#S(FOO :VALUE 1)) :TIMESTAMP 1
               :RHS-FUNCTION #<Compiled-function RHS/TEST #x3000413FCB3F>
               :PRODUCTION-MEMORY MEMORY/PRODUCTION/TEST)
 #S(ACTIVATION :RULE TEST :SALIENCE 0 :TOKEN (#S(FOO :VALUE 2)) :TIMESTAMP 1
               :RHS-FUNCTION #<Compiled-function RHS/TEST #x3000413FCB3F>
               :PRODUCTION-MEMORY MEMORY/PRODUCTION/TEST)
 #S(ACTIVATION :RULE TEST :SALIENCE 0 :TOKEN (#S(FOO :VALUE 3)) :TIMESTAMP 1
               :RHS-FUNCTION #<Compiled-function RHS/TEST #x3000413FCB3F>
               :PRODUCTION-MEMORY MEMORY/PRODUCTION/TEST)); No value
MPS> (run)
FIRE: TEST (#S(FOO :VALUE 1))

1 1
MPS> 