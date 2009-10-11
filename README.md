# Minimal Production System

## Introduction

The Minimal Production System \(MPS\) started out as an experiment in Common Lisp
macrology \(the idea was to convert a subset of [CLIPS](http://clipsrules.sourceforge.net/)
syntax into executable Common Lisp code\) but since the | character has special
meaning to the Common Lisp reader it's difficult to implement the or-connective-constraint
in pattern-CE's. So, instead I've focused on implementing a production system using
Common Lisp syntax and defstructs.

There's a bit more info about the CLIPS experiment on my old \(defunkt\) blog [// comments
are lies!](http://commentsarelies.blogspot.com/search/label/MPS)

## Current Status

Currently \(2009-10-11\) MPS has a small \(but growing\) set of feature tests \(see
/tests\) and works, more or less, as it should. The Not-CE can still only handle
one Pattern-CE. I'll try to fix that during autumn.

## Simplest example possible

    CL-USER> (in-package :mps)
    #<Package "MPS">
    MPS> (watch activations facts rules)
    T
    MPS> (defstruct foo value)
    FOO
    MPS> (defrule test
           (foo (value ?value))
           =>
           (print ?value)
           (halt))
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