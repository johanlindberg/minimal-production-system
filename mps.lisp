;;; Minimal Production System (MPS)
;;; Copyright (C) 2008-2009 Johan Lindberg, Pulp Software

;;; This program is free software: you can redistribute it and/or modify
;;; it under the terms of the GNU General Public License as published by
;;; the Free Software Foundation, either version 3 of the License, or
;;; (at your option) any later version.

;;; This program is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU General Public License for more details.

;;; You should have received a copy of the GNU General Public License
;;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

(defpackage :mps
  (:use :common-lisp)
  (:export :agenda
           :assert-facts
           :clear
           :deffacts
           :defrule
           :depth
           :facts
           :halt
           :modify-fact
           :reset
           :retract-facts
           :run
           :watch
           :unwatch))
(in-package :mps)

(defstruct activation
  rule
  salience
  token
  timestamp
  rhs-function
  production-memory)

(defparameter *deffacts* (make-hash-table))
(defparameter *defrules* '())

;;; Watch parameters
(defparameter *activations* nil)
(defparameter *compilations* nil)
(defparameter *facts* nil)
(defparameter *rules* nil)

;;; Debug parameters
(defparameter *code* nil) ; Print all generated code
(defparameter *trace* nil) ; Trace all generated code

;;; Compilation globals
(defparameter *variable-bindings* (make-hash-table))
(defparameter *fact-bindings* (make-hash-table))
(defparameter *ce-bindings* (make-hash-table))
(defparameter *nodes* (make-hash-table))
(defparameter *salience* 0)
(defparameter *compilation-string* '())

;;; Helper methods
(defun make-sym (&rest parts)
  "Makes a symbol of <parts>."
  (let ((sym ""))
    (dolist (part (mapcar #'string-upcase (mapcar #'string parts)))
      (setf sym (concatenate 'string sym part)))
    (intern sym)))

(defun variable-p (sym)
  "Returns T if <sym> is a variable (starts with ?) otherwise NIL."
  (and (symbolp sym)
       (eq (char (string sym) 0) #\?)))

;; Stolen from On Lisp by Paul Graham.
(defun flatten (lst)
  "Returns a flattened version of <lst>."
  (labels ((rec (lst acc) 
             (cond ((null lst) acc) 
                   ((atom lst) (cons lst acc)) 
                   (t (rec (car lst) (rec (cdr lst) acc)))))) 
    (rec lst nil)))

;;; Conflict resolution strategies (depth)
(flet ((order-by-salience (conflict-set)
         (stable-sort conflict-set #'(lambda (activation1 activation2)
                                       (> (activation-salience activation1)
                                          (activation-salience activation2))))))
  (defun depth (conflict-set)
    "Sorts (according to salience and timestamp) and returns <conflict-set>."
    (order-by-salience (stable-sort conflict-set
                                    #'(lambda (activation1 activation2)
                                        (> (activation-timestamp activation1)
                                           (activation-timestamp activation2)))))))

(let* ((conflict-resolution-strategy #'depth)
       (rete-network (make-hash-table))
       (root-node (setf (gethash 'root rete-network) (make-hash-table)))
       (working-memory (make-hash-table :test #'equalp))
       (current-fact-index 0)
       (current-timestamp 0))

  (defun agenda ()
    "Returns the current agenda and the number of activations on it."
    (let ((conflict-set (nreverse (flatten (get-conflict-set)))))
      (values (funcall conflict-resolution-strategy conflict-set)
              (length conflict-set))))

  (defun assert-facts (&rest fact-list)
    "Adds facts in <fact-list> to the working memory and Rete Network.

     Identical facts (tested with equalp) are not allowed and will not be
     processed. Returns the number of facts asserted."
    (let ((count 0))
      (incf current-timestamp)
      (dolist (fact fact-list)
        (unless (gethash fact working-memory)
          (let ((fact-copy (copy-structure fact)))
            (incf current-fact-index)
            (setf (gethash fact-copy working-memory) current-fact-index)
            (setf (gethash current-fact-index working-memory) fact-copy)
            (format *facts* "~&=> FACT: F-~D ~S~%" current-fact-index fact-copy)
            (incf count)
            (dolist (nodes (gethash (type-of fact-copy) (gethash 'root rete-network)))
              (if (consp nodes)
                  (dolist (node nodes)
                    (funcall node '+ fact-copy current-timestamp))
                  (funcall nodes '+ fact-copy current-timestamp))))))
      count))

  (defun clear ()
    "Clears the engine."
    (clrhash rete-network)
    (setf root-node (setf (gethash 'root rete-network) (make-hash-table)))

    (clrhash working-memory)
    (setf current-fact-index 0)
    (setf current-timestamp 0)

    (setf *defrules* '())
    (clrhash *nodes*)
    (clrhash *deffacts*)

    t)

  (defmacro deffacts (name &rest facts)
    (setf (gethash name *deffacts*) '())
    (dolist (fact facts)
      (push fact (gethash name *deffacts*)))
    `,(length (gethash name *deffacts*)))

  (defun facts ()
    "Returns all facts in Working Memory."
    (let ((result '()))
      (maphash #'(lambda (key value)
                   (when (numberp key)
                     (push value result)))
               working-memory)
      result))

  (defmacro modify-fact (fact modifier-fn)
    "Modifies a <fact> in Working Memory as specified in <modifier-fn>.

     <modifier-fn> needs to be a function that takes one argument (fact)."
    (let ((temp-reference (gensym)))
      `(let ((,temp-reference ,fact))
         (retract-facts ,temp-reference)
         (funcall ,modifier-fn ,fact)
         (assert-facts ,temp-reference))))

  (defun reset ()
    "Clears the Working Memory and Rete Network memory nodes of facts and then
     asserts all facts defined in deffacts forms."
    (apply #'retract-facts (facts))
    (setf current-fact-index 0)
    (maphash #'(lambda (name fact-list)
                 (declare (ignore name))
                 (apply #'assert-facts fact-list))
             *deffacts*)
    t)

  (defun retract-facts (&rest fact-list)
    "Removes facts in <fact-list> from the Working Memory and Rete Network."
    (let ((count 0))
      (incf current-timestamp)
      (dolist (fact fact-list)
        (when (numberp fact)
          (setf fact (get-fact-with-index fact)))
        (when (gethash fact working-memory)
          (let ((fact-index (get-fact-index-of fact)))
            (dolist (node (gethash (type-of fact) (gethash 'root rete-network)))
              (funcall node '- fact current-timestamp))
            (remhash fact-index working-memory)
            (remhash fact working-memory)
            (format *facts* "~&<= FACT: F-~D ~S~%" fact-index fact)
            (incf count))))

      count))

  (let ((limit -1))
    (defun run (&optional (n -1))
      "Run"
      (setf limit n)
      (do* ((curr-agenda (agenda) (agenda))
            (execution-count 0 (+ execution-count 1)))
           ((or (eq limit 0)
                (eq (length curr-agenda) 0)) execution-count)
        (decf limit)
        (let ((activation (first curr-agenda)))
          (format *rules* "~&FIRE: ~A ~S~%" (activation-rule activation) (activation-token activation))
          (funcall (activation-rhs-function activation) activation)
          (store-activation '- activation (activation-production-memory activation)))))

    (defun halt ()
      "Halt"
      (setf limit 0)))

  (defmacro watch (&rest flags)
    "Watch"
    `(progn
       ,@(mapcar #'(lambda (flag)
                     `(setf ,(make-sym "*" flag "*") t))
                 flags)))
      
  (defmacro unwatch (&rest flags)
    "Unwatch"
    `(progn
       ,@(mapcar #'(lambda (flag)
                     `(setf ,(make-sym "*" flag "*") nil))
                 flags)))

  ; Conditional element macros
  (defmacro exists (&rest conditional-elements)
    `(not (not ,@conditional-elements)))

  (defmacro forall (conditional-element &rest conditional-elements)
    `(not ,conditional-element (not ,@conditional-elements)))


  ;; Private API
  (defun add-to-production-nodes (node)
    "Adds <node> to the list of production nodes."
    (let ((production-memory (make-sym "MEMORY/" node)))
      (format *code* "~&(ADD-TO-PRODUCTION-NODES :NODE ~S)~%" node)
      (if (gethash 'production-nodes rete-network)
          (push production-memory (gethash 'production-nodes rete-network))
          (setf (gethash 'production-nodes rete-network) (list production-memory)))))

  (defun add-to-root (type node)
    "Adds <node> as a successor to the type-node for <type>."
    (format *code* "~&(ADD-TO-ROOT :TYPE ~S :NODE ~S)~%" type node)
    (if (gethash type root-node)
        (push node (gethash type root-node))
        (setf (gethash type root-node) (list node))))

  (defun connect-nodes (from to)
    "Connects <from> with <to> in the Rete Network."
    (format *code* "~&(CONNECT-NODES :FROM ~S :TO ~S)~%" from to)
    (if (gethash from rete-network)
        (push to (gethash from rete-network))
        (setf (gethash from rete-network) (list to))))

  (defun contents-of (memory)
    "Returns the contents of <memory>."
    (gethash memory rete-network))

  (defun get-conflict-set ()
    "Returns the conflict-set."
    (mapcar #'contents-of (gethash 'production-nodes rete-network)))

  (defun propagate (key token timestamp from)
    "Propagates <token> (with <key> and <timestamp>) to all nodes that are connected to <from>."
    (format *trace* "~&(PROPAGATE :KEY ~S :TOKEN ~S :TIMESTAMP ~S :FROM ~S)~%" key token timestamp from)
    (dolist (node (gethash from rete-network))
      (funcall node key token timestamp)))

  (defun get-fact-with-index (index)
    "Returns the fact instance with fact-index <index>."
    (gethash index working-memory))

  (defun get-fact-index-of (fact)
    "Returns the fact-index of <fact>."
    (gethash fact working-memory))

  (defun store-activation (key activation memory)
    "Adds <activation> to (if <key> is '+) or removes from (if <key> is '-) <memory>."
    (format *trace* "~&(STORE-ACTIVATION :KEY ~S :ACTIVATION ~S :MEMORY ~S)~%" key activation memory)
    (if (eq key '+)
        ;; Add activation
        (if (gethash memory rete-network)
            (unless (member activation (gethash memory rete-network) :test #'equalp)
              (push activation (gethash memory rete-network)))
            (setf (gethash memory rete-network) (list activation)))
        ;; Remove activation
        (when (gethash memory rete-network)
          (setf (gethash memory rete-network)
                (remove-if #'(lambda (item)
                               (and (equalp (activation-rule item) (activation-rule activation))
                                    (equalp (activation-token item) (activation-token activation))))
                           (gethash memory rete-network))))))

  (defun update-count (key token count-memory)
    "Increments (if <key> is '+) or decrements (if <key> is '-) <count-memory> for <token>."
    (format *trace* "~&(UPDATE-COUNT :KEY ~S :TOKEN ~S :COUNT-MEMORY ~S)" key token count-memory)
    (unless (gethash count-memory rete-network)
      (setf (gethash count-memory rete-network) (make-hash-table :test #'equalp)))
    (let ((old-count (gethash token (gethash count-memory rete-network) 0))
          (new-count (if (eq key '+)
                         (incf (gethash token (gethash count-memory rete-network) 0))
                         (decf (gethash token (gethash count-memory rete-network) 0)))))
      (values new-count old-count)))

  (defun store (key token memory)
    "Adds <token> to (if <key> is '+) or removes from (if <key> is '-) <memory>."
    (format *trace* "~&(STORE :KEY ~S :TOKEN ~S :MEMORY ~S)~%" key token memory)
    (if (eq key '+)
        ;; Add token
        (if (gethash memory rete-network)
            (unless (member token (gethash memory rete-network) :test #'equalp)
              (push token (gethash memory rete-network)))
            (setf (gethash memory rete-network) (list token)))
        ;; Remove token
        (when (gethash memory rete-network)
          (setf (gethash memory rete-network) (remove-if #'(lambda (item)
                                                             (equalp item token))
                                                         (gethash memory rete-network)))))))

(defmacro defrule (name &body body)
  (if (member name *defrules*)
      (error "Cannot redefine ~A" name)
      (progn
        (push name *defrules*)
        (setf *nodes* (make-hash-table)
              *fact-bindings* (make-hash-table)
              *ce-bindings* (make-hash-table)
              *variable-bindings* (make-hash-table)
              *compilation-string* '()
              *salience* 0)
        (let ((rhs (if (cdr (member '=> body))
                       (cdr (member '=> body))
                       `(t)))
              (lhs (ldiff body (member '=> body))))
          `(progn
             (compile-lhs ,name 0 ,@lhs)
             (compile-rhs ,name ,@rhs)
             (make-production-node ',name)
             (format *compilations* "~&DEFRULE ~A: ~{~A~}~%" ',name *compilation-string*)
             ',name)))))

(defmacro compile-lhs (rule-name position &rest conditional-elements)
  (unless (eq (car conditional-elements) 'nil)
    (cond ((consp (car conditional-elements))
           (if (equal 'salience (caar conditional-elements))
               `(progn
                  (setf *salience* ,(cadar conditional-elements))
                  (compile-lhs ,rule-name ,position ,@(cdr conditional-elements)))
               `(progn
                  (parse-ce ,rule-name ,position ,(car conditional-elements))
                  (compile-lhs ,rule-name ,(+ position 1) ,@(cdr conditional-elements)))))
          ((variable-p (car conditional-elements))
           (progn
             (assert (eq (cadr conditional-elements) '<-))
             `(progn
                (parse-pattern-ce ,rule-name ,position ,(car conditional-elements) ,(caddr conditional-elements))
                (compile-lhs ,rule-name ,(+ position 1) ,@(cdddr conditional-elements))))))))

(defmacro parse-ce (rule-name position conditional-element)
  (let ((ce-type (car conditional-element)))
    (case ce-type
      (not `(parse-not-ce ,rule-name ,position ,conditional-element))
      (test `(parse-test-ce ,rule-name ,position ,conditional-element))
      (otherwise `(parse-pattern-ce ,rule-name ,position nil ,conditional-element)))))

(defmacro parse-not-ce (rule-name position conditional-element)
  (if (eq position 0)
      (error "Error in ~A~%A Not-CE cannot appear first in a rule!" rule-name)
      (if (> (length (cdr conditional-element)) 1)
          (error "Error in ~A~%A Not-CE cannot contain more than one Pattern-CE!" rule-name) ; TBD!
          `(let ((not-node '()))
             (multiple-value-bind (alpha-node deferred-tests)
                 (make-alpha-node ',rule-name ',(caadr conditional-element) ',(cadr conditional-element) nil ,position nil)
               (setf (gethash ,position *nodes*) alpha-node)
               (setf not-node (make-single-not-node ',rule-name ,position deferred-tests))
               (connect-nodes alpha-node (make-sym not-node "-right")))))))

(defmacro parse-test-ce (rule-name position conditional-element)
  (if (eq position 0)
      (error "Error in ~A~%A Test-CE cannot appear first in a rule!" rule-name)
      `(let ((left-node (gethash ,(- position 1) *nodes*))
             (test-node (make-test-node ',rule-name ',(cadr conditional-element) ,position)))
         (setf (gethash ,position *nodes*) test-node)
         (connect-nodes left-node test-node))))

(defmacro parse-pattern-ce (rule-name position variable conditional-element)
  (let ((defstruct-name (car conditional-element)))
    `(let ((beta-node '()))
       (unless ,(null variable)
         (setf (gethash ',variable *fact-bindings*) ,position))
       (multiple-value-bind (alpha-node deferred-tests)
           (make-alpha-node ',rule-name ',defstruct-name ',conditional-element ',variable ,position t)
         (setf (gethash ,position *nodes*) alpha-node)
         (setf beta-node (make-beta-node ',rule-name ,position deferred-tests))
         (connect-nodes alpha-node (make-sym beta-node "-right"))))))

(defun make-alpha-node (rule-name defstruct-name conditional-element variable position accessible)
  (let ((prev-node '())
        (deferred-tests '())
        (tests '()))
    (dolist (slot (cdr conditional-element))
      (let* ((slot-name (car slot))
             (slot-binding (if (variable-p (cadr slot))
                               (cadr slot)
                               nil))
             (slot-constraint (if (null slot-binding)
                                  (cadr slot)
                                  (caddr slot))))
        (when (defer? slot-binding slot-constraint)
          (push slot-constraint deferred-tests)
          (setq slot-constraint '()))
        
        (push (if (or (and (consp slot-constraint)
                           (not (equalp (car slot-constraint) 'quote)))
                      (symbolp slot-constraint))
                  (make-symbol-constraint defstruct-name slot-name slot-binding slot-constraint variable position accessible)
                  (make-literal-constraint defstruct-name slot-name slot-constraint))
              tests)))
    
    (let* ((alpha-node-name (make-sym "ALPHA/" rule-name "-" (format nil "~A" position) "/" defstruct-name))
           (alpha-node `(defun ,alpha-node-name (key fact timestamp)
                          (format *trace* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',alpha-node-name key fact timestamp)
                          (when (and ,@tests)
                            (store key fact ',(make-sym "MEMORY/" alpha-node-name))
                            (propagate key fact timestamp ',alpha-node-name)))))
      (let ((*print-pretty* t))
        (format *code* "~&~S~%" alpha-node))
      (eval alpha-node)
      (push "+A" *compilation-string*)
      (if prev-node
          (connect-nodes prev-node alpha-node-name)
          (add-to-root defstruct-name alpha-node-name))
      (setf prev-node alpha-node-name))
    (values prev-node deferred-tests)))
      
(defun make-literal-constraint (defstruct-name slot-name slot-constraint)
  `(equalp (,(make-sym defstruct-name "-" slot-name) fact) ,slot-constraint))

(defun make-symbol-constraint (defstruct-name slot-name slot-binding slot-constraint variable position accessible)
  (let* ((slot-accessor (make-sym defstruct-name "-" slot-name))
         (binding-constraint (parse-binding-constraint slot-binding slot-constraint slot-accessor variable position accessible)))
    (cond ((and binding-constraint slot-constraint)
           `(and ,binding-constraint ,(expand-variables slot-constraint)))
          (binding-constraint
           binding-constraint)
          (slot-constraint
           (expand-variables slot-constraint))
          (t nil))))

(defun defer? (var constraint)
  (when var
    (cond ((null (car constraint)) '())
          ((atom (car constraint)) (or (and (variable-p (car constraint))
                                            (not (equal var (car constraint))))
                                       (defer? var (cdr constraint))))
          ((consp (car constraint)) (or (defer? var (car constraint))
                                        (defer? var (cdr constraint)))))))

(defun make-beta-node (rule-name position deferred-tests)
  (let* ((left-node (unless (eq position 0)
                      (gethash (- position 1) *nodes*)))
         (right-node (gethash position *nodes*))
         (beta-node-name (make-sym "BETA/" rule-name "-" (format nil "~d" position)))
         (left-activate (make-sym beta-node-name "-LEFT"))
         (right-activate (make-sym beta-node-name "-RIGHT"))
         (beta-node (if left-node
                        `(let ((left-memory  ',(make-sym "MEMORY/" left-node))
                               (right-memory ',(make-sym "MEMORY/" right-node)))
                           (defun ,left-activate (key token timestamp)
                             (declare (inline get-fact-with-index get-fact-index-of))
                             (format *trace* "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%" ',left-activate key token timestamp)
                             (dolist (fact (contents-of right-memory))
                               (let ((tok (append token (list (get-fact-index-of fact)))))
                                 (when (and ,@(make-binding-test position)
                                            ,@(expand-variables-token deferred-tests))
                                   (store key tok ',(make-sym "MEMORY/" beta-node-name))
                                   (propagate key tok timestamp ',beta-node-name)))))
                           
                           (defun ,right-activate (key fact timestamp)
                             (declare (inline get-fact-with-index get-fact-index-of))
                             (format *trace* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',right-activate key fact timestamp)
                             (dolist (token (contents-of left-memory))
                               (let ((tok (append token (list (get-fact-index-of fact)))))
                                 (when (and ,@(make-binding-test position)
                                            ,@(expand-variables-token deferred-tests))
                                   (store key tok ',(make-sym "MEMORY/" beta-node-name))
                                   (propagate key tok timestamp ',beta-node-name))))))
                        
                        ;; Left-input adapter
                        `(defun ,right-activate (key fact timestamp)
                           (declare (inline get-fact-index-of))
                           (format *trace* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',right-activate key fact timestamp)
                           (store key (list (get-fact-index-of fact)) ',(make-sym "MEMORY/" beta-node-name))
                           (propagate key (list (get-fact-index-of fact)) timestamp ',beta-node-name)))))
    
    (let ((*print-pretty* t))
      (format *code* "~&~S~%" beta-node))
    (eval beta-node)
    (push "+B" *compilation-string*)
    (unless (eq position 0)
      (connect-nodes left-node left-activate))
    (setf (gethash position *nodes*) beta-node-name)))

(defun make-single-not-node (rule-name position deferred-tests)
  (let* ((left-node (gethash (- position 1) *nodes*))
         (right-node (gethash position *nodes*))
         (not-node-name (make-sym "NOT/" rule-name "-" (format nil "~D" position)))
         (left-activate (make-sym not-node-name "-LEFT"))
         (right-activate (make-sym not-node-name "-RIGHT"))
         (not-node `(let ((left-memory ',(make-sym "MEMORY/" left-node))
                          (right-memory ',(make-sym "MEMORY/" right-node)))
                      (defun ,left-activate (key token timestamp)
                        (declare (inline get-fact-with-index get-fact-index-of))
                        (format *trace* "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%" ',left-activate key token timestamp)
                        (if (eq (length (contents-of right-memory)) 0)
                            (let ((tok (append token (list nil))))
                              (store key tok ',(make-sym "MEMORY/" not-node-name))
                              (propagate key tok timestamp ',not-node-name))			    
                            (let ((propagate-token t))
                              (dolist (fact (contents-of right-memory))
                                (let ((tok (append token (list (get-fact-index-of fact)))))
                                  (when (and ,@(make-binding-test position)
                                             ,@(expand-variables-token deferred-tests))
                                    (setf propagate-token nil))))
                              (when propagate-token
                                (let ((tok (append token (list nil))))
                                  (store key tok ',(make-sym "MEMORY/" not-node-name))
                                  (propagate key tok timestamp ',not-node-name))))))
                      
                      (defun ,right-activate (key fact timestamp)
                        (declare (inline get-fact-with-index get-fact-index-of))
                        (format *trace* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',right-activate key fact timestamp)
                        (dolist (token (contents-of left-memory))
                          (let ((tok (append token (list (get-fact-index-of fact))))
                                (ptok (append token (list nil))))
                            (when (and ,@(make-binding-test position)
                                       ,@(expand-variables-token deferred-tests))
                              (multiple-value-bind (new-count old-count)
                                  (update-count key tok ',(make-sym "COUNT-MEMORY/" not-node-name))
                                (declare (fixnum new-count old-count))
                                (store key ptok ',(make-sym "MEMORY/" not-node-name))
                                (cond ((and (eq (the fixnum new-count) 0)
                                            (eq (the fixnum old-count) 1)
                                            (eq key '-))
                                       (propagate '+ ptok timestamp ',not-node-name))
                                      ((and (eq (the fixnum new-count) 1)
                                            (or (eq (the fixnum old-count) 0)
                                                (eq (the fixnum old-count) nil))
                                            (eq key '+))
                                       (propagate '- ptok timestamp ',not-node-name)))))))))))
    
    (let ((*print-pretty* t))
      (format *code* "~&~S~%" not-node))
    (eval not-node)
    (push "+N" *compilation-string*)
    (connect-nodes left-node left-activate)
    (setf (gethash position *nodes*) not-node-name)))

(defun make-test-node (rule-name test-form position)
  (let ((test-node-name (make-sym "TEST/" rule-name "-" (format nil "~D" position)))
        (list-of-fact-bindings '())
        (list-of-variable-bindings '()))
    (maphash #'(lambda (key value)
                 (push (make-fact-binding key value) list-of-fact-bindings))
             *fact-bindings*)
    (maphash #'(lambda (key value)
                 (push (make-variable-binding key value) list-of-variable-bindings))
             *variable-bindings*)
    
    (let ((test-node
           `(defun ,test-node-name (key token timestamp)
              (declare (inline get-fact-with-index))
              (format *trace* "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%" ',test-node-name key token timestamp)
              (let* (,@list-of-fact-bindings
                     ,@list-of-variable-bindings)
                (when ,test-form
                  (store key token ',(make-sym "MEMORY/" test-node-name))
                  (propagate key token timestamp ',test-node-name))))))
      
      (let ((*print-pretty* t))
        (format *code* "~&~S~%" test-node))
      (eval test-node)
      (push "+T" *compilation-string*))
    test-node-name))

(defun make-binding-test (position)
  (let ((result '(t))) ; zero join
    (maphash #'(lambda (k v)
                 (declare (ignore k))
                 (when (> (length v) 1)
                   (let ((prev '()))
                     (dolist (b v)
                       (if (eql position (caddr b))
                           (when prev
                             (push `(equalp (,(car b) (get-fact-with-index (nth ,(caddr b) tok)))
                                            (,(car prev) (get-fact-with-index (nth ,(caddr prev) tok))))
                                   result))
                           (when (cadddr b)
                             (setf prev b)))))))
             *variable-bindings*)
    result))

(defun make-production-node (rule-name)
  (let* ((production-node-name (make-sym "PRODUCTION/" rule-name))
         (production-memory (make-sym "MEMORY/PRODUCTION/" rule-name))
         (production-node `(defun ,production-node-name (key token timestamp)
                             (format *trace* "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%" ',production-node-name key token timestamp)
                             (if (eq key '+)
                                 (format *activations* "~&=> ACTIVATION: ~A ~S~%" ',rule-name token)
                                 (format *activations* "~&<= ACTIVATION: ~A ~S~%" ',rule-name token))
                             (store-activation key (make-activation :rule ',rule-name
                                                                    :salience ,*salience*
                                                                    :token token
                                                                    :timestamp timestamp
                                                                    :rhs-function #',(make-sym "RHS/" rule-name)
                                                                    :production-memory ',production-memory)
                                               ',production-memory))))
    
    (let ((*print-pretty* t))
      (format *code* "~&~S~%" production-node))
    (eval production-node)
    (push "+P" *compilation-string*)
    (connect-nodes (gethash (- (hash-table-count *nodes*) 1) *nodes*) production-node-name)
    (add-to-production-nodes production-node-name)))

(defun parse-binding-constraint (slot-binding slot-constraint slot-accessor variable position accessible)
  (let ((fact-variable (if variable
                           variable
                           (gethash position *ce-bindings*)))
        (binding (gethash slot-binding *variable-bindings*)))
    (when (not (null slot-binding))
      ;; Make sure that this slot-value is reachable in the RHS
      (when (null fact-variable)
        (setf fact-variable (gensym))
        (setf (gethash position *ce-bindings*) fact-variable)
        (setf (gethash fact-variable *fact-bindings*) position))
      
      (if (not binding)
          (progn ; This is the first binding for this variable
            (setf (gethash slot-binding *variable-bindings*) (list (list slot-accessor fact-variable position accessible)))
            (when (null slot-constraint) t))

          (progn
            (dolist (b binding)
              ;; If this position already has a binding for this variable we'll
              ;; return an alpha-constraint
              (when (equal position (caddr b))
                (return `(equalp (,(car b) fact) (,slot-accessor fact)))))
            
            ;; Create a new binding
            (setf (gethash slot-binding *variable-bindings*)
                  (nconc (gethash slot-binding *variable-bindings*)
                         (list (list slot-accessor fact-variable position accessible))))
            (when (null slot-constraint) t))))))

(defun expand-variables (form)
  (maphash #'(lambda (key value)
               (nsubst `(,(caar value) fact) key form))
           *variable-bindings*)
  form)

(defun expand-variables-token (form)
  (maphash #'(lambda (key value)
               (nsubst `(,(caar value) (get-fact-with-index (nth ,(caddar value) tok))) key form)) 
           *variable-bindings*)
  form)

(defun make-variable-binding (key value)
  ;; variable-name : ((accessor fact-variable position) ...) -> (variable-name (accessor fact-variable))
  `(,key (,(caar value) ,(cadar value))))

(defun make-fact-binding (key value)
  ;; variable-name : position
  `(,key (get-fact-with-index (nth ,value token)))) 

(defmacro compile-rhs (rule-name &rest rhs)
  (let ((list-of-fact-bindings '())
        (list-of-variable-bindings '()))
    (maphash #'(lambda (key value)
                 (push (make-fact-binding key value) list-of-fact-bindings))
             *fact-bindings*)
    (maphash #'(lambda (key value)
                 (push (make-variable-binding key value) list-of-variable-bindings))
             *variable-bindings*)
    (let* ((rhs-function-name (make-sym "RHS/" rule-name))
           (rhs-function `(defun ,rhs-function-name (activation)
                            (declare (inline get-fact-with-index))
                            (format *trace* "~&(~A :ACTIVATION ~S)~%" ',rhs-function-name activation)
                            (let* ((token (activation-token activation))
                                   ,@list-of-fact-bindings
                                   ,@list-of-variable-bindings)
                              ,@rhs))))

      (let ((*print-pretty* t))
        (format *code* "~&~S~%" rhs-function))
      rhs-function)))
