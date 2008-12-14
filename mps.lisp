;;;; A Minimal Production System (MPS)
;;;; ---------------------------------
;;;; MPS is an attempt to make an easy (to understand, extend and use) Production
;;;; System[1] based on the Rete Algorithm[2]. It borrows all of the concepts and
;;;; syntax from the CLIPS/ART/OPS family of Production Systems.
;;;;
;;;; [1] http://en.wikipedia.org/wiki/Production_System
;;;; [2] http://en.wikipedia.org/wiki/Rete_algorithm

(defpackage :mps
  (:use :common-lisp)
  (:export :deftemplate	:defrule
	   :agenda :assert-fact	:breadth :clear
	   :depth :facts :get-strategy :load
	   :reset :run :set-strategy)
  (:shadow :assert))
(in-package :mps)


;;; Structures and parameters
(defstruct activation
  rule
  salience token timestamp
  rhs-func prod-mem)

(defparameter variable-bindings '())
(defparameter fact-bindings '())
(defparameter current-rule nil)

;;; Helper methods and macros
(defun as-keyword (sym)
  "Returns <sym> as a keyword."
  (intern (string-upcase sym) :keyword))

(defun make-sym (&rest parts)
  (let ((sym ""))
    (dolist (part (mapcar #'string-upcase (mapcar #'string parts)))
      (setf sym (concatenate 'string sym part)))
    (intern sym)))


;;; Conflict resolution strategies
(defun order-by-salience (conflict-set)
  (stable-sort conflict-set #'(lambda (activation1 activation2)
				(> (activation-salience activation1)
				   (activation-salience activation2)))))
		
(defun breadth (conflict-set)
  "Implementation of the conflict resolution strategy 'breadth'"
  (order-by-salience (stable-sort conflict-set
				  #'(lambda (activation1 activation2)
				      (< (activation-timestamp activation1)
					 (activation-timestamp activation2))))))

(defun depth (conflict-set)
  "Implementation of the conflict resolution strategy 'depth'"
  (order-by-salience (stable-sort conflict-set
				  #'(lambda (activation1 activation2)
				      (> (activation-timestamp activation1)
					 (activation-timestamp activation2))))))


;;; Inference engine implementation
(let* ((conflict-resolution-strategy #'depth)
       (rete-network (make-hash-table))
       (root-node (setf (gethash 'root rete-network) (make-hash-table)))
       (fact-index 0)
       (timestamp 0))

  ;; Public API
  (defun agenda ()
    "Return all activations on the agenda."
    (funcall conflict-resolution-strategy (flatten (get-conflict-set))))

  (defun assert (&rest facts)
    "Add <facts> to the working memory"
    (incf timestamp)
    (dolist (fact facts)
      (incf fact-index)
      (store '+ (list fact fact-index) 'memory/working-memory)
      (mapcar #'(lambda (node)
		  (funcall node '+ fact timestamp))
	      (gethash (type-of fact) (gethash 'root rete-network))))
    t)

  (defun clear ()
    "Clear the engine"
    ;; This doesn't clear deftemplates and globals!!
    (clrhash rete-network)
    (setf root-node (setf (gethash 'root rete-network) (make-hash-table)))
    t)

  (defun facts ()
    "Return all facts in working memory"
    (mapcar #'(lambda (fact)
		(car fact))
	    (gethash 'memory/working-memory rete-network)))

  (defun get-strategy ()
    "Return the current conflict resolution strategy."
    conflict-resolution-strategy)

  (defun all-memory-nodes ()
    "Returns a list with the names of all memory nodes in the Rete Network"
    (let ((mem-nodes '()))
      (maphash #'(lambda (key val)
		   (declare (ignore val))
		   (let ((skey (string key)))
		     (when (and (> (length skey) 7)
				(string-equal "MEMORY/"
					      (subseq skey 0 7)))
		       (setf mem-nodes (append (list key) mem-nodes)))))
	       rete-network)
      mem-nodes))

  (defun reset ()
    "Clear the working memory of facts"
    (mapcar #'(lambda (memory) (setf (gethash memory rete-network) '()))
	    (all-memory-nodes))
    t)

  (defun retract (&rest facts)
    "Remove <facts> from the Rete network"

    (incf timestamp)
    (dolist (fact facts)
      (store '- fact 'memory/working-memory)
      (mapcar #'(lambda (node) (funcall node '- fact timestamp))
	      (gethash (type-of fact) (gethash 'root rete-network))))
    t)

  (defun run (&optional (limit -1))
    (do* ((curr-agenda (agenda) (agenda))
	  (execution-count 0 (+ execution-count 1))
	  (limit limit (- limit 1)))
	 ((or (eq limit 0)
	      (= (length curr-agenda) 0)) execution-count)
      (let* ((activation (first curr-agenda)))
	(funcall (activation-rhs-func activation) activation)
	(store '- activation (activation-prod-mem activation)))))

  (defun set-strategy (strategy)
    "This function sets the current conflict resolution strategy. The default strategy is depth. 

     Syntax: 
       (set-strategy #'<strategy-function>) 
 
     where <strategy-function> is either depth or breadth (which are provided in MPS), or a custom
     function that performs conflict resolution. The agenda will be reordered to reflect the new
     conflict resolution strategy."
    (setf conflict-resolution-strategy strategy))


  ;; Private API
  (defun add-to-production-nodes (node)
    "Add <node> to the list of production nodes"
    (if (gethash 'production-nodes rete-network)
	(setf (gethash 'production-nodes rete-network) (append (gethash 'production-nodes rete-network) (list node)))
	(setf (gethash 'production-nodes rete-network) (list node))))

  (defun add-to-root (type node)
    "Add <node> as a successor to the type-node for <type>"
    (if (gethash type root-node)
	(setf (gethash type root-node) (append (gethash type root-node) (list node)))
	(setf (gethash type root-node) (list node))))

  (defun connect-nodes (from to)
    "Connect <from> with <to> in the Rete Network"
    (if (gethash from rete-network)
	(setf (gethash from rete-network) (append (gethash from rete-network) (list to)))
	(setf (gethash from rete-network) (list to))))

  (defun contents-of (memory)
    "Get all tokens in <memory>"
    (gethash memory rete-network))

  (defun flatten (x) 
    (labels ((rec (x acc) 
	       (cond ((null x) acc) 
		     ((atom x) (cons x acc)) 
		     (t (rec (car x) (rec (cdr x) acc)))))) 
      (rec x nil)))

  (defun get-conflict-set ()
    (mapcar #'contents-of (gethash 'production-nodes rete-network)))

  (defun propagate (key token timestamp from)
    "Propagate <token> to all nodes that are connected to <from>"
    (mapcar #'(lambda (node) (funcall node key token timestamp))
	    (gethash from rete-network)))

  (defun store (key token memory)
    "Add (if <key> is '+) or remove (if <key> is '-) <token> from <memory>"
    (if (eq key '+)
	;; Add token
	(if (gethash memory rete-network)
	    (setf (gethash memory rete-network) (append (gethash memory rete-network) (list token)))
	    (setf (gethash memory rete-network) (list token)))

	;; Remove token
	(if (gethash memory rete-network)
	    (setf (gethash memory rete-network) (remove-if #'(lambda (item) (eq item token))
							   (gethash memory rete-network)))))))

;;; deftemplate
;;;
;;; (deftemplate <deftemplate-name> [<comment>] 
;;;   <single-slot-definition>*) 
;;; 
;;; <single-slot-definition>  
;;;                ::= (slot <slot-name>  
;;;                          <default-attribute>) 
;;; 
;;; <default-attribute>   
;;;                ::= (default ?NONE | <expression>) | 
;;;                    (default-dynamic <expression>)

(defmacro slot (name &optional (default-form nil))
  (cond ((null default-form)
	 name)

	;; required value
	((and (eq (car default-form) 'default)
	      (eq (cadr default-form) '?NONE))
	 `(,name (error "The slot: ~A requires a value!" ',name)))

	;; default value
	((eq (car default-form) 'default)
	 `(,name ',(eval (cadr default-form))))

	;; default-dynamic value
	((eq (car default-form) 'default-dynamic)
	 `(,name ,(cadr default-form)))))

(defun call-defstruct-constructor (constructor &rest slots)
  (apply constructor (mapcan #'(lambda (slot)
				 `(,(as-keyword (car slot)) ,(cadr slot)))
			     (car slots))))
  
(defmacro deftemplate (name &body slots)
  "
  The deftemplate construct is used to create a template which can then
  be used by non-ordered facts to access fields of the fact by name.

  Syntax:
  <deftemplate-construct>  
    ::= (deftemplate <deftemplate-name> [<single-slot-definition>]*)
 
  <single-slot-definition>
    ::= (slot <slot-name> [<default-attribute>])
 
  <default-attribute> 
    ::= (default ?NONE | <expression>) |
        (default-dynamic <expression>)

  Examples:
  (deftemplate object
    (slot id (default-dynamic (gensym)))
    (slot name (default ?NONE))           ; Makes name a required field!
    (slot age))
  "
  (let ((defstruct-name (make-sym "deftemplate/" name))
	(defstruct-constructor (make-sym "make-deftemplate/" name)))
    `(progn
       (defstruct ,defstruct-name
	 ,@(mapcar #'macroexpand-1 slots))
     
       (defmacro ,name (&rest slots)
	 (call-defstruct-constructor ',defstruct-constructor slots)))))


;;; defrule
;;;
;;; ---
(defmacro compile-lhs (name &body lhs)
  `(progn
     (setf variable-bindings '())
     (setf fact-bindings '())
     (setf current-rule ',name)
     (parse ,name ,@lhs)))
	   
(defun make-variable-binding (binding)
  `(,(car binding) (,(make-sym "DEFTEMPLATE/" (cadr binding) "-" (caddr binding)) ,(cadddr binding))))

(defun make-fact-binding (binding)
  (let ((variable (car binding))
	(position (cadr binding)))
    `(,variable (nth ,position token))))

(defmacro compile-rhs (name &body rhs)
  (when (null rhs)
    (setf rhs '(t)))
  `(defun ,(make-sym "RHS/" name) (activation)
     (let* ((token (activation-token activation))
	    ,@(mapcar #'make-fact-binding (reverse fact-bindings))
	    ,@(mapcar #'make-variable-binding (reverse variable-bindings)))
       ,@rhs)))

(defmacro defrule (name &body body)
  "One of the primary methods of representing knowledge in CLIPS is a
   rule. A rule is a collection of conditions and the actions to be
   taken if the conditions are met."
  (let ((rhs (cdr (member '=> body)))
	(lhs (ldiff body (member '=> body))))
    `(progn
       (compile-lhs ,name ,@lhs)
       (compile-rhs ,name ,@rhs))))

(defun variable-p (sym)
  "Return T if <sym> is a variable (starts with $? or ?) otherwise NIL."
  (and (symbolp sym)
       (or (and (eq (char (string sym) 0) #\$)
		(eq (char (string sym) 1) #\?))
	   (eq (char (string sym) 0) #\?))))

(defmacro parse (name &rest conditional-elements)
  (unless (eq (car conditional-elements) 'nil)
    (cond ((consp (car conditional-elements))
	   `(progn
	      (parse-ce ,name ,(car conditional-elements))
	      (parse ,name ,@(cdr conditional-elements))))
	  ((variable-p (car conditional-elements))
	   (progn
	     (cl:assert (eq (cadr conditional-elements) '<-))
	     `(progn
		(parse-assigned-pattern-ce ,name ,(car conditional-elements) ,(caddr conditional-elements))
		(parse ,name ,@(cdddr conditional-elements))))))))

(defmacro parse-ce (name conditional-element)
  (let ((ce-type (car conditional-element)))
    (case ce-type
      (otherwise `(parse-pattern-ce ,name ,conditional-element)))))

(defmacro parse-assigned-pattern-ce (name variable pattern-ce)
  `(parse-pattern-ce ,name ',pattern-ce ',variable))

(defun contains-connective-constraints? (sym)
  (or (position #\& (symbol-name sym))
      (position #\~ (symbol-name sym))
      (position #\| (symbol-name sym))))    

(defmacro parse-pattern-ce (name pattern-ce &optional (binding (gensym) explicitly-bound))
  (declare (ignore name))
  `(progn
     ;; Update bindings
     (push (list (if ,explicitly-bound ,binding ',binding) (length fact-bindings)) fact-bindings)
     (dolist (slot (if ,explicitly-bound (cdr ,pattern-ce) (cdr ',pattern-ce)))
       (let ((value (cadr slot))
	     (slot-name (car slot))
	     (template (if ,explicitly-bound (car ,pattern-ce) (car ',pattern-ce))))
	 (when (variable-p value)
	   (when (contains-connective-constraints? value)
	     (do* ((pos (contains-connective-constraints? value) (contains-connective-constraints? val))
		   (prev 0 (contains-connective-constraints? val))
		   (val value (subseq val prev pos)))
		  (pos t)
	       (print val)))
	   (push (list value template slot-name (if ,explicitly-bound ,binding ',binding)) variable-bindings))))))
