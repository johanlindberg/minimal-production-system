;;; Minimal Production System (MPS)

(defpackage :mps
  (:use :common-lisp)
  (:export :defrule
	   :agenda :assert-fact	:breadth :clear
	   :depth :facts :get-strategy :load
	   :reset :run :set-strategy)
  (:shadow :assert))
(in-package :mps)

(defmacro ppexp (&body body)
       `(pprint (macroexpand-1 ',@body)))

;;; Structures and parameters
(defstruct activation
  rule
  salience token timestamp
  rhs-func prod-mem)

(defparameter variable-bindings '())
(defparameter fact-bindings '())

;;; Helper methods

(defun as-keyword (sym)
  "Returns <sym> as a keyword."
  (intern (string-upcase sym) :keyword))

(defun make-sym (&rest parts)
  "Makes a symbol of <parts>."
  (let ((sym ""))
    (dolist (part (mapcar #'string-upcase (mapcar #'string parts)))
      (setf sym (concatenate 'string sym part)))
    (intern sym)))

(defun variable-p (sym)
  "Return T if <sym> is a variable (starts with $? or ?) otherwise NIL."
  (and (symbolp sym)
       (or (and (eq (char (string sym) 0) #\$)
		(eq (char (string sym) 1) #\?))
	   (eq (char (string sym) 0) #\?))))

;; Stolen from the Common Lisp Cookbook. See
;; http://cl-cookbook.sourceforge.net/strings.html
(defun split (string &optional (delimiter #\SPACE))
  "Splits <string> into pieces separated by <delimiter>."
  (loop for i = 0 then (1+ j)
     as j = (position delimiter string :start i)
     collect (subseq string i j)
     while j))


;;; defrule
(defmacro defrule (name &body body)
  (declare (ignore docstring))
  (let ((rhs (cdr (member '=> body)))
	(lhs (ldiff body (member '=> body))))
    `(progn
       (compile-lhs ,name ,@lhs)
       (compile-rhs ,name ,@rhs))))

;; defrule - LHS
(defmacro compile-lhs (rule-name &body lhs)
  `(progn
     (setf variable-bindings '())
     (setf fact-bindings '())
     (parse ,rule-name ,@lhs)))

(defmacro parse (rule-name &rest conditional-elements)
  (unless (eq (car conditional-elements) 'nil)
    (cond ((consp (car conditional-elements))
	   `(progn
	      (parse-ce ,rule-name ,(car conditional-elements))
	      (parse ,rule-name ,@(cdr conditional-elements))))
	  ((variable-p (car conditional-elements))
	   (progn
	     (cl:assert (eq (cadr conditional-elements) '<-))
	     `(progn
		(parse-pattern-ce ,rule-name ,(car conditional-elements) ,(caddr conditional-elements))
		(parse ,rule-name ,@(cdddr conditional-elements))))))))

(defmacro parse-ce (rule-name conditional-element)
  (let ((ce-type (car conditional-element)))
    (case ce-type
      (not `(parse-not-ce ,rule-name ,conditional-element)) ; TBD
      (test `(parse-test-ce ,rule-name ,conditional-element)) ; TBD
      (otherwise `(parse-pattern-ce ,rule-name ,(gensym) ,conditional-element)))))

(defmacro parse-not-ce (rule-name variable pattern-ce)
  (declare (ignore rule-name))
  (print (list 'not variable pattern-ce)))

(defmacro parse-test-ce (rule-name variable pattern-ce)
  (declare (ignore rule-name))
  (print (list 'test variable pattern-ce)))

(defmacro parse-pattern-ce (rule-name variable pattern-ce)
  (declare (ignore rule-name))
  (let ((defstruct-name (car pattern-ce)))
    `(progn
       ;; Update bindings
       (push (list ',variable (length fact-bindings)) fact-bindings)
       (generate-network-nodes ',defstruct-name ',pattern-ce ',variable))))

(defun generate-network-nodes (defstruct-name conditional-element variable)
  (let* ((slot (cadr conditional-element))
	 (slot-name (car slot))
	 (slot-value (cadr slot)))
    ;; Generate a new node for each &-constraint, ~ and / are handled within the
    ;; nodes. (fact (foo ?foo&~1&~2)) expands into two alpha nodes: fact-foo-is-
    ;; not-1 and fact-foo-is-not-2.
    (dolist (constraint (split (symbol-name slot-value) #\&))
      (let ((part (intern (string-upcase constraint))))
	(if (variable-p part)
	    (push (list part defstruct-name slot-name variable) variable-bindings)
	    (eval (make-node defstruct-name slot-name part)))))))

(defun make-node (defstruct-name slot-name pattern-constraint)
  (let* ((or-constraint (position #\| (symbol-name pattern-constraint)))
	 (not-constraint (position #\~ (symbol-name pattern-constraint)))
	 (not-constraint-value (subseq (symbol-name pattern-constraint) (+ not-constraint 1))))
    (cond
      (or-constraint
       (let ((function-name (make-sym "alpha/" defstruct-name "-" slot-name))
	     (constraint '()))
	 (dolist (constraint (split (symbol-name pattern-constraint) #\/))
	   (let* ((partial-constraint (intern (string-upcase constraint)))
		  (partial-not-constraint (position #\~ (symbol-name partial-constraint)))
		  (partial-not-constraint-value (subseq (symbol-name partial-constraint) (+ partial-not-constraint 1))))
	     (print (list partial-constraint partial-not-constraint partial-not-constraint-value))
	     (if partial-not-constraint
		 (progn
		   (push `(not (eq (,(make-sym defstruct-name "-" slot-name) fact)
				   ,(read-from-string partial-not-constraint-value))) constraint)
		   (setf function-name (concatenate 'string function-name "-is-not-" partial-not-constraint-value "-or")))
		 (progn
		   (push `(eq (,(make-sym defstruct-name "-" slot-name) fact)
			      ,(read-from-string partial-not-constraint-value)) constraint)
		   (setf function-name (concatenate 'string function-name "-is-" partial-not-constraint-value "-or"))))))
	 ; Remove the last "-or" from function-name
	 (print function-name)
	 (setf function-name (subseq function-name 0 (- (length function-name) 3)))
	 (print function-name)
	 `(defun ,function-name (key fact timestamp)
	    (when (or ,constraint)
	      (unless (consp fact)
		(setf fact (list fact)))
	      (store key fact ',(make-sym "memory/" function-name))
	      (propagate key fact timestamp ',function-name)))))

      (not-constraint
       `(defun ,(make-sym "alpha/" defstruct-name "-" slot-name "-is-not-" not-constraint-value) (key fact timestamp)
	  (when (not (eq (,(make-sym defstruct-name "-" slot-name) fact)
			 ,(read-from-string not-constraint-value)))
	    (unless (consp fact)
	      (setf fact (list fact)))
	    (store key fact ',(make-sym "memory/alpha/" defstruct-name "-" slot-name "-is-not-" not-constraint-value))
	    (propagate key fact timestamp ',(make-sym "alpha/" defstruct-name "-" slot-name "-is-not-" not-constraint-value)))))

      (t
       `(defun ,(make-sym "alpha/" defstruct-name "-" slot-name "-is-" not-constraint-value) (key fact timestamp)
	  (when (eq (,(make-sym defstruct-name "-" slot-name) fact)
		    ,(read-from-string not-constraint-value))
	    (unless (consp fact)
	      (setf fact (list fact)))
	    (store key fact ',(make-sym "memory/alpha/" defstruct-name "-" slot-name "-is-" not-constraint-value))
	    (propagate key fact timestamp ',(make-sym "alpha/" defstruct-name "-" slot-name "-is-" not-constraint-value))))))))



;; defrule - RHS
(defun make-variable-binding (binding)
  `(,(car binding) (,(make-sym (cadr binding) "-" (caddr binding)) ,(cadddr binding))))

(defun make-fact-binding (binding)
  (let ((variable (car binding))
	(position (cadr binding)))
    `(,variable (nth ,position token))))

(defmacro compile-rhs (rule-name &body rhs)
  (when (null rhs)
    (setf rhs '(t)))
  `(defun ,(make-sym "RHS/" rule-name) (activation)
     (let* ((token (activation-token activation))
	    ,@(mapcar #'make-fact-binding (reverse fact-bindings))
	    ,@(mapcar #'make-variable-binding (reverse variable-bindings)))
       ,@rhs)))

