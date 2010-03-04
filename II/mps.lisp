;;;; Minimal Production System II

;; Helper methods

(defun variablep (sym)
  "Returns T if <sym> is a variable (starts with ?) otherwise NIL."
  (and (symbolp sym)
       (eq (char (string sym) 0) #\?)))

(defun sym (&rest parts)
  "Constructs and interns a symbol by concatenating <parts>."
  (let ((result ""))
    (dolist (part parts)
      (setf result (string-upcase (format nil "~A~A" result part))))
    (intern result)))

;; Compile time temporary data. These variables holds fact and variable bindings
;; that need to be accessed at macroexpansion time

(defparameter *fact-bindings* nil)
(defparameter *variable-bindings* nil)

;; Compile time session data. This variables hold the dispatch information for
;; the object type node (aka bus node in Forgy's thesis). The object type node
;; is reconstructed every time a new rule is defined.

(defvar *object-type-node* (make-hash-table))

;; Core data structures. This variable holds all memories.

(defvar *memory* (make-hash-table))
(defvar *activations* (make-hash-table))

;; Macros. These are the building blocks of the MPS rule language and they
;; expand into a bunch of defuns that represent the Rete network of the rules.

(defmacro defrule (name &body body)
  (let* ((rhs (member '=> body))
	 (lhs (ldiff body rhs)))
    (setf *fact-bindings* (make-hash-table))
    (setf *variable-bindings* (make-hash-table))
    `(progn
       (compile-lhs ,name ,@lhs)
       (compile-rhs ,name ,@(cdr rhs)))))

(defmacro compile-lhs (name &rest conditional-elements)
  (let ((result '())
	(index 0))
    (dolist (ce conditional-elements)
      (incf index)
      (case (car ce) ;; Dispatch on CE type (not, test and pattern)
	(not (push `(compile-not-ce ,name ,index ,(cdr ce)) result))
	(test (push `(compile-test-ce ,name ,index ,(cdr ce)) result))
	(otherwise
	 (progn
	   ;; If a CE starts with a variable it is assumed to be a fact binding.
	   ;; NOTE! The <- operator which is used in MPS is not available.
	   ;; ?foo <- (foo ...) in MPS is written as (?foo (foo ...)) in MPS II.
	   (when (variablep (car ce))
	     (setf (gethash (car ce) *fact-bindings*)
		   `(,(car ce) (nth ,index token)))
	     (setf ce (cdr ce))) ; make sure that we only pass on the actual CE
	   (push `(compile-pattern-ce ,name ,index ,ce) result)))))
    `(progn
       ,@result
       (make-object-type-node) ; regenerate the object-type-node defun
       (make-production-node ',name ,(+ index 1)))))

(defun make-object-type-node ()
  (let ((body '()))
    (maphash #'(lambda (key value)
		 (dolist (v value)
		   (push `(,key (,v fact)) body)))
	     *object-type-node*)
    (print `(defun object-type-node (&rest facts)
	      (dolist (fact facts)
		(case (type-of fact)
		  ,@body))))))

(defun make-production-node (name index)
  (print `(defun ,(sym name index "-left") (key token timestamp)
	    (store-activation key token timestamp))))

(defmacro compile-not-ce (name index conditional-elements)
  `(let ((not-node (compile-lhs ,(sym name index)
				,@conditional-elements)))
     (magic-happens-here ,name ,index)))

(defun make-not-node (name index conditional-elements)
  (declare (ignore name index conditional-elements))
  (print t))

(defmacro compile-test-ce (name index test-form)
  `(make-test-node ',name ,index ,test-form)
  `(make-beta-node ',name ,index ,t))

(defun make-test-node (name index test-form)
  (print `(defun ,(sym name index "-left") (key token timestamp)
	    (let (,@(expand-variable-bindings))
	      (when ,test-form
		(store key token ,(sym name index "-alpha-memory"))
		(,(sym name (+ index 1) "-left") key token timestamp))))))

(defmacro compile-pattern-ce (name index conditional-element)
  (multiple-value-bind (slot-constraint join-constraint)
      (extract-constraints (cdr conditional-element))
    (unless (member (sym name index "-right") 
		    (gethash (car conditional-element) *object-type-node* '()))
      (push (sym name index "-right")
	    (gethash (car conditional-element) *object-type-node* '())))
    `(progn
       (make-alpha-node ',name ,index ',slot-constraint)
       (make-beta-node ',name ,index ',join-constraint))))

(defun extract-constraints (conditional-element)
  (let ((slot-constraint '())
	(join-constraint '()))
    (dolist (slot conditional-element)
      (let ((slot-name (car slot))
	    (slot-value (cadr slot))
	    (slot-constraint (caddr slot)))))
;	(cond ((variablep slot-value)
;	       (let ((binding (gethash slot-value *variable-bindings*)))
;		 (when (and binding (
;		   (if (
;		   (if 
	(values slot-constraint t)))

(defun make-alpha-node (name index slot-constraint)
  (print `(defun ,(sym name index) (key fact timestamp)
	    (when ,slot-constraint
	      (store key token ',(sym name index "-alpha-memory"))
	      (,(sym name index "-right") key token timestamp)))))

(defun make-beta-node (name index join-constraints)
  (let ((left `(defun ,(sym name index "-left") (key tok timestamp)
		 (dolist (fact (contents-of ,(sym name (- index 1) "-alpha-memory")))
		   (let* ((token (append tok (list fact)))
			  ,@(expand-variable-bindings))
		   (when ,join-constraints
		     (store key token ,(sym name index "-beta-memory"))
		     (,(sym name (+ index 1) "-left") key token timestamp))))))
	(right `(defun ,(sym name index "-right") (key fact timestamp)
		  (dolist (tok (contents-of ,(sym name (- index 1) "-beta-memory")))
		    (let* ((token (append tok (list fact)))
			   ,@(expand-variable-bindings))
		      (when ,join-constraints
			(store key token ,(sym name index "-beta-memory"))
			(,(sym name (+ index 1) "-left") key token timestamp)))))))
    (print `(progn
	      ,left
	      ,right))))

(defun expand-variable-bindings ()
  (let ((result '()))
    (maphash #'(lambda (k v)
		 (declare (ignore k))
		 (push v result)) *variable-bindings*)
    (maphash #'(lambda (k v)
		 (declare (ignore k))
		 (push v result)) *fact-bindings*)
    result))

(defmacro compile-rhs (name &rest expressions)
  `(print '(compile-rhs ,name ,@expressions)))
      
    