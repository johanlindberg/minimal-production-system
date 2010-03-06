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

;; Temporary data (used at macroexpansion time).

(defparameter *fact-bindings* nil)
(defparameter *variable-bindings* nil)

(defvar *object-type-node* (make-hash-table))

;; Runtime data (core).

(defvar *memory* (make-hash-table))
(defvar *activations* (make-hash-table))

;; Macros. These are the building blocks of the MPS rule language and they
;; expand into a bunch of defuns that represent the Rete network of the rules.

(defmacro defrule (name &body body)
  (let* ((rhs (member '=> body))
	 (lhs (ldiff body rhs))
	 (production-node-name (sym name "-production")))
    (setf *fact-bindings* (make-hash-table))
    (setf *variable-bindings* (make-hash-table))
    `(progn
       (compile-lhs ,name ,production-node-name ,@lhs)
       (make-object-type-node) ; regenerate the object-type-node defun
       (make-production-node ',production-node-name)
       (compile-rhs ,name ,@(cdr rhs)))))

(defmacro compile-lhs (name end-node-name &rest conditional-elements)
  (let ((result '())
	(next-node-name nil)
	(index 0))
    (dolist (ce conditional-elements)
      (if (eq index (length conditional-elements))
	  (setf next-node-name end-node-name)
	  (setf next-node-name (sym name (+ index 1))))

      (case (car ce) ;; Dispatch on CE type (not, test and pattern)
	(not
	 (push `(compile-not-ce ,name ,index ,next-node-name ,(cdr ce)) result))
	(test
	 (push `(compile-test-ce ,name ,index ,next-node-name ,(cdr ce)) result))
	(otherwise
	 (progn
	   ;; If a CE starts with a variable it is assumed to be a fact binding.
	   ;; NOTE! The <- operator which is used in MPS is not available.
	   ;; ?foo <- (foo ...) in MPS is written as (?foo (foo ...)) in MPS II.
	   (when (variablep (car ce))
	     (setf (gethash (car ce) *fact-bindings*)
		   `(,(car ce) (nth ,index token)))
	     (setf ce (cadr ce))) ; make sure that we only pass on the actual CE
	   (push `(compile-pattern-ce ,name ,index ,next-node-name ,ce) result))))
      (incf index))

    `(progn
       ,@result)))

(defun make-object-type-node ()
  (let ((body '()))
    (maphash #'(lambda (key value)
		 (let ((result '()))
		   (dolist (v value)
		     (push `(,v fact) result))
		   (push `(,key (progn ,@result)) body)))
	     *object-type-node*)
    (print `(defun object-type-node (&rest facts)
	      (dolist (fact facts)
		(case (type-of fact)
		  ,@body))))))

(defun make-production-node (name)
  (print `(defun ,(sym name "-left") (key token timestamp)
	    (store-activation key token timestamp))))

(defmacro compile-not-ce (name index next conditional-elements)
  `(progn
     (compile-lhs ,(sym name index)
		  ,(sym name index "-right")
		  ,@conditional-elements)
     (make-not-node ',name ,index ',next t)))

(defun make-not-node (name index next join-constraints)
  (let ((left `(defun ,(sym name index "-left") (key tok timestamp)
		 (dolist (fact (contents-of ,(sym name (- index 1) "-alpha-memory")))
		   (let* ((token (append tok (list fact)))
			  ,@(expand-variable-bindings))
		   (when ,join-constraints
		     (store key token ,(sym name index "-beta-memory"))
		     (,(sym next "-left") key token timestamp))))))
	(right `(defun ,(sym name index "-right") (key fact timestamp)
		  (dolist (tok (contents-of ,(sym name (- index 1) "-beta-memory")))
		    (let* ((token (append tok (list fact)))
			   ,@(expand-variable-bindings))
		      (when ,join-constraints
			(store key token ,(sym name index "-beta-memory"))
			(,(sym next "-left") key token timestamp)))))))
    (print (if (eq index 0)
	       `(progn ,right)
	       `(progn
		  ,left
		  ,right)))))
  
(defmacro compile-test-ce (name index next test-form)
  `(make-test-node ',name ,index ',next ,test-form))

(defun make-test-node (name index next test-form)
  (print `(defun ,(sym name index "-left") (key token timestamp)
	    (let (,@(expand-variable-bindings))
	      (when ,test-form
		(store key token ,(sym name index "-alpha-memory"))
		(,(sym next "-left") key token timestamp))))))

(defmacro compile-pattern-ce (name index next conditional-element)
  (multiple-value-bind (slot-constraint join-constraint)
      (extract-constraints index conditional-element)
    (unless (member (sym name index)
		    (gethash (car conditional-element) *object-type-node* '()))
      (push (sym name index)
	    (gethash (car conditional-element) *object-type-node* '())))
    `(progn
       (make-alpha-node ',name ,index ',slot-constraint)
       (make-beta-node ',name ,index ',next ',join-constraint))))

(defun extract-constraints (index conditional-element)
  (let ((slot-constraints '())
	(join-constraints '())
	(defstruct-name (car conditional-element)))
    (dolist (slot (cdr conditional-element))
      (let* ((slot-name (car slot))
	     (slot-value (cadr slot))
	     (slot-constraint (caddr slot))
	     (slot-accessor (sym defstruct-name "-" slot-name))
	     (existing-binding (gethash slot-value *variable-bindings* '())))
	(if (variablep slot-value)
	    ;; slot ::= (name variable constraint)
	    (if existing-binding
		(if (eq index (caddr existing-binding))
		    (push `(equalp ,(cadr existing-binding)
				   (,slot-accessor (nth ,index token)))
			  slot-constraints)
		    (push `(equalp ,(cadr existing-binding)
				   (,slot-accessor (nth ,index token)))
			  join-constraints))
		(setf (gethash slot-value *variable-bindings*)
		      `(,slot-value ,slot-accessor ,index)))
	    ;; slot ::= (name constant constraint)
	    (push `(equalp ',slot-value
			   (,slot-accessor (nth ,index token)))
		  slot-constraints))

	(when slot-constraint
	  (push slot-constraint slot-constraints))))

    (unless join-constraints
      (setf join-constraints `(t)))
    (values `(and ,@slot-constraints)
	    `(and ,@join-constraints))))

(defun make-alpha-node (name index slot-constraint)
  (print `(defun ,(sym name index) (key fact timestamp)
	    (let (,@(expand-fact-bindings index))
	      (when ,slot-constraint
		(store key token ',(sym name index "-alpha-memory"))
		(,(sym name index "-right") key token timestamp))))))

(defun make-beta-node (name index next join-constraints)
  (let ((left `(defun ,(sym name index "-left") (key tok timestamp)
		 (dolist (fact (contents-of ,(sym name (- index 1) "-alpha-memory")))
		   (let* ((token (append tok (list fact)))
			  ,@(expand-variable-bindings))
		   (when ,join-constraints
		     (store key token ,(sym name index "-beta-memory"))
		     (,(sym next "-left") key token timestamp))))))
	(right `(defun ,(sym name index "-right") (key fact timestamp)
		  (dolist (tok (contents-of ,(sym name (- index 1) "-beta-memory")))
		    (let* ((token (append tok (list fact)))
			   ,@(expand-variable-bindings))
		      (when ,join-constraints
			(store key token ,(sym name index "-beta-memory"))
			(,(sym next "-left") key token timestamp)))))))
    (print (if (eq index 0)
	       `(progn ,right)
	       `(progn
		  ,left
		  ,right)))))

(defun expand-fact-bindings (index)
  (let ((result '()))
    (maphash #'(lambda (k v)
		 (declare (ignore k))
		 (when (eq (caddr v) index)
		   (push `(,(car v) (,(cadr v) fact)) result)))
	     *variable-bindings*)
    result))

(defun expand-variable-bindings ()
  (let ((result '()))
    (maphash #'(lambda (k v)
		 (declare (ignore k))
		 (push `(,(car v) (,(cadr v) (nth ,(caddr v) token))) result))
	     *variable-bindings*)
    (maphash #'(lambda (k v)
		 (declare (ignore k))
		 (push v result))
	     *fact-bindings*)
    result))

(defmacro compile-rhs (name &rest body)
  `(make-rhs-node ',name ',body))

(defun make-rhs-node (name body)
  (print `(defun ,(sym name "-rhs") (token)
	    (let (,@(expand-variable-bindings))
	      ,@body))))