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

(defmacro emit (&body body)
  `(progn
     (print ,@body)
     (eval ,@body)))

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
       (make-production-node ',production-node-name)
       (compile-lhs ,name ,production-node-name ,@lhs)
       (make-object-type-node) ; regenerate the object-type-node defun
       (compile-rhs ,name ,@(cdr rhs)))))

(defmacro compile-lhs (name end-node-name &rest conditional-elements)
  (let ((result '())
	(next-node-name nil)
	(index (- (length conditional-elements) 1)))
    (dolist (ce (reverse conditional-elements))
      (if (eq index (- (length conditional-elements) 1))
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
      (decf index))
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
    (emit `(defun object-type-node (&rest facts)
	     (dolist (fact facts)
	       (case (type-of fact)
		 ,@body))))))

(defun make-production-node (name)
  (emit `(defun ,(sym name "-left") (key token timestamp)
	   (store-activation key token timestamp))))

(defmacro compile-not-ce (name index next conditional-elements)
  `(progn
     (compile-lhs ,(sym name index)
		  ,(sym name index "-right")
		  ,@conditional-elements)
     (make-not-node ',name ,index ',next t)))

(defun make-not-node (name index next join-constraints)
  (let ((left `(defun ,(sym name index "-left") (key tok timestamp)
		 (if (eq (length (contents-of ',(sym name (- index 1) "-alpha-memory"))) 0)
		     (let ((token (append tok (list nil))))
		       (store key token ',(sym name index "-beta-memory"))
		       (,(sym next "-left") key token timestamp))
		     (let ((propagate-token t))
		       (dolist (fact (contents-of ',(sym name (- index 1) "-alpha-memory")))
			 (let ((token (append tok (list fact))))
			   (when ,join-constraints
			     (setf propagate-token nil))))
		       (when propagate-token
			 (let ((token (append tok (list nil))))
			   (store key token ',(sym name index "-beta-memory"))
			   (,(sym next "-left") key token timestamp)))))))
	(right `(defun ,(sym name index "-right") (key fact timestamp)
		  (dolist (tok (contents-of ',(sym name (- index 1) "-beta-memory")))
		    (let ((token (append tok (list fact))))
		      (when ,join-constraints
			(multiple-value-bind (new-count old-count)
			    (update-count key token ',(sym name index "-not-memory"))
			  (store key token ',(sym name index "-beta-memory"))
			  (cond ((and (eq new-count 0)
				      (eq old-count 1)
				      (eq key '-))
				 (,(sym next "-left") '+ token timestamp))
				((and (eq new-count 1)
				      (or (eq old-count 0)
					  (eq old-count nil))
				      (eq key '+))
				 (,(sym next "-left") '- token timestamp))))))))))
    (emit (if (eq index 0)
	      `(progn ,right)
	      `(progn
		 ,left
		 ,right)))))
  
(defmacro compile-test-ce (name index next test-form)
  `(make-test-node ',name ,index ',next ,test-form))

(defun make-test-node (name index next test-form)
  (emit `(defun ,(sym name index "-left") (key token timestamp)
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
		    (push `(equalp (,(cadr existing-binding)
				     (nth ,(caddr existing-binding) token))
				   (,slot-accessor (nth ,index token)))
			  slot-constraints)
		    (push `(equalp (,(cadr existing-binding)
				     (nth ,(caddr existing-binding) token))
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

    (values `(and ,@slot-constraints)
	    `(and ,@join-constraints))))

(defun make-alpha-node (name index slot-constraint)
  (emit `(defun ,(sym name index) (key fact timestamp)
	   (let (,@(expand-fact-bindings index))
	     (when ,slot-constraint
	       (store key fact ',(sym name index "-alpha-memory"))
	       (,(sym name index "-right") key fact timestamp))))))

(defun make-beta-node (name index next join-constraints)
  (let ((left `(defun ,(sym name index "-left") (key tok timestamp)
		 (dolist (fact (contents-of ,(sym name (- index 1) "-alpha-memory")))
		   (let* ((token (append tok (list fact))))
		     (when ,join-constraints
		       (store key token ',(sym name index "-beta-memory"))
		       (,(sym next "-left") key token timestamp))))))
	(right `(defun ,(sym name index "-right") (key fact timestamp)
		  (dolist (tok (contents-of ,(sym name (- index 1) "-beta-memory")))
		    (let* ((token (append tok (list fact))))
		      (when ,join-constraints
			(store key token ',(sym name index "-beta-memory"))
			(,(sym next "-left") key token timestamp)))))))
    (emit (if (eq index 0)
	      `(progn ,right)
	      `(progn
		 ,left
		 ,right)))))

(defmacro store-activation (key token memory)
  `(store ,key ,token ,memory *activations*))

(defun store (key token memory &optional (table *memory*))
  (if (eq key '+)
      (if (gethash memory table)
	  (unless (member token (gethash memory table) :test #'equalp)
	    (push token (gethash memory table)))
	  (setf (gethash memory table) (list token)))
      ;; Remove token
      (when (gethash memory table)
	(setf (gethash memory table) (remove-if #'(lambda (item)
						    (equalp item token))
						(gethash memory table))))))

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
  (emit `(defun ,(sym name "-rhs") (token)
	   (let (,@(expand-variable-bindings))
	     ,@body))))