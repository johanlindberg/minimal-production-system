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

;; Macros. These are the building blocks of the MPS rule language and they
;; expand into a bunch of function definitions and function calls that maintain
;; current state of the compilation.

(defmacro defrule (name &body body)
  (let* ((rhs (member '=> body))
	 (lhs (ldiff body rhs)))
    `(let ((bindings (make-hash-table))
	   (previous-node 'nil))
       (compile-lhs ,name ,@lhs)
       (compile-rhs ,name ,@(cdr rhs)))))

(defmacro compile-lhs (name &rest conditional-elements)
  (let ((result '())
	(index 0))
    (dolist (ce conditional-elements)
      (case (car ce)
	(not (push `(compile-not-ce ,name ,(incf index) ,(cdr ce)) result))
	(test (push `(compile-test-ce ,name ,(incf index) ,(cdr ce)) result))
	(otherwise (push `(compile-pattern-ce ,name ,(incf index) ,ce) result))))
    `(progn
       ,@result
       (make-production-node ,name ,(incf index)))))

(defmacro compile-not-ce (name index conditional-elements)
  `(let ((not-node (compile-lhs ,(sym name index)
				,@conditional-elements)))
     (magic-happens-here ,name ,index)))

(defun make-not-node (name index conditional-elements)
  (print t))

(defmacro compile-test-ce (name index test-form)
  `(make-test-node ,name ,index ,test-form))

(defun make-test-node (name index test-form)
  (print `(defun ,(sym name index) (key token timestamp)
	    (let (,@(expand-variable-bindings))
	      (when ,test-form
		(store key token ,(sym "MEMORY/" name index))
		(,(sym name (+ index 1)) key token timestamp))))))

(defmacro compile-pattern-ce (name index conditional-element)
  `(progn
     (unless (gethash ',(car conditional-element) *object-type-node*)
       (setf (gethash ',(car conditional-element) *object-type-node*)
	     ',(sym name index)))
     (make-alpha-node ,name ,index ,conditional-element)
     (make-beta-node ,name ,index)))

(defmacro compile-rhs (name &rest expressions)
  `(print '(compile-rhs ,name ,@expressions)))
      
    