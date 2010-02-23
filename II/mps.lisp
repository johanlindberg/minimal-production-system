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
      (setf result (format nil "~A~A" result (string-upcase part))))
    (intern result)))


(defmacro defrule (name &body body)
  (let* ((rhs (member '=> body))
	 (lhs (ldiff body rhs)))
    `(progn
       (compile-lhs ,name ,@lhs)
       (compile-rhs ,name ,@rhs))))

(defmacro compile-lhs (name &rest conditional-elements)
  (let ((result '())
	(index 0))
    (dolist (conditional-element conditional-elements)
      (case (car conditional-element)
	(not (push `(compile-not-ce ,name ,(incf index) ,(cdr conditional-element)) result))
	(test (push `(compile-test-ce ,name ,(incf index) ,(cdr conditional-element)) result))
	(otherwise (push `(compile-pattern-ce ,name ,(incf index) ,(cdr conditional-element)) result))))
    `(progn ,@result)))

(defmacro compile-ce (name index conditional-element)
  `(print '(compile-ce ,name ,index ,conditional-element)))

(defmacro compile-rhs (name &rest expressions)
  `(print '(compile-rhs ,name ,@expressions)))
      
    