

; (fact (foo ?foo&~1&~2))
; (fact (bar ?foo&~3&~4))
;

(defun split (string &optional (delimiter #\SPACE))
  (loop for i = 0 then (1+ j)
     as j = (position delimiter string :start i)
     collect (subseq string i j)
     while j))

(defun variable-p (sym)
  "Return T if <sym> is a variable (starts with $? or ?) otherwise NIL."
  (and (symbolp sym)
       (or (and (eq (char (string sym) 0) #\$)
		(eq (char (string sym) 1) #\?))
	   (eq (char (string sym) 0) #\?))))

(defun make-sym (&rest parts)
  (let ((sym ""))
    (dolist (part (mapcar #'string-upcase (mapcar #'string parts)))
      (setf sym (concatenate 'string sym part)))
    (intern sym)))

(defun make-node (deftemplate-name slot-name pattern-constraint)
  (let ((p (position #\~ (symbol-name pattern-constraint))))
    (cond (p
	   `(defun ,(make-sym deftemplate-name "-"
			      slot-name "-is-not-"
			      (subseq (symbol-name pattern-constraint) (+ p 1))) (key fact timestamp)
	      (when (not (eq (,(make-sym deftemplate-name "-" slot-name) fact) ,(read-from-string (subseq (symbol-name pattern-constraint) (+ p 1)))))
		(print (list key fact timestamp)))))
	  (t
	   `(defun ,(make-sym deftemplate-name "-"
			      slot-name "-is-"
			      (subseq (symbol-name pattern-constraint) p)) (key fact timestamp)
	      (when (not (eq (,(make-sym deftemplate-name "-" slot-name) fact) ,(read-from-string (subseq (symbol-name pattern-constraint) p))))
		(print (list key fact timestamp))))))))

(defun generate-network-nodes (deftemplate-name slot)
  (let ((slot-name (car slot))
	(slot-value (cadr slot)))
    (dolist (constraint (split (symbol-name slot-value) #\&))
      (let ((part (intern (string-upcase constraint))))
	(unless (variable-p part)
	  (print part)
	  (eval (make-node deftemplate-name slot-name part)))))))

(defun parse-pattern-ce (pattern-ce)
  (let ((deftemplate-name (car pattern-ce)))
    (dolist (slot (cdr pattern-ce))
      (generate-network-nodes deftemplate-name slot))))
	