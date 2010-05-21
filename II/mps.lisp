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

(defpackage :MPS
  (:use :cl)
  (:export "=>"           ; symbols

	   :assert-facts  ; public API
	   :retract-facts
	   :run           ; TBD

	   :defrule

	   :agenda
	   :clear
	   :facts
	   :modify-fact
	   :reset
	   
	   :deffacts))
(in-package :MPS)

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

;; Compilation data.

(defparameter *fact-bindings* nil)
(defparameter *variable-bindings* nil)

;; Runtime data.

(defvar *memory* (make-hash-table :test #'equalp)) ; node memories
(defvar *working-memory* (make-hash-table :test #'equalp))

(defvar *activations* (make-hash-table :test #'equalp))
(defvar *object-type-node* (make-hash-table))

(defvar *defrules* '())
(defvar *deffacts* '())

(defvar *current-timestamp* 0)
(defvar *current-fact-index* 0)

(defstruct activation
  rule
  salience
  token
  timestamp)

(defmacro emit (&body body)
  `(progn
     (print ,@body)
     (eval ,@body)))

(defun make-object-type-node ()
  (let ((body '())
	(func `(defun object-type-node (key timestamp &rest facts) ; dummy impl
		 (declare (ignore key timestamp facts)))))
    (when (> (hash-table-count *object-type-node*) 0)
      (maphash #'(lambda (key value)
		   (let ((result '()))
		     (dolist (v value)
		       (push `(,v key fact timestamp) result))
		     (push `(,key (progn ,@result)) body)))
	       *object-type-node*)
      (setf func `(defun object-type-node (key timestamp &rest facts)
		    (dolist (fact facts)
		      (case (type-of fact)
			,@body)))))
    (emit func)))
(make-object-type-node) ; wrap this in (eval-when ...) ?

;; Memory access

(defun contents-of (memory &optional (table *memory*))
  "Returns the contents of <memory>."
  (gethash memory table))

(defun store-activation (key token timestamp rule salience)
  (let ((activation (make-activation :rule rule
				     :salience salience
				     :token token
				     :timestamp timestamp)))
    (if (eq key '+)
	;; Add token
	(if (gethash salience *activations*)
	    (unless (member activation (gethash salience *activations*) :test #'equalp)
	      (push activation (gethash salience *activations*)))
	    (setf (gethash salience *activations*) (list activation)))
	;; Remove token
	(when (gethash salience *activations*)
	  (setf (gethash salience *activations*)
		(remove-if #'(lambda (item)
			       (and (equalp (activation-rule item) rule)
				    (equalp (activation-token item) token)))
			   (gethash salience *activations*)))))))

(defun store (key token memory)
  (if (eq key '+)
      ;; Add token
      (if (gethash memory *memory*)
	  (unless (member token (gethash memory *memory*) :test #'equalp)
	    (push token (gethash memory *memory*)))
	  (setf (gethash memory *memory*) (list token)))
      ;; Remove token
      (when (gethash memory *memory*)
	(setf (gethash memory *memory*)
	      (remove-if #'(lambda (item)
			     (equalp item token))
			 (gethash memory *memory*))))))

;; Working memory

(defun assert-facts (&rest fact-list)
  "Adds facts in <fact-list> to the working memory and Rete Network.

   Identical facts (tested with equalp) are not allowed and will not be
   processed. Returns the number of facts asserted."

  (let ((count 0))
    (incf *current-timestamp*)
    (dolist (fact fact-list)
      (unless (gethash fact *working-memory*)
	(let ((fact-copy (copy-structure fact)))
	  (incf *current-fact-index*)
	  (setf (gethash fact-copy *working-memory*) *current-fact-index*)
	  (incf count)
	  (object-type-node '+ *current-timestamp* fact-copy))))

    count))

(defmacro modify-fact (fact modifier-fn)
  "Modifies a <fact> in Working Memory as specified in <modifier-fn>.

   <modifier-fn> needs to be a function that takes one argument (fact)."
  (let ((temp-reference (gensym)))
    `(let ((,temp-reference ,fact))
       (retract-facts ,temp-reference)
       (funcall ,modifier-fn ,fact)
       (assert-facts ,temp-reference))))

(defun retract-facts (&rest fact-list)
  "Removes facts in <fact-list> from the Working Memory and Rete Network."
  (let ((count 0))
    (incf *current-timestamp*)
    (dolist (fact fact-list)
      (when (gethash fact *working-memory*)
	(object-type-node '- *current-timestamp* fact)
	(remhash fact *working-memory*)
	(incf count)))

    count))

(defun deffacts (&rest facts)
  (setf *deffacts* (append *deffacts* facts)))

(defun facts ()
  "Returns all facts in Working Memory."
  (let ((result '()))
    (maphash #'(lambda (key value)
		 (when (numberp value)
		   (push key result)))
	     *working-memory*)
    result))

;; Engine functions

(defun order-by-salience (conflict-set)
  (stable-sort conflict-set #'(lambda (activation1 activation2)
				(> (activation-salience activation1)
				   (activation-salience activation2)))))
(defun depth (conflict-set)
  (stable-sort conflict-set
	       #'(lambda (activation1 activation2)
		   (> (activation-timestamp activation1)
		      (activation-timestamp activation2)))))

(defun conflict-set ()
  (let ((result '()))
    (maphash #'(lambda (k v)
		 (declare (ignore k))
		 (push v result))
	     *activations*)
    result))
			
(defun agenda ()
  "Return the current agenda."
  (depth (order-by-salience (conflict-set))))

(defun clear ()
  "Clears the engine."
  (clrhash *working-memory*)
  (clrhash *memory*)
  (clrhash *activations*)

  (clrhash *object-type-node*)
  (make-object-type-node)

  (setf *defrules* '()) ; undef all generated functions?
  (setf *deffacts* '())

  (setf *current-timestamp* 0)
  (setf *current-fact-index* 0)

  t)

(defun reset ()
  "Resets the engine."
  (clrhash *working-memory*)
  (clrhash *memory*)
  (clrhash *activations*)

  (apply #'assert-facts *deffacts*)

  t)

;; These macros are the building blocks of the MPS rule language and they
;; expand into a bunch of defuns that represent the Rete network of the rules.

(defmacro defrule (name &body body)
  (let* ((rhs (member '=> body))
	 (lhs (ldiff body rhs))
	 (production-node-name (sym name "-production")))
    (when (member name *defrules*)
      (error "~&~A is already defined!" name))
    (push name *defrules*)
    (setf *fact-bindings* (make-hash-table))
    (setf *variable-bindings* (make-hash-table))
    `(progn
       (make-production-node ',production-node-name ',name 0)
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

(defun make-production-node (name rule salience)
  (emit `(defun ,(sym name "-left") (key token timestamp)
	   (store-activation key token timestamp ',rule ',salience))))

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
		 (dolist (fact (contents-of ',(sym name (- index 1) "-alpha-memory")))
		   (let* ((token (append tok (list fact))))
		     (when ,join-constraints
		       (store key token ',(sym name index "-beta-memory"))
		       (,(sym next "-left") key token timestamp))))))

	(right `(defun ,(sym name index "-right") (key fact timestamp)
		  (dolist (tok (contents-of ',(sym name (- index 1) "-beta-memory")))
		    (let* ((token (append tok (list fact))))
		      (when ,join-constraints
			(store key token ',(sym name index "-beta-memory"))
			(,(sym next "-left") key token timestamp))))))

	(top `(defun ,(sym name index "-right") (key fact timestamp)
		(let* ((token (list fact)))
		  (store key token ',(sym name index "-beta-memory"))
		  (,(sym next "-left") key token timestamp)))))
    (emit (if (eq index 0)
	      `(progn ,top)
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
  (emit `(defun ,(sym name "-rhs") (token)
	   (let (,@(expand-variable-bindings))
	     ,@body))))
