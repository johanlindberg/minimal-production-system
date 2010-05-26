;;; Minimal Production System (MPS)
;;; Copyright (C) 2008-2010 Johan Lindberg, Pulp Software

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

	   :agenda        ; public API
	   :assert-facts
	   :clear
	   :deffacts
	   :defrule
	   :facts
	   :halt
	   :modify-facts
	   :reset
	   :retract-facts
	   :run
	   :salience))
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

(defmacro emit (&body body)
  `(progn
     (print ,@body)
     (eval ,@body)))

;; Compilation data.

(defparameter *salience* 0)
(defparameter *fact-bindings* nil)
(defparameter *variable-bindings* nil)

;; Runtime data.

(defvar *memory* (make-hash-table :test #'equalp)) ; Rete Network node memories
(defvar *working-memory* (make-hash-table :test #'equalp))

(defvar *activations* (make-hash-table :test #'equalp))
(defvar *object-type-node* (make-hash-table))

(defvar *defrules* '())
(defvar *deffacts* '())

(defvar *conflict-resolution-strategy* 'nil)

(defvar *current-timestamp* 0)
(defvar *current-fact-index* 0)

(defstruct activation
  rule
  salience
  token
  timestamp)

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
    (store key activation salience
	   *activations*
	   #'(lambda (i)
	       (and (equalp (activation-rule i) rule)
		    (equalp (activation-token i) token))))))

(defun store (key item memory
	      &optional
	      (table *memory*)
	      (removal-fn #'(lambda (i)
			      (equalp i item))))
  (if (eq key '+)
      ;; Add item
      (if (gethash memory table)
	  (unless (member item (gethash memory table) :test #'equalp)
	    (push item (gethash memory table)))
	  (setf (gethash memory table) (list item)))
      ;; Remove item
      (when (gethash memory table)
	(setf (gethash memory table)
	      (remove-if removal-fn (gethash memory table))))))

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

(defmacro modify-facts (modifier-fn &rest facts)
  "Modifies <facts> in Working Memory as specified in <modifier-fn>.

   <modifier-fn> needs to be a function that takes one argument (fact)."
  (let ((let-bindings '())
	(gensyms '())
	(modifier-calls '()))
    (dolist (fact facts)
      (let ((temp-reference (gensym)))
	(push `(,temp-reference ,fact) let-bindings)
	(push temp-reference gensyms)
	(push `(funcall ,modifier-fn ,temp-reference) modifier-calls)))
    `(let (,@let-bindings)
       (retract-facts ,@gensyms)
       ,@modifier-calls
       (assert-facts ,@gensyms))))

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
  (stable-sort (order-by-salience conflict-set)
	       #'(lambda (activation1 activation2)
		   (> (activation-timestamp activation1)
		      (activation-timestamp activation2)))))
(setf *conflict-resolution-strategy* #'depth)

(defun conflict-set ()
  (let ((result '()))
    (maphash #'(lambda (salience activations)
		 (declare (ignore salience))
		 (dolist (activation activations)
		   (push activation result)))
	     *activations*)
    result))

(defun agenda ()
  (funcall *conflict-resolution-strategy* (conflict-set)))

(defun clear ()
  "Clears the engine.

   Clear removes all facts from working memory, the conflict set and the
   Rete Network node memories. It also clears the object type node, any
   deffacts forms and all counters (fact index and timestamp).

   The list of defined rules is cleared but the functions generated from
   evaluating any defrule forms will still exist in current package name
   space."
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
  "Resets the engine.

   Reset clears the working memory, the conflict set and the Rete Network
   memory nodes. If there are any deffacts forms available they will be
   re-asserted."
  (clrhash *working-memory*)
  (clrhash *memory*)
  (clrhash *activations*)

  (apply #'assert-facts *deffacts*)

  t)

(let ((limit -1))
  (defun run (&optional (n -1))
    "Run"
    (setf limit n)
    (do* ((curr-agenda (agenda) (agenda))
	  (execution-count 0 (+ execution-count 1)))
	 ((or (eq limit 0)
	      (eq (length curr-agenda) 0)) execution-count)
      (decf limit)
      (let* ((activation (first curr-agenda))
	     (token (activation-token activation))
	     (timestamp (activation-timestamp activation))
	     (rule (activation-rule activation))
	     (salience (activation-salience activation))
	     (action (sym (activation-rule activation) "-rhs")))
	(funcall action token)
	(store-activation '- token timestamp rule salience))))

  (defun halt ()
    "Halt"
    (setf limit 0)))

;; These macros are the building blocks of the MPS rule language and they
;; expand into a bunch of defuns that represent the Rete network of the rules.

(defmacro defrule (name &body body)
  (let* ((rhs (member '=> body))
	 (lhs (ldiff body rhs))
	 (production-node-name (sym name "-production")))
    (when (member name *defrules*)
      (error "~&~A is already defined!" name))
    (push name *defrules*)
    (setf *salience* 0)
    (setf *fact-bindings* (make-hash-table))
    (setf *variable-bindings* (make-hash-table))
    `(progn
       (compile-lhs ,name ,production-node-name ,@lhs)
       (make-object-type-node) ; regenerate the object-type-node defun
       (make-production-node ',production-node-name ',name)
       (compile-rhs ,name ,@(cdr rhs)))))

(defmacro compile-lhs (name end-node-name &rest contents)
  (let ((result '())
	(conditional-elements '())
	(next-node-name nil)
	(index 0))
    (dolist (ce contents)
      (case (car ce) ;; Dispatch on meta data (salience)
	(salience
	 (setf *salience* (cadr ce)))
	(otherwise
	 (push ce conditional-elements))))

    (setf index (- (length conditional-elements) 1))
    (dolist (ce conditional-elements)
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
	   (when (variablep (car ce))
	     (setf (gethash (car ce) *fact-bindings*)
		   `(,(car ce) (nth ,index token)))
	     (setf ce (cadr ce))) ; make sure that we only pass on the actual CE
	   (push `(compile-pattern-ce ,name ,index ,next-node-name ,ce) result))))
      (decf index))
    `(progn
       ,@result)))

(defun make-production-node (name rule)
  (emit `(defun ,(sym name "-left") (key token timestamp)
	   (store-activation key token timestamp ',rule ',*salience*))))

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
