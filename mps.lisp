;;; Minimal Production System (MPS)

(defpackage :mps
  (:use :common-lisp)
  (:export :defrule
	   :agenda :assert-fact	:breadth :clear
	   :depth :facts :get-strategy :load
	   :modify :reset :run :set-strategy)
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

;; Stolen from On Lisp by Paul Graham.
(defun flatten (x) 
  (labels ((rec (x acc) 
	     (cond ((null x) acc) 
		   ((atom x) (cons x acc)) 
		   (t (rec (car x) (rec (cdr x) acc)))))) 
    (rec x nil)))


;;; Conflict resolution strategies
;;; ------------------------------
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
;;; -------------------------------
(let* ((conflict-resolution-strategy #'depth)
       (rete-network (make-hash-table))
       (root-node (setf (gethash 'root rete-network) (make-hash-table)))
       (working-memory (make-hash-table :test #'equalp))
       (fact-index 0)
       (timestamp 0))

  ;; Public API
  (defun agenda ()
    "Return all activations on the agenda."
    (funcall conflict-resolution-strategy (flatten (get-conflict-set))))

  (defun assert (&rest facts)
    "Add <facts> to the working memory and Rete Network"
    (incf timestamp)
    (dolist (fact facts)
      (incf fact-index)
      (unless (gethash fact working-memory)
	(setf (gethash fact working-memory) fact-index)
	(setf (gethash fact-index working-memory) fact)
	(mapcar #'(lambda (node)
		    (funcall node '+ fact timestamp))
		(gethash (type-of fact) (gethash 'root rete-network)))))
    t)

  (defun clear ()
    "Clear the engine"
    (clrhash rete-network)
    (clrhash working-memory)
    (setf root-node (setf (gethash 'root rete-network) (make-hash-table)))
    (setf fact-index 0)
    (setf timestamp 0)

    t)

  (defun facts ()
    "Return all facts in working memory"
    (let ((result '()))
      (maphash #'(lambda (key value)
		   (when (numberp key)
		     (push value result)))
	     working-memory)
      result))
    

  (defun get-strategy ()
    "Return the current conflict resolution strategy."
    conflict-resolution-strategy)

  (defun modify (fact &rest slots)
    "Modify <fact>"
    (when (numberp fact)
      (setf fact (get-fact fact)))
    ; TBD
    nil)

  (defun reset ()
    "Clear the Working Memory and Rete network memory nodes of facts"
    (clrhash working-memory)
    (mapcar #'(lambda (memory)
		(setf (gethash memory rete-network) '()))
	    (all-memory-nodes))
    t)

  (defun retract (&rest facts)
    "Remove <facts> from the Working Memory and Rete network"
    (incf timestamp)
    (dolist (fact facts)
      (when (gethash fact working-memory)
	(setf fact-index (get-fact-index-of fact))
	(remhash fact-index working-memory)
	(remhash fact working-memory)
	  
	(mapcar #'(lambda (node)
		    (funcall node '- fact timestamp))
		(gethash (type-of fact) (gethash 'root rete-network)))))
    t)

  (defun run (&optional (limit -1))
    "Run"
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

  (defun connect-nodes (from to)
    "Connect <from> with <to> in the Rete Network"
    (if (gethash from rete-network)
	(setf (gethash from rete-network) (append (gethash from rete-network) (list to)))
	(setf (gethash from rete-network) (list to))))

  (defun contents-of (memory)
    "Get all tokens in <memory>"
    (gethash memory rete-network))

  (defun get-conflict-set ()
    (mapcar #'contents-of (gethash 'production-nodes rete-network)))

  (defun propagate (key token timestamp from)
    "Propagate <token> to all nodes that are connected to <from>"
    (mapcar #'(lambda (node)
		(funcall node key token timestamp))
	    (gethash from rete-network)))

  (defun get-fact-with-index (index)
    (gethash index working-memory))

  (defun get-fact-index-of (fact)
    (gethash fact working-memory))

  (defun store (key token memory)
    "Add <token> to (if <key> is '+) or remove from (if <key> is '-) <memory>"
    (if (eq key '+)
	;; Add token
	(if (gethash memory rete-network)
	    (if (not (member token (gethash memory rete-network) :test #'equalp))
		(push (gethash memory rete-network) token))
	    (setf (gethash memory rete-network) (list token)))

	;; Remove token
	(if (gethash memory rete-network)
	    (setf (gethash memory rete-network) (remove-if #'(lambda (item)
							       (equalp item token))
							   (gethash memory rete-network)))))))

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

