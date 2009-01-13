;;; Minimal Production System (MPS)

(defpackage :mps
  (:use :common-lisp)
  (:export :defrule :deftemplate
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

(defparameter variable-bindings (make-hash-table))
(defparameter fact-bindings (make-hash-table))
(defparameter nodes (make-hash-table))

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
  "Return T if <sym> is a variable (starts with ?) otherwise NIL."
  (and (symbolp sym)
       (eq (char (string sym) 0) #\?)))

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
    "Add <facts> to the working memory and Rete Network."
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
      (setf fact (get-fact-with-index fact)))
    ; TBD
    nil)

  (defun reset ()
    "Clear the Working Memory and Rete network memory nodes of facts."
    (clrhash working-memory)
    (mapcar #'(lambda (memory)
		(setf (gethash memory rete-network) '()))
	    (all-memory-nodes))
    t)

  (defun retract (&rest facts)
    "Remove <facts> from the Working Memory and Rete network."
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
;;; deftemplate
;;;
;;; (deftemplate <deftemplate-name> [<comment>] 
;;;   <single-slot-definition>*) 
;;; 
;;; <single-slot-definition>  
;;;                ::= (slot <slot-name>  
;;;                          <default-attribute>) 
;;; 
;;; <default-attribute>   
;;;                ::= (default ?NONE | <expression>) | 
;;;                    (default-dynamic <expression>)

(defmacro slot (name &optional (default-form nil))
  (cond ((null default-form)
	 name)

	;; required value
	((and (eq (car default-form) 'default)
	      (eq (cadr default-form) '?NONE))
	 `(,name (error "The slot: ~A requires a value!" ',name)))

	;; default value
	((eq (car default-form) 'default)
	 `(,name ',(eval (cadr default-form))))

	;; default-dynamic value
	((eq (car default-form) 'default-dynamic)
	 `(,name ,(cadr default-form)))))

(defun call-defstruct-constructor (constructor &rest slots)
  (apply constructor (mapcan #'(lambda (slot)
				 `(,(as-keyword (car slot)) ,(cadr slot)))
			     (car slots))))
  
(defmacro deftemplate (name &body slots)
  "
  The deftemplate construct is used to create a template which can then
  be used by non-ordered facts to access fields of the fact by name.

  Syntax:
  <deftemplate-construct>  
    ::= (deftemplate <deftemplate-name> [<single-slot-definition>]*)
 
  <single-slot-definition>
    ::= (slot <slot-name> [<default-attribute>])
 
  <default-attribute> 
    ::= (default ?NONE | <expression>) |
        (default-dynamic <expression>)

  Examples:
  (deftemplate object
    (slot id (default-dynamic (gensym)))
    (slot name (default ?NONE))           ; Makes name a required field!
    (slot age))
  "
  (let ((defstruct-name (make-sym "deftemplate/" name))
	(defstruct-constructor (make-sym "make-deftemplate/" name)))
    `(progn
       (defstruct ,defstruct-name
	 ,@(mapcar #'macroexpand-1 slots))
     
       (defmacro ,name (&rest slots)
	 (call-defstruct-constructor ',defstruct-constructor slots)))))


;;; defrule
(defmacro defrule (name &body body)
  (declare (ignore docstring))
  (let ((rhs (cdr (member '=> body)))
	(lhs (ldiff body (member '=> body))))
    `(progn
;       (let ((fact-bindings (make-hash-table))
;	     (variable-bindings (make-hash-table)))
	 (compile-lhs ,name ,@lhs)
	 (compile-rhs ,name ,@rhs))))

;; defrule - LHS
(defmacro compile-lhs (rule-name &body lhs)
  `(progn
     (setf variable-bindings (make-hash-table))
     (setf fact-bindings (make-hash-table))
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
      (not `(parse-not-ce ,rule-name ,conditional-element))
      (test `(parse-test-ce ,rule-name ,conditional-element))
      (otherwise `(parse-pattern-ce ,rule-name nil ,conditional-element)))))

(defmacro parse-not-ce (rule-name variable &rest conditional-elements)
  ; TBD
  (print (list 'not rule-name variable conditional-elements)))

(defmacro parse-test-ce (rule-name variable conditional-element)
  ; TBD
  (print (list 'test rule-name variable conditional-element)))

(defmacro parse-pattern-ce (rule-name variable conditional-element)
  (let ((deftemplate-name (car conditional-element))
	(position (hash-table-count fact-bindings)))
    `(progn
       (unless ,(null variable)
	 (setf (gethash ',variable fact-bindings) ,position))
       (setf (gethash ,position nodes) (make-alpha-nodes ',rule-name ',deftemplate-name ',conditional-element ',variable ,position))
       (make-beta-node ',rule-name ',deftemplate-name ,position))))

(defun make-alpha-nodes (rule-name deftemplate-name conditional-element variable position)
  (let ((prev-node '()))
    (dolist (slot (cdr conditional-element))
      (let* ((slot-name (car slot))
	     (slot-binding (if (variable-p (cadr slot))
			       (cadr slot)
			       nil))
	     (slot-constraint (if (null slot-binding)
				  (cadr slot)
				  (caddr slot))))
	(multiple-value-bind (alpha-node alpha-node-name)
	    (if (or (consp slot-constraint)
		    (symbolp slot-constraint))
		(make-node-with-symbol-constraint rule-name deftemplate-name slot-name slot-binding slot-constraint variable position)
		(make-node-with-literal-constraint rule-name deftemplate-name slot-name slot-constraint position))
	  (pprint alpha-node)
	  (eval alpha-node)
	  (if prev-node
	      (connect-nodes prev-node alpha-node-name)
	      (add-to-root (car conditional-element) alpha-node-name))
	  (setf prev-node alpha-node-name))))
    prev-node))

(defun make-beta-node (rule-name deftemplate-name position)
  (print 'beta))

(defun make-node-with-literal-constraint (rule-name deftemplate-name slot-name slot-constraint position)
  (let ((defstruct-name (make-sym "deftemplate/" deftemplate-name))
	(node-name (make-sym "alpha/" rule-name "-" (format nil "~A" position) "/" deftemplate-name "-" slot-name)))
    (values
     `(defun ,node-name (key fact timestamp)
	(when (eq (,(make-sym defstruct-name "-" slot-name) fact)
		  ,slot-constraint)
	  (unless (consp fact)
	    (setf fact (list fact)))
	  (store key fact ',(make-sym "memory/" node-name))
	  (propagate key fact timestamp ',node-name)))
     node-name)))

(defun make-node-with-symbol-constraint (rule-name deftemplate-name slot-name slot-binding slot-constraint variable position)
  (let* ((defstruct-name (make-sym "deftemplate/" deftemplate-name))
	 (node-name (make-sym "alpha/" rule-name "-" (format nil "~A" position) "/" deftemplate-name "-" slot-name))
	 (slot-accessor (make-sym defstruct-name "-" slot-name))
	 (binding-constraint (parse-binding-constraint slot-binding slot-constraint slot-accessor variable position))
	 (constraint (if slot-constraint
			 (expand-variables slot-constraint)
			 binding-constraint)))
    (values
     `(defun ,node-name (key fact timestamp)
	(when ,constraint
	  (unless (consp fact)
	    (setf fact (list fact)))
	  (store key fact ',(make-sym "memory/" node-name))
	  (propagate key fact timestamp ',node-name)))
     node-name)))

(defun parse-binding-constraint (slot-binding slot-constraint slot-accessor variable position)
  (let ((fact-variable variable))
    (when (not (null slot-binding))
      ;; Make sure that this slot-value is reachable in the RHS
      (when (and (null fact-variable)
		 (null (gethash slot-binding variable-bindings)))
	(setf fact-variable (gensym))
	(setf (gethash fact-variable fact-bindings) position))
      ;; Bind this variable to this CE
      (if (not (gethash slot-binding variable-bindings))
	  (progn
	    (setf (gethash slot-binding variable-bindings) (list slot-accessor fact-variable (list position)))
	    (when (null slot-constraint)
	      t))
	  (unless (member position (caddr (gethash slot-binding variable-bindings)))
	    (push (caddr (gethash slot-binding variable-bindings)) position)
	    (when (null slot-constraint)
	      t))))))

(defun expand-variable (variable-name)
  (car (gethash variable-name variable-bindings)))

(defun expand-variables (form)
  (maphash #'(lambda (key value)
	       (nsubst (car value) key form))
	   variable-bindings)
  form)
	   

;; defrule - RHS
(defun make-variable-binding (key value)
  ;; variable-name : (accessor variable)
  `(,key (,(car value) ,(cadr value))))

(defun make-fact-binding (key value)
  ;; variable-name : position
  `(,key (nth ,value token)))

(defmacro compile-rhs (rule-name &body rhs)
  (let ((list-of-fact-bindings '())
	(list-of-variable-bindings '()))
    (maphash #'(lambda (key value)
		 (push (make-fact-binding key value) list-of-fact-bindings)) fact-bindings)
    (maphash #'(lambda (key value)
		 (push (make-variable-binding key value) list-of-variable-bindings)) variable-bindings)
    (when (null rhs)
      (setf rhs '(t)))
    (let ((rhs-function
	   `(defun ,(make-sym "RHS/" rule-name) (activation)
	      (let* ((token (activation-token activation))
		     ,@list-of-fact-bindings
		     ,@list-of-variable-bindings)
		,@rhs))))
      (pprint rhs-function))))
