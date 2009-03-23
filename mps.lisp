;;; Minimal Production System (MPS)

(defpackage :mps
  (:use :common-lisp)
  (:export :agenda
	   :assert-facts
	   :batch
	   :clear
	   :defrule
	   :facts
	   :modify-facts ; TBD
	   :reset
	   :retract-facts
	   :run))
(in-package :mps)

(defstruct activation
  rule salience token timestamp rhs-func prod-mem)

;;; Debug parameters
(defparameter print-generated-code nil)
(defparameter trace-generated-code nil)
(declaim (optimize (speed 0)
		   (space 0)
		   (debug 3)))

;;; Watch parameters
(defparameter activations t)
(defparameter compilations nil) ; TBD
(defparameter facts t)
(defparameter rules t)
(defparameter statistics nil) ; TBD

;;; Compilation globals
(defparameter variable-bindings (make-hash-table))
(defparameter fact-bindings (make-hash-table))
(defparameter ce-bindings (make-hash-table))
(defparameter nodes (make-hash-table))

;;; Helper methods
(defun make-sym (&rest parts)
  "Makes a symbol of <parts>."
  (let ((sym ""))
    (dolist (part (mapcar #'string-upcase (mapcar #'string parts)))
      (setf sym (concatenate 'string sym part)))
    (intern sym)))

(defun variable-p (sym)
  "Returns T if <sym> is a variable (starts with ?) otherwise NIL."
  (and (symbolp sym)
       (eq (char (string sym) 0) #\?)))

;; Stolen from On Lisp by Paul Graham.
(defun flatten (x) 
  (labels ((rec (x acc) 
	     (cond ((null x) acc) 
		   ((atom x) (cons x acc)) 
		   (t (rec (car x) (rec (cdr x) acc)))))) 
    (rec x nil)))

(flet ((order-by-salience (conflict-set)
	 (stable-sort conflict-set #'(lambda (activation1 activation2)
				       (> (activation-salience activation1)
					  (activation-salience activation2))))))
  (defun depth (conflict-set)
    "Implementation of the conflict resolution strategy 'depth'"
    (order-by-salience (stable-sort conflict-set
				    #'(lambda (activation1 activation2)
					(> (activation-timestamp activation1)
					   (activation-timestamp activation2)))))))

;;; Inference engine implementation
;;; -------------------------------
(let* ((conflict-resolution-strategy #'depth)
       (rete-network (make-hash-table))
       (root-node (setf (gethash 'root rete-network) (make-hash-table)))
       (working-memory (make-hash-table :test #'equalp))
       (current-fact-index 0)
       (current-timestamp 0))

  ;; Public API
  (defun agenda ()
    "Returns the current agenda and the number of activations on it."
    (let ((conflict-set (flatten (get-conflict-set))))

      (values (funcall conflict-resolution-strategy conflict-set)
	      (length conflict-set))))

  (defun assert-facts (&rest fact-list)
    "Adds facts in <fact-list> to the working memory and Rete Network.

     Identical facts (tested with equalp) are not allowed and will not be
     processed. The number of facts asserted is returned."
    (let ((count 0))
      (incf current-timestamp)
      (dolist (fact fact-list)
	(unless (gethash fact working-memory)
	  (incf current-fact-index)
	  (setf (gethash fact working-memory) current-fact-index)
	  (setf (gethash current-fact-index working-memory) fact)
	  (format facts "~&=> ~D ~S" current-fact-index fact)
	  (incf count)
	  (mapcar #'(lambda (nodes)
		      (if (consp nodes)
			  (dolist (node nodes)
			    (funcall node '+ fact current-timestamp))
			  (funcall nodes '+ fact current-timestamp)))
		  (gethash (type-of fact) (gethash 'root rete-network)))))

      count))

  (defun batch (file)
    "Allows batch processing of interactive commands by replacing standard
     input with the contents of a file."
    (let ((*print-pretty* t)
	  (count 0))
      (with-open-file (stream file
			      :direction :input
			      :if-does-not-exist nil)
	(do ((form (read stream) (progn
				   (incf count)
				   (read stream nil 'eof))))
	    ((eq form 'eof))
	  (format t "~&~A> ~S~%" (if (package-nicknames *package*)
				     (car (package-nicknames *package*))
				     (package-name *package*)) form)
	  (let ((result (multiple-value-list (eval form))))
	    (format t "~&~{~S~%~}" result))))

      count))

  (defun clear ()
    "Clears the engine. NOTE! clear does NOT remove defstructs."
    (clrhash rete-network)
    (clrhash working-memory)
    (setf root-node (setf (gethash 'root rete-network) (make-hash-table)))
    (setf current-fact-index 0)
    (setf current-timestamp 0)

    t)

  (defun facts ()
    "Returns all facts in Working Memory."
    (let ((result '()))
      (maphash #'(lambda (key value)
		   (when (numberp key)
		     (push value result)))
	     working-memory)

      result))
    
  (defmacro modify-facts (fact-modifiers)
    "Modifies facts in Working Memory as specified in <fact-modifiers>."
    (let ((fact-bindings '())
	  (modify-forms '()))
      (dolist (fact-modifier fact-modifiers)
	(let ((fact (car fact-modifier))
	      (fact-binding (gensym))
	      (slot-values (cdr fact-modifier)))
	  (when (numberp fact)
	    (setf fact (get-fact-with-index fact)))
	  
	  (push `(,fact-binding ,fact) fact-bindings)
	  (dolist (slot-value slot-values)
	    (let ((slot-name (car slot-value))
		  (slot-value (cadr slot-value)))
	      (push `(setf (,(make-sym (type-of fact) "-" slot-name) ,fact-binding) ,slot-value) modify-forms)))))
      `(let (,@fact-bindings)
	 (retract-facts ,@(mapcar #'car fact-bindings))
	 ,@modify-forms
	 (assert-facts ,@(mapcar #'car fact-bindings)))))

  (defun reset ()
    "Clear the Working Memory and Rete Network memory nodes of facts."
    (clrhash working-memory)
    (mapcar #'(lambda (memory)
		(setf (gethash memory rete-network) '()))
	    (all-memory-nodes))

    t)

  (defun retract-facts (&rest fact-list)
    "Removes facts in <fact-list> from the Working Memory and Rete Network."
    (let ((count 0))
      (incf current-timestamp)
      (dolist (fact fact-list)
	(when (numberp fact)
	  (setf fact (get-fact-with-index fact)))
	(when (gethash fact working-memory)
	  (let ((fact-index (get-fact-index-of fact)))
	    (remhash fact-index working-memory)
	    (remhash fact working-memory)
	    (format facts "~&<= ~D ~S" fact-index fact)
	    (incf count)
	    (mapcar #'(lambda (node)
			(funcall node '- fact current-timestamp))
		    (gethash (type-of fact) (gethash 'root rete-network))))))

      count))

  (defun run (&optional (limit -1))
    "Run"
    (do* ((curr-agenda (agenda) (agenda))
	  (execution-count 0 (+ execution-count 1))
	  (limit limit (- limit 1)))
	 ((or (eq limit 0)
	      (= (length curr-agenda) 0)) execution-count)
      (let* ((activation (first curr-agenda)))
	(format rules "~&FIRE: ~A ~S" (activation-rule activation) (activation-token activation))
	(funcall (activation-rhs-func activation) activation)
	(store '- activation (activation-prod-mem activation)))))


  ; Conditional element macros
  (defmacro exists (&rest conditional-elements)
    `(not (not ,@conditional-elements)))

  (defmacro forall (conditional-element &rest conditional-elements)
    `(not ,conditional-element (not ,@conditional-elements)))


  ;; Private API
  (defun add-to-production-nodes (node)
    "Adds <node> to the list of production nodes."
    (let ((production-memory (make-sym "MEMORY/" node)))
      (format print-generated-code "~&(ADD-TO-PRODUCTION-NODES :NODE ~S)" node)
      (if (gethash 'production-nodes rete-network)
	  (push production-memory (gethash 'production-nodes rete-network))
	  (setf (gethash 'production-nodes rete-network) (list production-memory)))))

  (defun add-to-root (type node)
    "Adds <node> as a successor to the type-node for <type>."
    (format print-generated-code "~&(ADD-TO-ROOT :TYPE ~S :NODE ~S)" type node)
    (if (gethash type root-node)
	(push node (gethash type root-node))
	(setf (gethash type root-node) (list node))))

  (defun all-memory-nodes ()
    "Returns a list with the names of all memory nodes in the Rete Network."
    (let ((mem-nodes '()))
      (maphash #'(lambda (key val)
		   (declare (ignore val))
		   (let ((skey (string key)))
		     (when (and (> (length skey) 7)
				(string-equal "MEMORY/"
					      (subseq skey 0 7)))
		       (setf mem-nodes (cons key mem-nodes)))))
	       rete-network)

      mem-nodes))

  (defun connect-nodes (from to)
    "Connects <from> with <to> in the Rete Network."
    (format print-generated-code "~&(CONNECT-NODES :FROM ~S :TO ~S)" from to)
    (if (gethash from rete-network)
	(push to (gethash from rete-network))
	(setf (gethash from rete-network) (list to))))

  (defun contents-of (memory)
    "Returns all tokens in <memory>."
    (gethash memory rete-network))

  (defun get-conflict-set ()
    (mapcar #'contents-of (gethash 'production-nodes rete-network)))

  (defun propagate (key token timestamp from)
    "Propagates <token> to all nodes that are connected to <from>."
    (format trace-generated-code "~&(PROPAGATE :KEY ~S :TOKEN ~S :TIMESTAMP ~S :FROM ~S)" key token timestamp from)
    (mapcar #'(lambda (node)
		(funcall node key token timestamp))
	    (gethash from rete-network)))

  (defun get-fact-with-index (index)
    "Returns the fact instance with fact-index <index>."
    (gethash index working-memory))

  (defun get-fact-index-of (fact)
    "Returns the fact-index of <fact>."
    (gethash fact working-memory))

  (defun store (key token memory)
    "Adds <token> to (if <key> is '+) or removes from (if <key> is '-) <memory>."
    (format trace-generated-code "~&(STORE :KEY ~S :TOKEN ~S :MEMORY ~S)" key token memory)
    (if (eq key '+)
	;; Add token
	(if (gethash memory rete-network)
	    (unless (member token (gethash memory rete-network) :test #'equalp)
	      (push token (gethash memory rete-network)))
	    (setf (gethash memory rete-network) (list token)))
	;; Remove token
	(when (gethash memory rete-network)
	  (setf (gethash memory rete-network) (remove-if #'(lambda (item)
							     (equalp item token))
							 (gethash memory rete-network)))))))
;;; defrule
(defmacro defrule (name &body body)
  "Rules are defined using the defrule construct.

   Syntax:
   <defrule-construct>
     ::= (defrule <rulename>
           <conditional-element>*
           =>
           <expression>*)

   <conditional-element>
     ::= <template-pattern-CE> | <assigned-pattern-CE> |  
         <not-CE> | <test-CE> | <exists-CE>

   <template-pattern-CE> ::= (<defstruct-name> <single-field-LHS-slot>*)
   <assigned-pattern-CE> ::= <single-field-variable> <- <template-pattern-CE>

   <not-CE>              ::= (not <conditional-element>)  
   <test-CE>             ::= (test <function-call>) 
   <exists-CE>           ::= (exists <conditional-element>+) 

   <single-field-LHS-slot>
     ::= (<slot-name> [<single-field-variable>] <constraint>)
  "
  (let ((rhs (if (cdr (member '=> body))
		 (cdr (member '=> body))
		 `(t)))
	(lhs (ldiff body (member '=> body))))
    `(progn
       (let ((fact-bindings (make-hash-table))
	     (ce-bindings (make-hash-table))
	     (variable-bindings (make-hash-table)))
	 (compile-lhs ,name ,@lhs)
	 (compile-rhs ',name ',@rhs)
	 (make-production-node ',name))
       ',name)))

(defmacro compile-lhs (rule-name &rest lhs)
  `(parse ,rule-name 0 ,@lhs))

(defmacro parse (rule-name position &rest conditional-elements)
  (unless (eq (car conditional-elements) 'nil)
    (cond ((consp (car conditional-elements))
	   `(progn
	      (parse-ce ,rule-name ,position ,(car conditional-elements))
	      (parse ,rule-name ,(+ position 1) ,@(cdr conditional-elements))))
	  ((variable-p (car conditional-elements))
	   (progn
	     (cl:assert (eq (cadr conditional-elements) '<-))
	     `(progn
		(parse-pattern-ce ,rule-name ,position ,(car conditional-elements) ,(caddr conditional-elements))
		(parse ,rule-name ,(+ position 1) ,@(cdddr conditional-elements))))))))

(defmacro parse-ce (rule-name position conditional-element)
  (let ((ce-type (car conditional-element)))
    (case ce-type
      (not `(parse-not-ce ,rule-name ,position ,conditional-element))
      (test `(parse-test-ce ,rule-name ,position ,conditional-element))
      (otherwise `(parse-pattern-ce ,rule-name ,position nil ,conditional-element)))))

(defmacro parse-not-ce (rule-name position &rest conditional-elements)
  ; TBD
  `(print (list 'not ,rule-name ,position ,conditional-elements)))

(defmacro parse-test-ce (rule-name position variable conditional-element)
  ; TBD
  `(print (list 'test ,rule-name ,position ,variable ,conditional-element)))

(defmacro parse-pattern-ce (rule-name position variable conditional-element)
  (let ((defstruct-name (car conditional-element)))
    `(let ((alpha-node '())
	   (beta-node '()))
       (unless ,(null variable)
	 (setf (gethash ',variable fact-bindings) ,position))
       (setf alpha-node (make-alpha-nodes ',rule-name ',defstruct-name ',conditional-element ',variable ,position))
       (setf (gethash ,position nodes) alpha-node)
       (setf beta-node (make-beta-node ',rule-name ,position))
       (connect-nodes alpha-node (make-sym beta-node "-right")))))

(defun make-alpha-nodes (rule-name defstruct-name conditional-element variable position)
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
		(make-node-with-symbol-constraint rule-name defstruct-name slot-name slot-binding slot-constraint variable position)
		(make-node-with-literal-constraint rule-name defstruct-name slot-name slot-constraint position))
	  (let ((*print-pretty* t))
	    (format print-generated-code "~&~S" alpha-node))
	  (eval alpha-node)
	  (if prev-node
	      (connect-nodes prev-node alpha-node-name)
	      (add-to-root defstruct-name alpha-node-name))
	  (setf prev-node alpha-node-name))))
    prev-node))

(defun make-beta-node (rule-name position)
  (let* ((left-node (unless (eq position 0)
		      (gethash (- position 1) nodes)))
	 (right-node (gethash position nodes))
	 (beta-node-name (make-sym "BETA/" rule-name "-" (format nil "~d" position)))
	 (left-activate (make-sym beta-node-name "-LEFT"))
	 (right-activate (make-sym beta-node-name "-RIGHT"))
	 (beta-node (if left-node
			`(let ((left-memory  ',(make-sym "MEMORY/" left-node))
			       (right-memory ',(make-sym "MEMORY/" right-node)))
			   (defun ,left-activate (key token timestamp)
			     (format trace-generated-code "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)" ',left-activate key token timestamp)
			     (dolist (fact (contents-of right-memory))
			       (let ((tok (append token (list fact))))
				 (when (and ,@(make-binding-test position))
				   (store key tok ',(make-sym "MEMORY/" beta-node-name))
				   (propagate key tok timestamp ',beta-node-name)))))
			   (defun ,right-activate (key fact timestamp)
			     (format trace-generated-code "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)" ',right-activate key fact timestamp)
			     (dolist (token (contents-of left-memory))
			       (let ((tok (append token (list fact))))
				 (when (and ,@(make-binding-test position))
				   (store key tok ',(make-sym "MEMORY/" beta-node-name))
				   (propagate key tok timestamp ',beta-node-name))))))
			;; Left-input adapter
			`(defun ,right-activate (key fact timestamp)
			   (format trace-generated-code "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)" ',right-activate key fact timestamp)
			   (store key (list fact) ',(make-sym "MEMORY/" beta-node-name))
			   (propagate key (list fact) timestamp ',beta-node-name)))))
    (let ((*print-pretty* t))
      (format print-generated-code "~&~S" beta-node))
    (eval beta-node)
    (unless (eq position 0)
      (connect-nodes left-node left-activate))
    (setf (gethash position nodes) beta-node-name)))

(defun make-binding-test (position)
  (let ((result '(t))) ; zero join
    (maphash #'(lambda (k v)
		 (declare (ignore k))
		 (when (> (length v) 1)
		   (let ((prev '()))
		     (dolist (b v)
		       (if (eql position (caddr b))
			   (when prev
			     (push `(equal (,(car b) (nth ,(caddr b) tok)) (,(car prev) (nth ,(caddr prev) tok))) result))
			   (setf prev b))))))
	     variable-bindings)
    result))

(defun make-production-node (rule-name)
  (let* ((production-node-name (make-sym "PRODUCTION/" rule-name))
	 (production-memory (make-sym "MEMORY/PRODUCTION/" rule-name))
	 (production-node `(defun ,production-node-name (key token timestamp)
			     (format trace-generated-code "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)" ',production-node-name key token timestamp)
			     (format activations "~&ACTIVATION: ~A ~S" ',rule-name token)
			     (store key (make-activation :rule ',rule-name
							 :salience 0
							 :token token
							 :timestamp timestamp
							 :rhs-func #',(make-sym "RHS/" rule-name)
							 :prod-mem ',production-memory)
				    ',production-memory))))
    (let ((*print-pretty* t))
      (format print-generated-code "~&~S" production-node))
    (eval production-node)
    (connect-nodes (gethash (- (hash-table-count nodes) 1) nodes) production-node-name)
    (add-to-production-nodes production-node-name)))

(defun make-node-with-literal-constraint (rule-name defstruct-name slot-name slot-constraint position)
  (let ((node-name (make-sym "ALPHA/" rule-name "-" (format nil "~A" position) "/" defstruct-name "-" slot-name)))
    (values
     `(defun ,node-name (key fact timestamp)
	(format trace-generated-code "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)" ',node-name key fact timestamp)
	(when (eq (,(make-sym defstruct-name "-" slot-name) fact) ,slot-constraint)
	  (store key fact ',(make-sym "MEMORY/" node-name))
	  (propagate key fact timestamp ',node-name)))
     node-name)))

(defun make-node-with-symbol-constraint (rule-name defstruct-name slot-name slot-binding slot-constraint variable position)
  (let* ((node-name (make-sym "ALPHA/" rule-name "-" (format nil "~A" position) "/" defstruct-name "-" slot-name))
	 (slot-accessor (make-sym defstruct-name "-" slot-name))
	 (binding-constraint (parse-binding-constraint slot-binding slot-constraint slot-accessor variable position))
	 (constraint (if slot-constraint
			 (expand-variables slot-constraint)
			 binding-constraint)))
    (values
     `(defun ,node-name (key fact timestamp)
	(format trace-generated-code "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)" ',node-name key fact timestamp)
	(when ,constraint
	  (store key fact ',(make-sym "MEMORY/" node-name))
	  (propagate key fact timestamp ',node-name)))
     node-name)))

(defun parse-binding-constraint (slot-binding slot-constraint slot-accessor variable position)
  (let ((fact-variable (if variable
			   variable
			   (gethash position ce-bindings)))
	(binding (gethash slot-binding variable-bindings)))
    (when (not (null slot-binding))
      ;; Make sure that this slot-value is reachable in the RHS
      (when (null fact-variable)
	(setf fact-variable (gensym))
	(setf (gethash position ce-bindings) fact-variable)
	(setf (gethash fact-variable fact-bindings) position))

      (if (not binding)
	  (progn ; This is the first binding for this variable
	    (setf (gethash slot-binding variable-bindings) (list (list slot-accessor fact-variable position)))
	    (when (null slot-constraint) t))
	  
	  (progn
	    (dolist (b binding)
	      ;; If this position already has a binding for this variable we'll
	      ;; return a alpha-constraint
	      (when (equal position (caddr b))
		(return `(equal (,(car b) fact) (,slot-accessor fact)))))

	    ;; Create a new binding
	    (setf (gethash slot-binding variable-bindings)
		  (append (gethash slot-binding variable-bindings)
			  (list (list slot-accessor fact-variable position))))
	    (when (null slot-constraint) t))))))

(defun expand-variable (variable-name)
  (car (gethash variable-name variable-bindings)))

(defun expand-variables (form)
  (maphash #'(lambda (key value)
	       (nsubst `(,(car value) fact) key form))
	   variable-bindings)
  form)

(defun make-variable-binding (key value)
  ;; variable-name : ((accessor fact-variable position) ...) -> (variable-name (accessor fact-variable))
  `(,key (,(caar value) ,(cadar value))))

(defun make-fact-binding (key value)
  ;; variable-name : position
  `(,key (nth ,value token)))

(defun compile-rhs (rule-name &rest rhs)
  (let ((list-of-fact-bindings '())
	(list-of-variable-bindings '()))
    (maphash #'(lambda (key value)
		 (push (make-fact-binding key value) list-of-fact-bindings))
	     fact-bindings)
    (maphash #'(lambda (key value)
		 (push (make-variable-binding key value) list-of-variable-bindings))
	     variable-bindings)
    (let* ((rhs-function-name (make-sym "RHS/" rule-name))
	   (rhs-function `(defun ,rhs-function-name (activation)
			    (format trace-generated-code "~&(~A :ACTIVATION ~S)" ',rhs-function-name activation)
			    (let* ((token (activation-token activation))
				   ,@list-of-fact-bindings
				   ,@list-of-variable-bindings)
			      ,@rhs))))
      (let ((*print-pretty* t))
	(format print-generated-code "~&~S" rhs-function))
      (eval rhs-function))))
