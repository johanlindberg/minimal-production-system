;;; Minimal Production System (MPS)

(defpackage :mps
  (:use :common-lisp)
  (:export :agenda
	   :assert-facts
	   :clear
           :deffacts
	   :defrule
	   :facts
	   :modify-fact
	   :reset
	   :retract-facts
	   :run))
(in-package :mps)

(defstruct activation
  rule salience token timestamp rhs-function production-memory)

;;; Debug parameters
(defparameter *print-generated-code* nil)
(defparameter *trace-generated-code* nil)
(declaim (optimize (speed 0)
		   (space 0)
		   (debug 3)))

(defparameter *deffacts* (make-hash-table))
(defparameter *defrules* '())
(defparameter *generated-functions* '())

;;; Watch parameters
(defparameter *activations* t)
(defparameter *compilations* nil) ; TBD
(defparameter *facts* t)
(defparameter *rules* t)
(defparameter *statistics* nil) ; TBD

;;; Compilation globals
(defparameter *variable-bindings* (make-hash-table))
(defparameter *fact-bindings* (make-hash-table))
(defparameter *ce-bindings* (make-hash-table))
(defparameter *nodes* (make-hash-table))
(defparameter *salience* 0)

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
(defun flatten (lst)
  "Returns a flattened version of <lst>."
  (labels ((rec (lst acc) 
	     (cond ((null lst) acc) 
		   ((atom lst) (cons lst acc)) 
		   (t (rec (car lst) (rec (cdr lst) acc)))))) 
    (rec lst nil)))

;;; Conflict resolution strategies (depth)
(flet ((order-by-salience (conflict-set)
	 (stable-sort conflict-set #'(lambda (activation1 activation2)
				       (> (activation-salience activation1)
					  (activation-salience activation2))))))
  (defun depth (conflict-set)
    "Sorts (according to salience and timestamp) and returns <conflict-set>."
    (order-by-salience (stable-sort conflict-set
				    #'(lambda (activation1 activation2)
					(> (activation-timestamp activation1)
					   (activation-timestamp activation2)))))))

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
     processed. Returns the number of facts asserted."
    (let ((count 0))
      (incf current-timestamp)
      (dolist (fact fact-list)
	(unless (gethash fact working-memory)
          (let ((fact-copy (copy-structure fact)))
            (incf current-fact-index)
            (setf (gethash fact-copy working-memory) current-fact-index)
            (setf (gethash current-fact-index working-memory) fact-copy)
            (format *facts* "~&=> FACT: F-~D ~S~%" current-fact-index fact-copy)
            (incf count)
            (mapcar #'(lambda (nodes)
                        (if (consp nodes)
                            (dolist (node nodes)
                              (funcall node '+ fact-copy current-timestamp))
                            (funcall nodes '+ fact-copy current-timestamp)))
                    (gethash (type-of fact-copy) (gethash 'root rete-network))))))

      count))

  (defun clear ()
    "Clears the engine. NOTE! clear does NOT remove defstructs."
    (clrhash rete-network)
    (clrhash working-memory)
    (clrhash *nodes*)

    (setf *defrules* '())
    (clrhash *deffacts*)

    (setf root-node (setf (gethash 'root rete-network) (make-hash-table)))
    (setf current-fact-index 0)
    (setf current-timestamp 0)

    t)

  (defmacro deffacts (name &rest facts)
    (setf (gethash name *deffacts*) '())
    (dolist (fact facts)
      (push fact (gethash name *deffacts*)))
    `,(length (gethash name *deffacts*)))

  (defun facts ()
    "Returns all facts in Working Memory."
    (let ((result '()))
      (maphash #'(lambda (key value)
		   (when (numberp key)
		     (push value result)))
	     working-memory)

      result))

  (defun token-to-string (token)
    (format nil "~{f-~A,~}" (mapcar #'(lambda (fact)
                                        (get-fact-index-of fact))
                                    token)))

  (defun facts-to-indexes (facts)
    (mapcar #'(lambda (fact)
                (get-fact-index-of fact))
            facts))

  (defun matches (rule-name)
    (let ((alpha-memory (concatenate 'string "MEMORY/ALPHA/" (string rule-name)))
          (beta-memory (concatenate 'string "MEMORY/BETA/" (string rule-name)))
          (production-memory (concatenate 'string "MEMORY/PRODUCTION/" (string rule-name)))
          (i 0)
          (j 0))
      (dolist (mem (sort (all-memory-nodes) #'string-lessp))
        (let ((memory-node (string mem)))
          (cond ((and (>= (length memory-node) (length alpha-memory))
                      (string-equal (subseq memory-node 0 (length alpha-memory)) alpha-memory))
                 (format t "~&Matches for pattern ~A:~%~{f-~A~%~}" (incf i) (facts-to-indexes (contents-of mem))))
                ((and (>= (length memory-node) (length beta-memory))
                      (string-equal (subseq memory-node 0 (length beta-memory)) beta-memory))
                 (if (> j 0)
                     (unless (= (- i j) 1)
                       (format t "~&Partial matches for patterns 1-~A:~%~{~A~%~}" (incf j) (mapcar #'(lambda (token)
                                                                                                       (token-to-string token))
                                                                                                   (contents-of mem))))
                     (incf j)))
                ((and (>= (length memory-node) (length production-memory))
                      (string-equal (subseq memory-node 0 (length production-memory)) production-memory))
                 (format t "~&Complete matches for ~A:~%~{~A~%~}" (string rule-name) (mapcar #'(lambda (activation)
                                                                                                 (token-to-string (activation-token activation)))
                                                                                             (contents-of mem)))))))))

  (defmacro modify-fact (fact modifier-fn)
    "Modifies a <fact> in Working Memory as specified in <modifier-fn>.

     <modifier-fn> needs to be a function that takes one argument (fact)."
    (let ((temp-reference (gensym)))      
      `(let ((,temp-reference ,fact))
         (retract-facts ,temp-reference)
         (funcall ,modifier-fn ,fact)
         (assert-facts ,temp-reference))))

  (defun reset ()
    "Clears the Working Memory and Rete Network memory nodes of facts and then
     asserts all facts defined in deffacts forms."
    (apply #'retract-facts (facts))

    (maphash #'(lambda (name fact-list)
                 (declare (ignore name))
                 (apply #'assert-facts fact-list))
             *deffacts*)
    
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
	    (format *facts* "~&<= FACT: F-~D ~S~%" fact-index fact)
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
	      (eq (length curr-agenda) 0)) execution-count)
      (let ((activation (first curr-agenda)))
	(format *rules* "~&FIRE: ~A ~S~%" (activation-rule activation) (activation-token activation))
	(funcall (activation-rhs-function activation) activation)
	(store-activation '- activation (activation-production-memory activation)))))


  ; Conditional element macros
  (defmacro exists (&rest conditional-elements)
    `(not (not ,@conditional-elements)))

  (defmacro forall (conditional-element &rest conditional-elements)
    `(not ,conditional-element (not ,@conditional-elements)))


  ;; Private API
  (defun add-to-production-nodes (node)
    "Adds <node> to the list of production nodes."
    (let ((production-memory (make-sym "MEMORY/" node)))
      (format *print-generated-code* "~&(ADD-TO-PRODUCTION-NODES :NODE ~S)~%" node)
      (if (gethash 'production-nodes rete-network)
	  (push production-memory (gethash 'production-nodes rete-network))
	  (setf (gethash 'production-nodes rete-network) (list production-memory)))))

  (defun add-to-root (type node)
    "Adds <node> as a successor to the type-node for <type>."
    (format *print-generated-code* "~&(ADD-TO-ROOT :TYPE ~S :NODE ~S)~%" type node)
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
    (format *print-generated-code* "~&(CONNECT-NODES :FROM ~S :TO ~S)~%" from to)
    (if (gethash from rete-network)
	(push to (gethash from rete-network))
	(setf (gethash from rete-network) (list to))))

  (defun contents-of (memory)
    "Returns the contents of <memory>."
    (gethash memory rete-network))

  (defun get-conflict-set ()
    "Returns the conflict-set."
    (mapcar #'contents-of (gethash 'production-nodes rete-network)))

  (defun propagate (key token timestamp from)
    "Propagates <token> (with <key> and <timestamp>) to all nodes that are connected to <from>."
    (format *trace-generated-code* "~&(PROPAGATE :KEY ~S :TOKEN ~S :TIMESTAMP ~S :FROM ~S)~%" key token timestamp from)
    (mapcar #'(lambda (node)
		(funcall node key token timestamp))
	    (gethash from rete-network)))

  (defun get-fact-with-index (index)
    "Returns the fact instance with fact-index <index>."
    (gethash index working-memory))

  (defun get-fact-index-of (fact)
    "Returns the fact-index of <fact>."
    (gethash fact working-memory))

  (defun store-activation (key activation memory)
    "Adds <activation> to (if <key> is '+) or removes from (if <key> is '-) <memory>."
    (format *trace-generated-code* "~&(STORE-ACTIVATION :KEY ~S :ACTIVATION ~S :MEMORY ~S)~%" key activation memory)
    (if (eq key '+)
	;; Add activation
	(if (gethash memory rete-network)
	    (unless (member activation (gethash memory rete-network) :test #'equalp)
	      (push activation (gethash memory rete-network)))
	    (setf (gethash memory rete-network) (list activation)))
	;; Remove activation
	(when (gethash memory rete-network)
	  (setf (gethash memory rete-network)
		(remove-if #'(lambda (item)
			       (and (equalp (activation-rule item) (activation-rule activation))
				    (equalp (activation-token item) (activation-token activation))))
			   (gethash memory rete-network))))))

  (defun update-count (key token count-memory)
    "Increments (if <key> is '+) or decrements (if <key> is '-) <count-memory> for <token>."
    (format *trace-generated-code* "~&(UPDATE-COUNT :KEY ~S :TOKEN ~S :COUNT-MEMORY ~S)" key token count-memory)
    (unless (gethash count-memory rete-network)
      (setf (gethash count-memory rete-network) (make-hash-table :test #'equalp)))
    (let ((old-count (gethash token (gethash count-memory rete-network)))
	  (new-count (if (eq key '+)
			 (incf (gethash token (gethash count-memory rete-network) 0))
			 (decf (gethash token (gethash count-memory rete-network) 0)))))
      (values new-count old-count)))

  (defun store (key token memory)
    "Adds <token> to (if <key> is '+) or removes from (if <key> is '-) <memory>."
    (format *trace-generated-code* "~&(STORE :KEY ~S :TOKEN ~S :MEMORY ~S)~%" key token memory)
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

(defmacro defrule (name &body body)
  (if (member name *defrules*)
      (format t "~&Cannot redefine rule: ~A" name)
      (progn
        (push name *defrules*)
        (setf *fact-bindings* (make-hash-table)
              *ce-bindings* (make-hash-table)
              *variable-bindings* (make-hash-table))
        (let ((rhs (if (cdr (member '=> body))
                       (cdr (member '=> body))
                       `(t)))
              (lhs (ldiff body (member '=> body))))
          `(progn
             (compile-lhs ,name 0 ,@lhs)
             (compile-rhs ,name ,@rhs)
             (make-production-node ',name)
             ',name)))))

(defmacro compile-lhs (rule-name position &rest conditional-elements)
  (unless (eq (car conditional-elements) 'nil)
    (cond ((consp (car conditional-elements))
	   (if (equal 'salience (caar conditional-elements))
	       `(progn
		  (setf *salience* ,(cadar conditional-elements))
		  (compile-lhs ,rule-name ,position ,@(cdr conditional-elements)))
	       `(progn
		  (parse-ce ,rule-name ,position ,(car conditional-elements))
		  (compile-lhs ,rule-name ,(+ position 1) ,@(cdr conditional-elements)))))
	  ((variable-p (car conditional-elements))
	   (progn
	     (assert (eq (cadr conditional-elements) '<-))
	     `(progn
		(parse-pattern-ce ,rule-name ,position ,(car conditional-elements) ,(caddr conditional-elements))
		(compile-lhs ,rule-name ,(+ position 1) ,@(cdddr conditional-elements))))))))

(defmacro parse-ce (rule-name position conditional-element)
  (let ((ce-type (car conditional-element)))
    (case ce-type
      (not `(parse-not-ce ,rule-name ,position ,conditional-element))
      (test `(parse-test-ce ,rule-name ,position ,conditional-element))
      (otherwise `(parse-pattern-ce ,rule-name ,position nil ,conditional-element)))))

(defmacro parse-not-ce (rule-name position conditional-element)
  (if (eq position 0)
      (format t "A Not-CE cannot appear FIRST in a rule!") ; TBD! Raise exception!?
      (if (> (length (cdr conditional-element)) 1)
	  (format t "A Not-CE cannot contain more than one Pattern-CE!") ; TBD!
	  `(let* ((alpha-node '())
		  (not-node '()))
	     (setf alpha-node (make-alpha-nodes ',rule-name ',(caadr conditional-element) ',(cadr conditional-element) nil ,position))
	     (setf (gethash ,position *nodes*) alpha-node) ; TBD! This should be done differently!?
	     (setf not-node (make-single-not-node ',rule-name ,position))
	     (connect-nodes alpha-node (make-sym not-node "-right"))))))

(defmacro parse-test-ce (rule-name position conditional-element)
  (if (eq position 0)
      (format t "A Test-CE cannot appear FIRST in a rule!") ; TBD! Raise exception!?
      `(let ((left-node (gethash ,(- position 1) *nodes*))
	     (test-node (make-test-node ',rule-name ',(cadr conditional-element) ,position)))
	 (setf (gethash ,position *nodes*) test-node)
	 (connect-nodes left-node test-node))))

(defmacro parse-pattern-ce (rule-name position variable conditional-element)
  (let ((defstruct-name (car conditional-element)))
    `(let ((beta-node '()))
       (unless ,(null variable)
	 (setf (gethash ',variable *fact-bindings*) ,position))
       (multiple-value-bind (alpha-node deferred-tests)
           (make-alpha-nodes ',rule-name ',defstruct-name ',conditional-element ',variable ,position)
         (setf (gethash ,position *nodes*) alpha-node) ; TBD! This should be done differently!?
         (setf beta-node (make-beta-node ',rule-name ,position deferred-tests))
         (connect-nodes alpha-node (make-sym beta-node "-right"))))))

(defun make-alpha-nodes (rule-name defstruct-name conditional-element variable position)
  (let ((prev-node '())
        (deferred-tests '()))
    (dolist (slot (cdr conditional-element))
      (let* ((slot-name (car slot))
	     (slot-binding (if (variable-p (cadr slot))
			       (cadr slot)
			       nil))
	     (slot-constraint (if (null slot-binding)
				  (cadr slot)
				  (caddr slot))))
        (when (defer? slot-binding slot-constraint)
          (push slot-constraint deferred-tests)
          (setq slot-constraint '()))

	(multiple-value-bind (alpha-node alpha-node-name)
            (if (or (and (consp slot-constraint)
                         (not (equalp (car slot-constraint) 'quote)))
                    (symbolp slot-constraint))
                (make-node-with-symbol-constraint rule-name defstruct-name slot-name slot-binding slot-constraint variable position)
                (make-node-with-literal-constraint rule-name defstruct-name slot-name slot-constraint position))
	  (let ((*print-pretty* t))
	    (format *print-generated-code* "~&~S~%" alpha-node))
	  (eval alpha-node)
	  (if prev-node
	      (connect-nodes prev-node alpha-node-name)
	      (add-to-root defstruct-name alpha-node-name))
	  (setf prev-node alpha-node-name))))
    (values prev-node deferred-tests)))

(defun defer? (var constraint)
  (when var
    (cond ((null (car constraint)) '())
          ((atom (car constraint)) (or (and (variable-p (car constraint))
                                            (not (equal var (car constraint))))
                                       (defer? var (cdr constraint))))
          ((consp (car constraint)) (or (defer? var (car constraint))
                                        (defer? var (cdr constraint)))))))

(defun make-beta-node (rule-name position deferred-tests)
  (let* ((left-node (unless (eq position 0)
		      (gethash (- position 1) *nodes*)))
	 (right-node (gethash position *nodes*))
	 (beta-node-name (make-sym "BETA/" rule-name "-" (format nil "~d" position)))
	 (left-activate (make-sym beta-node-name "-LEFT"))
	 (right-activate (make-sym beta-node-name "-RIGHT"))
	 (beta-node (if left-node
			`(let ((left-memory  ',(make-sym "MEMORY/" left-node))
			       (right-memory ',(make-sym "MEMORY/" right-node)))
			   (defun ,left-activate (key token timestamp)
			     (format *trace-generated-code* "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%" ',left-activate key token timestamp)
			     (dolist (fact (contents-of right-memory))
			       (let ((tok (append token (list fact))))
				 (when (and ,@(make-binding-test position) ,@(expand-variables-token deferred-tests))
				   (store key tok ',(make-sym "MEMORY/" beta-node-name))
				   (propagate key tok timestamp ',beta-node-name)))))
			   (defun ,right-activate (key fact timestamp)
			     (format *trace-generated-code* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',right-activate key fact timestamp)
			     (dolist (token (contents-of left-memory))
			       (let ((tok (append token (list fact))))
				 (when (and ,@(make-binding-test position) ,@(expand-variables-token deferred-tests))
				   (store key tok ',(make-sym "MEMORY/" beta-node-name))
				   (propagate key tok timestamp ',beta-node-name))))))
			;; Left-input adapter
			`(defun ,right-activate (key fact timestamp)
			   (format *trace-generated-code* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',right-activate key fact timestamp)
			   (store key (list fact) ',(make-sym "MEMORY/" beta-node-name))
			   (propagate key (list fact) timestamp ',beta-node-name)))))
    (let ((*print-pretty* t))
      (format *print-generated-code* "~&~S~%" beta-node))
    (eval beta-node)
    (unless (eq position 0)
      (connect-nodes left-node left-activate))
    (setf (gethash position *nodes*) beta-node-name)))

(defun make-single-not-node (rule-name position)
  (let* ((left-node (gethash (- position 1) *nodes*))
	 (right-node (gethash position *nodes*))
	 (not-node-name (make-sym "NOT/" rule-name "-" (format nil "~D" position)))
	 (left-activate (make-sym not-node-name "-LEFT"))
	 (right-activate (make-sym not-node-name "-RIGHT"))
	 (not-node `(let ((left-memory ',(make-sym "MEMORY/" left-node))
			  (right-memory ',(make-sym "MEMORY/" right-node)))
		      (defun ,left-activate (key token timestamp)
			(format *trace-generated-code* "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%" ',left-activate key token timestamp)
			(if (eq (length (contents-of right-memory)) 0)
			    (progn
                              (update-count key token ',(make-sym "COUNT-MEMORY/" not-node-name))
			      (store key token ',(make-sym "MEMORY/" not-node-name))
			      (propagate key token timestamp ',not-node-name))			    
			    (dolist (fact (contents-of right-memory))
			      (let ((tok (append token (list fact))))
				(when (and ,@(make-binding-test position))
				  (multiple-value-bind (new-count old-count)
				      (update-count key tok ',(make-sym "COUNT-MEMORY/" not-node-name))
                                    (declare (ignore old-count))
				    (when (eq new-count 0)
				      (store key token ',(make-sym "MEMORY/" not-node-name))
				      (propagate key token timestamp ',not-node-name))))))))
		      (defun ,right-activate (key fact timestamp)
			(format *trace-generated-code* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',right-activate key fact timestamp)
			(dolist (token (contents-of left-memory))
			  (let ((tok (append token (list fact)))) ; TBD! This is not neccessary?!
			    (when (and ,@(make-binding-test position))
			      (multiple-value-bind (new-count old-count)
				  (update-count key tok ',(make-sym "COUNT-MEMORY/" not-node-name))
                                (store key token ',(make-sym "MEMORY/" not-node-name))
				(cond ((and (eq new-count 0)
					    (eq old-count 1)
					    (eq key '-))
				       (propagate '+ token timestamp ',not-node-name))
				      ((and (eq new-count 1)
					    (or (eq old-count 0)
						(eq old-count nil))
					    (eq key '+))
				       (propagate '- token timestamp ',not-node-name)))))))))))
    (let ((*print-pretty* t))
      (format *print-generated-code* "~&~S~%" not-node))
    (eval not-node)
    (connect-nodes left-node left-activate)
    (setf (gethash position *nodes*) not-node-name)))

(defun make-test-node (rule-name test-form position)
  (let ((test-node-name (make-sym "TEST/" rule-name "-" (format nil "~D" position)))
	(list-of-fact-bindings '())
	(list-of-variable-bindings '()))
    (maphash #'(lambda (key value)
		 (push (make-fact-binding key value) list-of-fact-bindings))
	     *fact-bindings*)
    (maphash #'(lambda (key value)
		 (push (make-variable-binding key value) list-of-variable-bindings))
	     *variable-bindings*)

    (let ((test-node
	   `(defun ,test-node-name (key token timestamp)
	      (format *trace-generated-code* "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%" ',test-node-name key token timestamp)
	      (let* (,@list-of-fact-bindings
		     ,@list-of-variable-bindings)
		(when ,test-form
		  (store key token ',(make-sym "MEMORY/" test-node-name))
		  (propagate key token timestamp ',test-node-name))))))
      (let ((*print-pretty* t))
	(format *print-generated-code* "~&~S~%" test-node))
      (eval test-node))
    test-node-name))

(defun make-binding-test (position)
  (let ((result '(t))) ; zero join
    (maphash #'(lambda (k v)
		 (declare (ignore k))
		 (when (> (length v) 1)
		   (let ((prev '()))
		     (dolist (b v)
		       (if (eql position (caddr b))
			   (when prev
			     (push `(equalp (,(car b) (nth ,(caddr b) tok)) (,(car prev) (nth ,(caddr prev) tok))) result))
			   (setf prev b))))))
	     *variable-bindings*)
    result))

(defun make-production-node (rule-name)
  (let* ((production-node-name (make-sym "PRODUCTION/" rule-name))
	 (production-memory (make-sym "MEMORY/PRODUCTION/" rule-name))
	 (production-node `(defun ,production-node-name (key token timestamp)
			     (format *trace-generated-code* "~&(~A :KEY ~S :TOKEN ~S :TIMESTAMP ~S)~%" ',production-node-name key token timestamp)
			     (if (eq key '+)
				 (format *activations* "~&=> ACTIVATION: ~A ~S~%" ',rule-name token)
				 (format *activations* "~&<= ACTIVATION: ~A ~S~%" ',rule-name token))
			     (store-activation key (make-activation :rule ',rule-name
								    :salience ,*salience*
								    :token token
								    :timestamp timestamp
								    :rhs-function #',(make-sym "RHS/" rule-name)
								    :production-memory ',production-memory)
					       ',production-memory))))
    (let ((*print-pretty* t))
      (format *print-generated-code* "~&~S~%" production-node))
    (eval production-node)
    (connect-nodes (gethash (- (hash-table-count *nodes*) 1) *nodes*) production-node-name)
    (add-to-production-nodes production-node-name)))

(defun make-node-with-literal-constraint (rule-name defstruct-name slot-name slot-constraint position)
  (let ((node-name (make-sym "ALPHA/" rule-name "-" (format nil "~A" position) "/" defstruct-name "-" slot-name)))
    (values
     `(defun ,node-name (key fact timestamp)
	(format *trace-generated-code* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',node-name key fact timestamp)
	(when (equalp (,(make-sym defstruct-name "-" slot-name) fact) ,slot-constraint)
	  (store key fact ',(make-sym "MEMORY/" node-name))
	  (propagate key fact timestamp ',node-name)))
     node-name)))

(defun make-node-with-symbol-constraint (rule-name defstruct-name slot-name slot-binding slot-constraint variable position)
  (let* ((node-name (make-sym "ALPHA/" rule-name "-" (format nil "~A" position) "/" defstruct-name "-" slot-name))
	 (slot-accessor (make-sym defstruct-name "-" slot-name))
	 (binding-constraint (parse-binding-constraint slot-binding slot-constraint slot-accessor variable position))
         (constraint (cond ((and binding-constraint slot-constraint)
                            `(and ,binding-constraint ,(expand-variables slot-constraint)))
                           (binding-constraint
                            binding-constraint)
                           (slot-constraint
                            (expand-variables slot-constraint))
                           (t nil))))
    (values
     `(defun ,node-name (key fact timestamp)
	(format *trace-generated-code* "~&(~A :KEY ~S :FACT ~S :TIMESTAMP ~S)~%" ',node-name key fact timestamp)
	(when ,constraint
	  (store key fact ',(make-sym "MEMORY/" node-name))
	  (propagate key fact timestamp ',node-name)))
     node-name)))

(defun parse-binding-constraint (slot-binding slot-constraint slot-accessor variable position)
  (let ((fact-variable (if variable
			   variable
			   (gethash position *ce-bindings*)))
	(binding (gethash slot-binding *variable-bindings*)))
    (when (not (null slot-binding))
      ;; Make sure that this slot-value is reachable in the RHS
      (when (null fact-variable)
	(setf fact-variable (gensym))
	(setf (gethash position *ce-bindings*) fact-variable)
	(setf (gethash fact-variable *fact-bindings*) position))

      (if (not binding)
	  (progn ; This is the first binding for this variable
	    (setf (gethash slot-binding *variable-bindings*) (list (list slot-accessor fact-variable position)))
	    (when (null slot-constraint) t))
	  
	  (progn
	    (dolist (b binding)
	      ;; If this position already has a binding for this variable we'll
	      ;; return an alpha-constraint
	      (when (equal position (caddr b))
		(return `(equalp (,(car b) fact) (,slot-accessor fact)))))

	    ;; Create a new binding
	    (setf (gethash slot-binding *variable-bindings*)
		  (append (gethash slot-binding *variable-bindings*)
			  (list (list slot-accessor fact-variable position))))
	    (when (null slot-constraint) t))))))

(defun expand-variable (variable-name)
  (car (gethash variable-name *variable-bindings*)))

(defun expand-variables (form)
  (maphash #'(lambda (key value)
	       (nsubst `(,(caar value) fact) key form))
	   *variable-bindings*)
  form)

(defun expand-variables-token (form)
  (maphash #'(lambda (key value)
	       (nsubst `(,(caar value) (nth ,(caddar value) tok)) key form))
	   *variable-bindings*)
  form)

(defun make-variable-binding (key value)
  ;; variable-name : ((accessor fact-variable position) ...) -> (variable-name (accessor fact-variable))
  `(,key (,(caar value) ,(cadar value))))

(defun make-fact-binding (key value)
  ;; variable-name : position
  `(,key (nth ,value token)))

(defmacro compile-rhs (rule-name &rest rhs)
  (let ((list-of-fact-bindings '())
	(list-of-variable-bindings '()))
    (maphash #'(lambda (key value)
		 (push (make-fact-binding key value) list-of-fact-bindings))
	     *fact-bindings*)
    (maphash #'(lambda (key value)
		 (push (make-variable-binding key value) list-of-variable-bindings))
	     *variable-bindings*)
    (let* ((rhs-function-name (make-sym "RHS/" rule-name))
	   (rhs-function `(defun ,rhs-function-name (activation)
			    (format *trace-generated-code* "~&(~A :ACTIVATION ~S)~%" ',rhs-function-name activation)
			    (let* ((token (activation-token activation))
				   ,@list-of-fact-bindings
				   ,@list-of-variable-bindings)
			      ,@rhs))))
      (let ((*print-pretty* t))
	(format *print-generated-code* "~&~S~%" rhs-function))
      rhs-function)))
