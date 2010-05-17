;; Minimal Production System II
;; Core functionality.

;; Runtime data.

(defvar *memory* (make-hash-table :test #'equalp)) ; node memories
(defvar *working-memory* (make-hash-table :test #'equalp))

(defvar *activations* (make-hash-table :test #'equalp))
(defvar *object-type-node* (make-hash-table))

(defvar *defrules* '())

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
(make-object-type-node)

;; Memory access

(defun contents-of (memory &optional (table *memory*))
  "Returns the contents of <memory>."
  (gethash memory table))

(defmacro store-activation (key token timestamp rule salience)
  `(store ,key
	  (make-activation :rule ,rule
			   :salience ,salience
			   :token ,token
			   :timestamp ,timestamp)
	  ,salience
	  *activations*))

(defun store (key token memory &optional (table *memory*))
  (if (eq key '+)
      ;; Add token
      (if (gethash memory table)
	  (unless (member token (gethash memory table) :test #'equalp)
	    (push token (gethash memory table)))
	  (setf (gethash memory table) (list token)))
      ;; Remove token
      (when (gethash memory table)
	(setf (gethash memory table) (remove-if #'(lambda (item)
						    (equalp item token))
						(gethash memory table))))))

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

(defun facts ()
  "Returns all facts in Working Memory."
  (let ((result '()))
    (maphash #'(lambda (key value)
		 (when (numberp value)
		   (push key result)))
	     *working-memory*)
    result))

  (defun clear ()
    "Clears the engine."
    (clrhash *memory*)
    (clrhash *working-memory*)

    (clrhash *activations*)

    (clrhash *object-type-node*)
    (make-object-type-node)

    (setf *defrules* '())

    (setf *current-timestamp* 0)
    (setf *current-fact-index* 0)

    t)
