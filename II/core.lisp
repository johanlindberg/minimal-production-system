;; Minimal Production System II
;; Core functionality.

;; Runtime data.

(defvar *memory* (make-hash-table)) ; node memories
(defvar *working-memory* (make-hash-table))

(defvar *activations* (make-hash-table))

(defvar *object-type-node* (make-hash-table))

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

(defun object-type-node (key timestamp &rest facts) ; dummy impl
  (declare (ignore key timestamp facts)))

(defun make-object-type-node ()
  (let ((body '()))
    (maphash #'(lambda (key value)
		 (let ((result '()))
		   (dolist (v value)
		     (push `(,v key fact timestamp) result))
		   (push `(,key (progn ,@result)) body)))
	     *object-type-node*)
    (emit `(defun object-type-node (key timestamp &rest facts)
	     (dolist (fact facts)
	       (case (type-of fact)
		 ,@body))))))

;; Memory access

(defun contents-of (memory &optional (table *memory*))
  "Returns the contents of <memory>."
  (gethash memory table))

(defmacro store-activation (key token timestamp rule salience)
  `(store ,key (make-activation :rule ,rule
				:salience ,salience
				:token ,token
				:timestamp ,timestamp) *activations*))

(defun store (key token memory &optional (table *memory*))
  (if (eq key '+)
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
