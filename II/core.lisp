;; Minimal Production System II
;; Core functionality.

;; Runtime data.

(defvar *memory* (make-hash-table))
(defvar *activations* (make-hash-table))

(defvar *object-type-node* (make-hash-table))

(defvar *current-timestamp* 0)
(defvar *current-fact-index* 0)

;; Object type node

(defun object-type-node (key timestamp &rest facts)
  (declare (ignore key timestamp facts))) ; dummy impl

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

(defmacro store-activation (key token memory)
  `(store ,key ,token ,memory *activations*))

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
      (unless (gethash fact *memory*)
	(let ((fact-copy (copy-structure fact)))
	  (incf *current-fact-index*)
	  (setf (gethash fact-copy *memory*) *current-fact-index*)
	  (setf (gethash *current-fact-index* *memory*) fact-copy)
	  (incf count)

	  (object-type-node '+ *current-timestamp* fact-copy))))
    count))

