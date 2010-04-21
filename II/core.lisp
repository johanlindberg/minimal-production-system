;; Minimal Production System II
;; Core functionality.

;; Runtime data.

(defvar *memory* (make-hash-table))
(defvar *activations* (make-hash-table))

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
