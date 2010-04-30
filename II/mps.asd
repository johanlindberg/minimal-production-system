(defpackage :mps-system
  (:use :cl :asdf))
(in-package :mps-system)
     
(defsystem :mps
  :description "Minimal Production System (MPS), a small and portable production system for Common Lisp."
  :version "0.9"
  :author "Johan Lindberg <johan@pulp.se>"
  :licence "GPL"
  :components ((:file "runtime")
	       (:file "compiler" :depends-on ("runtime"))))

