(in-package :asdf)
     
(defsystem "mps-system"
  :description "Minimal Production System (MPS), a small and portable production system for Common Lisp."
  :version "0.9"
  :author "Johan Lindberg <johan@pulp.se>"
  :licence "GPL"
  :components ((:file "core")
	       (:file "lang" :depends-on ("core"))))

