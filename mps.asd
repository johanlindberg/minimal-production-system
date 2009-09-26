(defpackage :mps-system
  (:use :common-lisp :asdf))
(in-package :mps-system)

(defsystem :MPS
  :description "MPS - Minimal Production System"
  :version "0.1"
  :author "Johan Lindberg, Pulp Software <johan@pulp.se>"
  :licence "GPL"
  :components ((:file "mps")))
