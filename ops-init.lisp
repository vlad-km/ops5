;;; -*- mode:lisp; coding:utf-8 -*-

;;; ****************************************************************
;;; OPS5 Interpreter ***********************************************
;;; ****************************************************************
;;; This Common Lisp version of OPS5 is in the public domain.  It is based
;;; in part on based on a Franz Lisp implementation done by Charles L. Forgy
;;; at Carnegie-Mellon University, which was placed in the public domain by
;;; the author in accordance with CMU policies.  Ported to Common Lisp by 
;;; George Wood and Jim Kowalski. CMU Common Lisp modifications by
;;; Dario Guise, Skef Wholey, Michael Parzen, and Dan Kuokka. 
;;; Modified to work in CLtL1, CLtL2 and X3J13 compatible lisps by 
;;; Mark Kantrowitz on 14-OCT-92.
;;; 
;;; This code is made available is, and without warranty of any kind by the
;;; authors or by Carnegie-Mellon University.
;;;

;;; 15-OCT-92 mk    Modified definition of RESET-OPS.

#+ops5
(in-package "OPS")

(defparameter *ops-version* "19-OCT-92")

(defun ops-init ()
  (backup-init)
  (compile-init)
  (main-init)
  (match-init)
  (io-init)
  (rhs-init)
  (format t "~%Common Lisp OPS5 interpreter, version ~A.~%" *ops-version*))

(defun reset-ops ()
  (format t "~%Resetting OPS5 interpreter ~%")
  (remove! *)
  (ops-init)
  (clear-ops-hash-tables)
  ;; (i-g-v)
  (setq *class-list* nil
	      *pcount* 0))

#+ops5
(in-package :cl-user)

;;; *EOF*

