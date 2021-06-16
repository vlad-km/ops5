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

;;;; This file contains the functions that match working memory
;;;; elements against productions LHS.

#+ops5
(in-package "OPS")



;;; External global variables

(defvar *current-token* nil)


;;; Internal global variables

(defvar *alpha-data-part* nil)
(defvar *alpha-flag-part* nil)
(defvar *flag-part* nil)
(defvar *data-part* nil)
(defvar *sendtocall* nil)
(defvar *side* nil)

;; Define register variables *c1* through *c127*
(macrolet ((define-registers ()
             `(progn
                ,@(loop for i from 1 to 127
                        for name = (read-from-string (format nil "*c~A*" i))
                        collect `(defvar ,name)))))
  (define-registers))



;;; Network interpreter


(defun match-init ()
  (setq *current-token* 0.))


(defun match (flag wme)
  (sendto flag (list wme) 'left (list *first-node*)))

; note that eval-nodelist is not set up to handle building
; productions.  would have to add something like ops4's build-flag

(defun eval-nodelist (nl)
  (dolist (node nl)
    (setq *sendtocall* nil)
    (setq *last-node* node)
    (apply (car node) (cdr node)))) 

(defun sendto (flag data side nl)
  (dolist (node nl)
    (setq *side* side)
    (setq *flag-part* flag)
    (setq *data-part* data)
    (setq *sendtocall* t)
    (setq *last-node* node)
    (apply (car node) (cdr node)))) 

; &bus sets up the registers for the one-input nodes.  note that this
(defun &bus (outs)
  (prog (dp)
    (setq *alpha-flag-part* *flag-part*)
    (setq *alpha-data-part* *data-part*)
    (setq dp (car *data-part*))
    (setq *c1* (pop dp))
    (setq *c2* (pop dp))
    (setq *c3* (pop dp))
    (setq *c4* (pop dp))
    (setq *c5* (pop dp))
    (setq *c6* (pop dp))
    (setq *c7* (pop dp))
    (setq *c8* (pop dp))
    (setq *c9* (pop dp))
    (setq *c10* (pop dp))
    (setq *c11* (pop dp))
    (setq *c12* (pop dp))
    (setq *c13* (pop dp))
    (setq *c14* (pop dp))
    (setq *c15* (pop dp))
    (setq *c16* (pop dp))
    (setq *c17* (pop dp))
    (setq *c18* (pop dp))
    (setq *c19* (pop dp))
    (setq *c20* (pop dp))
    (setq *c21* (pop dp))
    (setq *c22* (pop dp))
    (setq *c23* (pop dp))
    (setq *c24* (pop dp))
    (setq *c25* (pop dp))
    (setq *c26* (pop dp))
    (setq *c27* (pop dp))
    (setq *c28* (pop dp))
    (setq *c29* (pop dp))
    (setq *c30* (pop dp))
    (setq *c31* (pop dp))
    (setq *c32* (pop dp))
    (setq *c33* (pop dp))
    (setq *c34* (pop dp))
    (setq *c35* (pop dp))
    (setq *c36* (pop dp))
    (setq *c37* (pop dp))
    (setq *c38* (pop dp))
    (setq *c39* (pop dp))
    (setq *c40* (pop dp))
    (setq *c41* (pop dp))
    (setq *c42* (pop dp))
    (setq *c43* (pop dp))
    (setq *c44* (pop dp))
    (setq *c45* (pop dp))
    (setq *c46* (pop dp))
    (setq *c47* (pop dp))
    (setq *c48* (pop dp))
    (setq *c49* (pop dp))
    (setq *c50* (pop dp))
    (setq *c51* (pop dp))
    (setq *c52* (pop dp))
    (setq *c53* (pop dp))
    (setq *c54* (pop dp))
    (setq *c55* (pop dp))
    (setq *c56* (pop dp))
    (setq *c57* (pop dp))
    (setq *c58* (pop dp))
    (setq *c59* (pop dp))
    (setq *c60* (pop dp))
    (setq *c61* (pop dp))
    (setq *c62* (pop dp))
    (setq *c63* (pop dp))
    (setq *c64* (pop dp))
    ;-------- added for 127 atr
    (setq *c65* (pop dp))
    (setq *c66* (pop dp))
    (setq *c67* (pop dp))
    (setq *c68* (pop dp))
    (setq *c69*(pop dp))
    (setq *c70* (pop dp))
    (setq *c71* (pop dp))
    (setq *c72* (pop dp))
    (setq *c73* (pop dp))
    (setq *c74* (pop dp))
    (setq *c75* (pop dp))
    (setq *c76* (pop dp))
    (setq *c77* (pop dp))
    (setq *c78* (pop dp))
    (setq *c79*(pop dp))
    (setq *c80* (pop dp))
    (setq *c81* (pop dp))
    (setq *c82* (pop dp))
    (setq *c83* (pop dp))
    (setq *c84* (pop dp))
    (setq *c85* (pop dp))
    (setq *c86* (pop dp))
    (setq *c87* (pop dp))
    (setq *c88* (pop dp))
    (setq *c89*(pop dp))
    (setq *c90* (pop dp))
    (setq *c91* (pop dp))
    (setq *c92* (pop dp))
    (setq *c93* (pop dp))
    (setq *c94* (pop dp))
    (setq *c95* (pop dp))
    (setq *c96* (pop dp))
    (setq *c97* (pop dp))
    (setq *c98* (pop dp))
    (setq *c99*(pop dp))
    (setq *c100* (pop dp))
    (setq *c101* (pop dp))
    (setq *c102* (pop dp))
    (setq *c103* (pop dp))
    (setq *c104* (pop dp))
    (setq *c105* (pop dp))
    (setq *c106* (pop dp))
    (setq *c107* (pop dp))
    (setq *c108* (pop dp))
    (setq *c109*(pop dp))
    (setq *c110* (pop dp))
    (setq *c111* (pop dp))
    (setq *c112* (pop dp))
    (setq *c113* (pop dp))
    (setq *c114* (pop dp))
    (setq *c115* (pop dp))
    (setq *c116* (pop dp))
    (setq *c117* (pop dp))
    (setq *c118* (pop dp))
    (setq *c119*(pop dp))
    (setq *c120* (pop dp))
    (setq *c121* (pop dp))
    (setq *c122* (pop dp))
    (setq *c123* (pop dp))
    (setq *c124* (pop dp))
    (setq *c125* (pop dp))
    (setq *c126* (pop dp))
    (setq *c127* (pop dp))
    ;(setq *c128* (car dp))
    ;--------
    (eval-nodelist outs))) 

(defun &any (outs register const-list)
  (prog (z c)
     (setq z (fast-symeval register))
     (cond ((numberp z) (go number)))
   symbol
     (cond ((null const-list) (return nil))
		       ((eq (car const-list) z) (go ok))
		       (t (setq const-list (cdr const-list)) (go symbol)))
   number
     (cond ((null const-list) (return nil))
		       ((and (numberp (setq c (car const-list)))
		             (=alg c z))
		        (go ok))
		       (t (setq const-list (cdr const-list)) (go number)))
   ok
     (eval-nodelist outs))) 

(defun teqa (outs register constant)
  (and (eq (fast-symeval register) constant) (eval-nodelist outs))) 

(defun tnea (outs register constant)
  (and (not (eq (fast-symeval register) constant)) (eval-nodelist outs))) 

(defun txxa (outs register constant)
  (declare (ignore constant))
  (and (symbolp (fast-symeval register)) (eval-nodelist outs))) 

(defun teqn (outs register constant)
  (let ((z (fast-symeval register)))
    (when (and (numberp z)
	       (=alg z constant))
      (eval-nodelist outs)))) 

(defun tnen (outs register constant)
  (let ((z (fast-symeval register)))
    (when (or (not (numberp z))
	      (not (=alg z constant)))
      (eval-nodelist outs)))) 

(defun txxn (outs register constant)
  (declare (ignore constant))
  (let ((z (fast-symeval register)))
    (when (numberp z)
      (eval-nodelist outs)))) 

(defun tltn (outs register constant)
  (let ((z (fast-symeval register)))
    (when (and (numberp z)
	       (> constant z))
      (eval-nodelist outs)))) 

(defun tgtn (outs register constant)
  (let ((z (fast-symeval register)))
    (when (and (numberp z)
	             (> z constant))
      (eval-nodelist outs)))) 

(defun tgen (outs register constant)
  (let ((z (fast-symeval register)))
    (when (and (numberp z)
	             (not (> constant z)))
      (eval-nodelist outs)))) 

(defun tlen (outs register constant)
  (let ((z (fast-symeval register)))
    (when (and (numberp z)
	             (not (> z constant)))
      (eval-nodelist outs)))) 

(defun teqs (outs vara varb)
  (let* ((a (fast-symeval vara)) 
	       (b (fast-symeval varb)))
    (cond ((eq a b) 
	         (eval-nodelist outs))
	        ((and (numberp a)
		            (numberp b)
		            (=alg a b))
	         (eval-nodelist outs))))) 

(defun tnes (outs vara varb)
  (let* ((a (fast-symeval vara)) 
	       (b (fast-symeval varb)))
    (cond ((eq a b) 
	         nil)
	        ((and (numberp a)
		            (numberp b)
		            (=alg a b))
	         nil)
	        (t (eval-nodelist outs))))) 

(defun txxs (outs vara varb)
  (let* ((a (fast-symeval vara)) 
	       (b (fast-symeval varb)))
    (cond ((and (numberp a) (numberp b)) (eval-nodelist outs))
	        ((and (not (numberp a)) (not (numberp b)))
	         (eval-nodelist outs))))) 

(defun tlts (outs vara varb)
  (let* ((a (fast-symeval vara)) 
	       (b (fast-symeval varb)))
    (when (and (numberp a)
	             (numberp b)
	             (> b a))
      (eval-nodelist outs)))) 

(defun tgts (outs vara varb)
  (let* ((a (fast-symeval vara)) 
	       (b (fast-symeval varb)))
    (when (and (numberp a)
	             (numberp b)
	             (> a b))
      (eval-nodelist outs)))) 

(defun tges (outs vara varb)
  (let* ((a (fast-symeval vara)) 
	       (b (fast-symeval varb)))
    (when (and (numberp a)
	             (numberp b)
	             (not (> b a)))
      (eval-nodelist outs)))) 

(defun tles (outs vara varb)
  (let* ((a (fast-symeval vara)) 
	       (b (fast-symeval varb)))
    (when (and (numberp a)
	             (numberp b)
	             (not (> a b)))
      (eval-nodelist outs)))) 

(defun &two (left-outs right-outs)
  (prog (fp dp)
     (cond (*sendtocall*
	          (setq fp *flag-part*)
	          (setq dp *data-part*))
	         (t
	          (setq fp *alpha-flag-part*)
	          (setq dp *alpha-data-part*)))
     (sendto fp dp 'left left-outs)
     (sendto fp dp 'right right-outs))) 

(defun &mem (left-outs right-outs memory-list)
  (prog (fp dp)
     (cond (*sendtocall*
	          (setq fp *flag-part*)
	          (setq dp *data-part*))
	         (t
	          (setq fp *alpha-flag-part*)
	          (setq dp *alpha-data-part*)))
     (sendto fp dp 'left left-outs)
     (add-token memory-list fp dp nil)
     (sendto fp dp 'right right-outs))) 

(defun &and (outs lpred rpred tests)
  (let ((mem (if (eq *side* 'right) 
		             (memory-part lpred)
		             (memory-part rpred))))
    (cond ((not mem) nil)
	        ((eq *side* 'right)
	         (and-right outs mem tests))
	        (t
	         (and-left outs mem tests))))) 

(defun and-left (outs mem tests)
  (prog (fp dp memdp tlist tst lind rind res)
     (setq fp *flag-part*)
     (setq dp *data-part*)
   fail
     (and (null mem) (return nil))
     (setq memdp (car mem))
     (setq mem (cdr mem))
     (setq tlist tests)
   tloop
     (and (null tlist) (go succ))
     (setq tst (car tlist))
     (setq tlist (cdr tlist))
     (setq lind (car tlist))
     (setq tlist (cdr tlist))
     (setq rind (car tlist))
     (setq tlist (cdr tlist))
     ;;###        (comment the next line differs in and-left & -right)
     (setq res (funcall tst (gelm memdp rind) (gelm dp lind)))
     (cond (res (go tloop))
	         (t (go fail)))
   succ 
     ;;###	(comment the next line differs in and-left & -right)
     (sendto fp (cons (car memdp) dp) 'left outs)
     (go fail))) 

(defun and-right (outs mem tests)
  (prog (fp dp memdp tlist tst lind rind res)
     (setq fp *flag-part*)
     (setq dp *data-part*)
   fail
     (and (null mem) (return nil))
     (setq memdp (car mem))
     (setq mem (cdr mem))
     (setq tlist tests)
   tloop
     (and (null tlist) (go succ))
     (setq tst (car tlist))
     (setq tlist (cdr tlist))
     (setq lind (car tlist))
     (setq tlist (cdr tlist))
     (setq rind (car tlist))
     (setq tlist (cdr tlist))
     ;;###        (comment the next line differs in and-left & -right)
     (setq res (funcall tst (gelm dp rind) (gelm memdp lind)))
     (cond (res (go tloop))
	         (t (go fail)))
   succ 
     ;;###        (comment the next line differs in and-left & -right)
     (sendto fp (cons (car dp) memdp) 'right outs)
     (go fail))) 


(defun teqb (new eqvar)
  (cond ((eq new eqvar) t)
	      ((not (numberp new)) nil)
	      ((not (numberp eqvar)) nil)
	      ((=alg new eqvar) t)
	      (t nil))) 

(defun tneb (new eqvar)
  (cond ((eq new eqvar) nil)
	      ((not (numberp new)) t)
	      ((not (numberp eqvar)) t)
	      ((=alg new eqvar) nil)
	      (t t))) 

(defun tltb (new eqvar)
  (cond ((not (numberp new)) nil)
	      ((not (numberp eqvar)) nil)
	      ((> eqvar new) t)
	      (t nil))) 

(defun tgtb (new eqvar)
  (cond ((not (numberp new)) nil)
	      ((not (numberp eqvar)) nil)
	      ((> new eqvar) t)
	      (t nil))) 

(defun tgeb (new eqvar)
  (cond ((not (numberp new)) nil)
	      ((not (numberp eqvar)) nil)
	      ((not (> eqvar new)) t)
	      (t nil))) 

(defun tleb (new eqvar)
  (cond ((not (numberp new)) nil)
	      ((not (numberp eqvar)) nil)
	      ((not (> new eqvar)) t)
	      (t nil))) 

(defun txxb (new eqvar)
  (cond ((numberp new)
	       (cond ((numberp eqvar) t)
	             (t nil)))
	      ((numberp eqvar) nil)
	      (t t))) 

(defun &p (rating name var-dope ce-var-dope rhs)
  (declare (ignore var-dope ce-var-dope rhs))
  (prog (fp dp)
     (cond (*sendtocall*
	          (setq fp *flag-part*)
	          (setq dp *data-part*))
	         (t
	          (setq fp *alpha-flag-part*)
	          (setq dp *alpha-data-part*)))
     (and (member fp '(nil old)) (removecs name dp))
     (and fp (insertcs name dp rating)))) 

(defun &old (a b c d e)
  (declare (ignore a b c d e))
  nil) 

(defun &not (outs lmem rpred tests)
  (cond ((and (eq *side* 'right) (eq *flag-part* 'old)) nil)
	      ((eq *side* 'right) (not-right outs (car lmem) tests))
	      (t (not-left outs (memory-part rpred) tests lmem)))) 

(defun not-left (outs mem tests own-mem)
  (prog (fp dp memdp tlist tst lind rind res c)
     (setq fp *flag-part*)
     (setq dp *data-part*)
     (setq c 0.)
   fail
     (and (null mem) (go fin))
     (setq memdp (car mem))
     (setq mem (cdr mem))
     (setq tlist tests)
   tloop
     (and (null tlist) (setq c (1+ c)) (go fail))
     (setq tst (car tlist))
     (setq tlist (cdr tlist))
     (setq lind (car tlist))
     (setq tlist (cdr tlist))
     (setq rind (car tlist))
     (setq tlist (cdr tlist))
     ;;###        (comment the next line differs in not-left & -right)
     (setq res (funcall tst (gelm memdp rind) (gelm dp lind)))
     (cond (res (go tloop))
	         (t (go fail)))
   fin
     (add-token own-mem fp dp c)
     (and (== c 0.) (sendto fp dp 'left outs)))) 

(defun not-right (outs mem tests)
  (prog (fp dp memdp tlist tst lind rind res newfp inc newc)
     (setq fp *flag-part*)
     (setq dp *data-part*)
     (cond ((not fp) (setq inc -1.) (setq newfp 'new))
	         ((eq fp 'new) (setq inc 1.) (setq newfp nil))
	         (t (return nil)))
   fail
     (and (null mem) (return nil))
     (setq memdp (car mem))
     (setq newc (cadr mem))
     (setq tlist tests)
   tloop
     (and (null tlist) (go succ))
     (setq tst (car tlist))
     (setq tlist (cdr tlist))
     (setq lind (car tlist))
     (setq tlist (cdr tlist))
     (setq rind (car tlist))
     (setq tlist (cdr tlist))
     ;;###        (comment the next line differs in not-left & -right)
     (setq res (funcall tst (gelm dp rind) (gelm memdp lind)))
     (cond (res (go tloop))
	         (t (setq mem (cddr mem)) (go fail)))
   succ
     (setq newc (+ inc newc))           ;"plus" changed to "+" by gdw
     (rplaca (cdr mem) newc)
     (cond ((or (and (== inc -1.) (== newc 0.))
	              (and (== inc 1.) (== newc 1.)))
	          (sendto newfp memdp 'right outs)))
     (setq mem (cddr mem))
     (go fail))) 

;;; Node memories


(defun add-token (memlis flag data-part num)
  (let (was-present)
    (cond ((eq flag 'new)
	         (setq was-present nil)
	         (real-add-token memlis data-part num))
	        ((not flag) 
	         (setq was-present (remove-old memlis data-part num)))
	        ((eq flag 'old) (setq was-present t)))
    was-present))

(defun real-add-token (lis data-part num)
  (incf *current-token*)
  (when num 
    (push num (car lis)))
  (push data-part (car lis))) 

(defun remove-old (lis data num)
  (if num 
      (remove-old-num lis data)
      (remove-old-no-num lis data))) 

(defun remove-old-num (lis data)
  (prog (m next last)
     (setq m (car lis))
     (cond ((atom m) (return nil))
	         ((top-levels-eq data (car m))
	          (setq *current-token* (1- *current-token*))
	          (rplaca lis (cddr m))
	          (return (car m))))
     (setq next m)
   loop
     (setq last next)
     (setq next (cddr next))
     (cond ((atom next) (return nil))
	         ((top-levels-eq data (car next))
	          (rplacd (cdr last) (cddr next))
	          (setq *current-token* (1- *current-token*))
	          (return (car next)))
	         (t (go loop))))) 

(defun remove-old-no-num (lis data)
  (prog (m next last)
     (setq m (car lis))
     (cond ((atom m) (return nil))
	         ((top-levels-eq data (car m))
	          (setq *current-token* (1- *current-token*))
	          (rplaca lis (cdr m))
	          (return (car m))))
     (setq next m)
   loop
     (setq last next)
     (setq next (cdr next))
     (cond ((atom next) (return nil))
	         ((top-levels-eq data (car next))
	          (rplacd last (cdr next))
	          (setq *current-token* (1- *current-token*))
	          (return (car next)))
	         (t (go loop))))) 

#+ops5
(in-package :cl-user)

;;; *EOF*
