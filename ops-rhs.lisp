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

;;; bug: @vlad-km
;;;   (terpri port)
;;; current JSCL release dont support &optional stream
;;; todo:
;;;   (defun terpri (&optional port) ...)

;;;; This file contains all the functions necessary for RHS actions
;;;; including $actions.

#+ops5
(in-package "OPS")
;; see ops.lisp
; (shadow '(remove write))
; (export '(remove write make modify crlf))

;;; External global variables
(defvar *size-result-array* nil)
(defvar *in-rhs* nil)
(defvar *current-wm* nil)
(defvar *max-wm* nil)
(defvar *action-count* nil)
(defvar *critical* nil)


;;; Internal global variables
(defvar *wmpart-list* nil)
(defvar *wm-filter* nil)
(defvar *wm* nil)
(defvar *old-wm* nil)
(defvar *result-array* nil)
(defvar *variable-memory* nil)
(defvar *last* nil)
(defvar *max-index* nil)
(defvar *next-index* nil)
(defvar *data-matched* nil)
(defvar *ce-variable-memory* nil)
(defvar *rest* nil)
(defvar *build-trace* nil)

;;;; Functions for RHS evaluation
(defun rhs-init ()
  ;; if the size of result-array changes, change the line in i-g-v which
  ;; sets the value of *size-result-array*
  (setq *size-result-array* 255.)                             ;255 /256 set by gdw
  (setq *result-array* (make-array 256 :initial-element nil)) ;jgk
  (setq *in-rhs* nil)
  (setq *build-trace* nil)
  (setq *max-wm* (setq *current-wm* 0.))
  (setq *action-count* 0.)
  (setq *critical* nil)
  (setq *wmpart-list* nil))

(defun eval-rhs (pname data)
  (when *ptrace*
    (let ((port (trace-file)))
      (format port "~%~A. ~A " *cycle-count* pname)
      (time-tag-print data port)))
  (let ((node (gethash pname *topnode-table*)))
    (setq *data-matched* data
	        *p-name* pname
	        *last* nil)
    (init-var-mem (var-part node))
    (init-ce-var-mem (ce-var-part node))
    (begin-record pname data)
    (let ((*in-rhs* t))
      (eval (rhs-part node)))
    (end-record))) 

(defun eval-args (z)
  (prog (r)
     (rhs-tab 1.)
   la
     (and (atom z) (return nil))
     (setq r (pop z))
     (when (eq r '^)
	     (rhs-tab (car z))
	     (setq r (cadr z))
	     (setq z (cddr z)))
     (cond ((eq r '//)
	          ($value (car z))
	          (setq z (cdr z)))
	         (t ($change r)))
     (go la))) 

;;;; RHS actions
;;;; Some of these can be called at the top level.
(defmacro make (&body z)
  `(ops-make ',z))

;;; @vlad-km change remove to remove!
(defmacro remove! (&body z)
  `(ops-remove ',z))

(defmacro modify (&body z)
  `(ops-modify ',z))

(defmacro openfile (&body z)
  `(ops-openfile ',z))

(defmacro closefile (&body z)
  `(ops-closefile ',z))

(defmacro default (&body z)
  `(ops-default ',z))

;;; @vlad-km change write to write!
(defmacro write! (&body z)
  `(ops-write ',z))

(defmacro crlf (&body z)
  `(ops-crlf ',z))

(defmacro tabto (&body z)
  `(ops-tabto ',z))

(defmacro rjust (&body z)
  `(ops-rjust ',z))

(defmacro call (&body z)
  `(ops-call ',z))

;;; 5.3.10. bind 
;;; The action bi nd is used to assign values to variables. There are two forms of calls on bi nd. In the more 
;;; general form bi nd is given two arguments: a variable and an RHS pattern. It evaluates the pattern and then 
;;; assigns to the variable the value that is in position 1 of the result element For example, to add 1 to the 
;;; binding of <x>, the following would be executed. 
;;;   (bind <x> (compute <x> + 1)) 
;;; In the other form of bind, the action is given only one argument - the variable to be bound. When this 
;;; action is executed, a new symbolic atom is created and assigned to the variable. Thus the action 
;;;   (bind <z>) 
;;; is equivalent to 
;;;   (bind <z> (genatom))
(defmacro bind (&body z)
  `(ops-bind ',z))

(defmacro cbind (&body z)
  `(ops-cbind ',z))

(defmacro build (&body z)
  `(ops-build ',z))

;;; 5.2.7. A substr 
;;; The function substr extracts a sequence of values from an existing working memory element and puts 
;;; the values in the result element The function takes three arguments. The first argument is an element 
;;; designator. (See Section 5.1.) This argument indicates which working memory element is to be examined to 
;;; get the values. The second argument should be an integer, an attribute name, or a variable that is bound to an 
;;; integer or attribute name. This argument indicates the first value that is to be extracted. The third argument 
;;; should be an integer, an attribute name, a variable that is bound to an integer or attribute name, or the symbol 
;;; inf. This argument indicates the final value to extract.
;;; For example, if <w> is bound to (a b c d e), 
;;; then evaluating 
;;;    (make .. . ti o (subst r <w> 3 3) .. . ) 
;;; will cause the atom c to be copied into position 10 of the result element When more than one value is 
;;; 25 extracted, die values are placed in contiguous fields in die element; dius 
;;; (make .. . ti l (subst r <w> 2 4) .. . ) 
;;; will cause b to be copied into position 11, c to be copied into position 12, and d to be copied into position 13. 
;;; The special symbol inf indicates that substr is to continue taking values until it reaches the end of the 
;;; element it is extracting them from. Thus 
;;; (make .. . tl 4 (subst r <w> 4 inf) .. . ) 
;;; will copy d into position 14 and e into position 15.
(defmacro substr (&body l)
  `(ops-substr ',l))


;;; 5.27.5. compute 
;;; The function compute evaluates arithmetic expressions. The expressions can contain five operators, +, 
;;; *, // , and \\ , which denote respectively addition, subtraction, multiplication, division, and modulus. 
;;; Standard infix notation is used, but operator precedence is not used; compute evaluates the operators from 
;;; right to left. Parentheses can be used to override the right to left evaluation. Only numbers and variables that 
;;; are bound to numbers can be used in the expressions. Typical calls on compute include 
;;;   (compute <x> + 1) 
;;;   (compute (<b> * <b>) - 4 * <a> * <c>)
(defmacro compute (&body z)
  `(ops-compute ',z))

;;; 5.17A litval 
;;; The function litva l puts into the result element the number which has been assigned to an attribute 
;;; name. That is, if a is an attribute name, then (1 i tval a) determines the number of the field that is used 
;;; for attribute a and puts the number into the result element The function takes one argument, which 
;;; normally is an attribute name or a variable which is bound to an attribute name. The function will also accept 
;;; numbers or variables bound to numbers; when it is called with such an argument, it returns the number.
(defmacro litval (&body z)
  `(ops-litval ',z))

;;; The function accept takes input from the user and puts it into the result element The function takes 
;;; either one or zero arguments. If it has an argument, the argument must be a symbolic atom or a variable that
;;; is bound to a symbolic atom. The following are legal calls on accept 
;;;    (accept) 
;;;    (accept infile ) 
;;;    (accept <x>) 
;;; If accept is called with no arguments, it takes its input from the current default input stream. (See Section 
;;; 5.3.6.) If it is called with an argument, accept takes its input from the file that has been associated with the 
;;; atom. (See Section 5.3.4.) 
;;; The function will read either a single atom or a list. When it reads a list it strips the parentheses from the 
;;; list and puts the atoms of the list into the result element The interpreter determines whether it is to read a list 
;;; or a single atom by inspecting the first printing character in the input If the interpreter encounters (, it 
;;; expects to read a list so it does not stop reading until it reaches ). If it encounters any other printing 
;;; character, it reads only one atom. 
;;; If accept is asked to read beyond the end of a file, it puts the atom end-of-f i 1 e in the result element 
;;; In the LISP-based interpreters, if the end of the file is reached while a list is being read, a LISP error will 
;;; occur. 
(defmacro accept (&body z)
  `(ops-accept ',z))

;;; The function accept!ine is also used to read input The difference between accept and acceptl i ne 
;;; is that the latter always reads exactiy one line of input. The function reads everything on the line, removes 
;;; any parentheses that are there, and puts the atoms into the result element 
;;; This function takes any number of arguments. If the first argument is associated with an input file (see 
;;; Section 5.3.4) acceptline takes the input from that file; otherwise, it takes the input from the current 
;;; default input stream (see Section 5.3.6). The rest of the arguments are used when a null line is read or when 
;;; acceptl i ne tries to read beyond the.end of a file. A null line is a line that contains no characters other than 
;;; 27 spaces and tabs. When accept 1 i ne encounters a null line or the end of a file, it puts its arguments into the 
;;; result element. (If the first argument is not the name of a file, it is put in the result element along with the 
;;; other arguments.) Thus when the function 
;;; (acceptline nothing read) 
;;; is evaluated, the interpreter will read the default input (assuming that not hi ng is not associated to a file) and 
;;; then put into the result element either one line of input or the two atoms nothing and read.
(defmacro acceptline (&body z)
  `(ops-acceptline ',z))

(defmacro arith (&body z)
  `(ops-arith ',z))

(defun ops-make (z)
  ($reset)
  (eval-args z)
  ($assert)) 

(defun ops-remove (z)
  (prog (old)
     (when (not *in-rhs*)
       (return (top-level-remove z)))
   top
     (and (atom z) (return nil))
     (setq old (get-ce-var-bind (car z)))
     (when (null old)
       (%warn '|remove: argument not an element variable| (car z))
       (return nil))
     (remove-from-wm old)
     (setq z (cdr z))
     (go top))) 

;;; bug:
;;; (p nnn
;;;   (stamp ^id 1)
;;;    -->
;;;    (modify 1 ^id 2))  => new literalize (^id 2)
;;;
#+nil
(defun ops-modify (z)
  (prog (old)
     (cond ((not *in-rhs*)
	          (%warn '|cannot be called at top level| 'modify)
	          (return nil)))
     (setq old (get-ce-var-bind (car z)))
     (cond ((null old)
	          (%warn '|modify: first argument must be an element variable|
		               (car z))
	          (return nil)))
     (remove-from-wm old)
     (setq z (cdr z))
     ($reset)
   copy
     (and (atom old) (go fin))
     ($change (car old))
     (setq old (cdr old))
     (go copy)
   fin
     (eval-args z)
     ($assert)))

(defun ops-modify (z)
  (prog (old)
     (cond ((not *in-rhs*)
            (%warn '|cannot be called at top level| 'modify)
            (return nil)))
     (setq old (get-ce-var-bind (car z)))
     (cond ((null old)
            (%warn '|modify: first argument must be an element variable| (car z))
            (return nil)))
     (remove-from-wm old)
     (setq z (cdr z))
     ($reset)
     (go fin)
   copy
     (and (atom old) (go fin))
     ($change (car old))
     (setq old (cdr old))
     (go copy)
   fin
     ;; @vlad-km added literalize name from remove sentence
     (push (car old) z)
     (eval-args z)
     ($assert))) 


(defun ops-bind (z)
  (prog (val)
     (cond ((not *in-rhs*)
            (%warn '|cannot be called at top level| 'bind)
            (return nil)))
     (cond ((< (length z) 1.)
            (%warn '|bind: wrong number of arguments to| z)
            (return nil))
           ((not (symbolp (car z)))
            (%warn '|bind: illegal argument| (car z))
            (return nil))
           ((= (length z) 1.) (setq val (gensym)))
           (t ($reset)
              (eval-args (cdr z))
              (setq val ($parameter 1.))))
     (make-var-bind (car z) val))) 

(defun ops-cbind (z)
  (cond ((not *in-rhs*)
       (%warn '|cannot be called at top level| 'cbind))
      ((not (= (length z) 1.))
       (%warn '|cbind: wrong number of arguments| z))
      ((not (symbolp (car z)))
       (%warn '|cbind: illegal argument| (car z)))
      ((null *last*)
       (%warn '|cbind: nothing added yet| (car z)))
      (t (make-ce-var-bind (car z) *last*)))) 


(defun ops-call (z)
  (let ((f (car z)))
    ($reset)
    (eval-args (cdr z))
    (funcall f))) 


(defun halt () 
  (cond ((not *in-rhs*)
         (%warn '|cannot be called at top level| 'halt))
        (t (setq *halt-flag* t)))) 

(defun ops-build (z)
  (prog (r)
     (cond ((not *in-rhs*)
            (%warn '|cannot be called at top level| 'build)
            (return nil)))
     ($reset)
     (build-collect z)
     (setq r (unflat (use-result-array)))
     (and *build-trace* (funcall *build-trace* r))
     (compile-production (car r) (cdr r)))) 

(defun ops-compute (z) ($value (ari z))) 

; arith is the obsolete form of compute
(defun ops-arith (z) ($value (ari z))) 

;;; Should change the division in this function to use / instead of floor
;;; todo: note: what is it?
(defun ari (x)
  (cond ((atom x)
         (%warn '|bad syntax in arithmetic expression | x)
         0.)
        ((atom (cdr x)) (ari-unit (car x)))
        ((eq (cadr x) '+)
         (+ (ari-unit (car x)) (ari (cddr x))))
        ;;"plus" changed to "+" by gdw
        ((eq (cadr x) '-)
         (- (ari-unit (car x)) (ari (cddr x))))
        ((eq (cadr x) '*)
         (* (ari-unit (car x)) (ari (cddr x))))
        ((eq (cadr x) '//)
         ;; was (floor (ari-unit (car x)) (ari (cddr x))) ;@@@ quotient? /
         ;; but changed to / by mk 10-15-92
         (/ (ari-unit (car x)) (ari (cddr x))))
  	    ((eq (cadr x) 'quotient)
         ;; for backward compatability
         (floor (ari-unit (car x)) (ari (cddr x))))
        ;;@@@ kluge only works for integers
        ;;@@@ changed to floor by jcp (from round)
        ((eq (cadr x) '\\)
         (mod (floor (ari-unit (car x))) (floor (ari (cddr x)))))
        (t (%warn '|bad syntax in arithmetic expression | x) 0.))) 

;;; todo: note: (let)
(defun ari-unit (a)
  (prog (r)
     (cond ((consp  a) (setq r (ari a))) ;dtpr\consp gdw
           (t (setq r ($varbind a))))
     (cond ((not (numberp r))
            (%warn '|bad value in arithmetic expression| a)
            (return 0.))
           (t (return r))))) 

(defun ops-substr (l)
  (prog (k elm start end)
     (cond ((not (= (length l) 3.))
            (%warn '|substr: wrong number of arguments| l)
            (return nil)))
     (setq elm (get-ce-var-bind (car l)))
     (cond ((null elm)
            (%warn '|first argument to substr must be a ce var| l)
            (return nil)))
     (setq start ($varbind (cadr l)))
     (setq start ($litbind start))
     (cond ((not (numberp start))
            (%warn '|second argument to substr must be a number| l)
            (return nil)))
     ;;###	(comment |if a variable is bound to INF, the following|
     ;;	 |will get the binding and treat it as INF is|
     ;;	 |always treated.  that may not be good|)
     (setq end ($varbind (caddr l)))
     (cond ((eq end 'inf) (setq end (length elm))))
     (setq end ($litbind end))
     (cond ((not (numberp end))
            (%warn '|third argument to substr must be a number| l)
            (return nil)))
     ;;###	(comment |this loop does not check for the end of elm|
     ;;         |instead it relies on cdr of nil being nil|
     ;;         |this may not work in all versions of lisp|)
     (setq k 1.)
   la
     (cond ((> k end) (return nil))
           ((not (< k start)) ($value (car elm))))
     (setq elm (cdr elm))
     (setq k (1+ k))
     (go la))) 

(defun genatom nil ($value (gensym))) 

(defun ops-litval (z)
  (prog (r)
     (cond ((not (= (length z) 1.))
            (%warn '|litval: wrong number of arguments| z)
            ($value 0) 
            (return nil))
           ((numberp (car z)) ($value (car z)) (return nil)))
     (setq r ($litbind ($varbind (car z))))
     (cond ((numberp r) ($value r) (return nil)))
     (%warn '|litval: argument has no literal binding| (car z))
     ($value 0)))

;;;; rhs-tab implements the tab ('^') function in the rhs.  it has
;;; four responsibilities:
;;;	- to move the array pointers
;;;	- to watch for tabbing off the left end of the array
;;;	  (ie, to watch for pointers less than 1)
;;;	- to watch for tabbing off the right end of the array
;;;	- to write nil in all the slots that are skipped
;;; the last is necessary if the result array is not to be cleared
;;; after each use; if rhs-tab did not do this, $reset
;;; would be much slower.
(defun rhs-tab (z) ($tab ($varbind z)))

(defun time-tag-print (data port)
  (when (not (null data))
    (time-tag-print (cdr data) port)
    (princ '| | port)
    (princ (creation-time (car data)) port)))

(defun init-var-mem (vlist)
  (prog (v ind r)
     (setq *variable-memory* nil)
   top
     (and (atom vlist) (return nil))
     (setq v (car vlist))
     (setq ind (cadr vlist))
     (setq vlist (cddr vlist))
     (setq r (gelm *data-matched* ind))
     (setq *variable-memory* (cons (cons v r) *variable-memory*))
     (go top))) 

(defun init-ce-var-mem (vlist)
  (prog (v ind r)
     (setq *ce-variable-memory* nil)
   top
     (and (atom vlist) (return nil))
     (setq v (car vlist))
     (setq ind (cadr vlist))
     (setq vlist (cddr vlist))
     (setq r (nth (1- ind) *data-matched*)) ; was ce-gelm
     (setq *ce-variable-memory*
	         (cons (cons v r) *ce-variable-memory*))
     (go top))) 

(defun make-ce-var-bind (var elem)
  (push (cons var elem)
	*ce-variable-memory*)) 

(defun make-var-bind (var elem)
  (push (cons var elem) 
	*variable-memory*)) 

(defun get-ce-var-bind (x)
  (if (numberp x)
      (get-num-ce x)
      (let ((r (assoc x *ce-variable-memory*)))
	      (when r 
	        (cdr r))))) 

(defun get-num-ce (x)
  (prog (r l d)
     (setq r *data-matched*)
     (setq l (length r))
     (setq d (- l x))
     (and (> 0. d) (return nil))
   la
     (cond ((null r) (return nil))
           ((> 1. d) (return (car r))))
     (setq d (1- d))
     (setq r (cdr r))
     (go la))) 

(defun build-collect (z)
  (prog (r)
   la
     (and (atom z) (return nil))
     (setq r (car z))
     (setq z (cdr z))
     (cond ((consp  r)                  ;dtpr\consp gdw
            ($value '\()
	          (build-collect r)
	          ($value '\)))
           ((eq r '\\) ($change (car z)) (setq z (cdr z)))
           (t ($value r)))
     (go la))) 

(defun unflat (x)
  (setq *rest* x)
  (unflat*)) 

(defun unflat* ()
  (if (atom *rest*)
      nil
      (let ((c (pop *rest*)))
	      (cond ((eq c '\() (cons (unflat*) (unflat*)))
              ((eq c '\)) nil)
              (t (cons c (unflat*))))))) 

;;;; $Functions.
;;;; These functions provide an interface to the result array.
;;;; The result array is used to organize attribute values into their
;;;; correct slot.

(defun $litbind (x)
  (if (symbolp x)
      (or (literal-binding-of x)
          x)
      x)) 

(defun $varbind (x)
  (if *in-rhs*
      ;; If we're in the RHS, lookup the binding. 
      (let ((binding (assoc x *variable-memory*)))
        (if binding
            (cdr binding)
            x))
      ;; Otherwise just return it unevaluated.
      x))

(defun $change (x)
  (if (consp  x)                        ;dtpr\consp gdw
      (eval-function x)	
      ($value ($varbind x)))) 

(defun $reset nil
  (setq *max-index* 0.)
  (setq *next-index* 1.)) 

(defun $tab (z)
  (prog (edge next)
     (setq next ($litbind z))
     (when (floatp next)
       (setq next (floor next)))
     (when (or (not (numberp next)) 
	             (> next *size-result-array*)
	             (> 1. next))             ; ( '| |)
       (%warn '|illegal index after ^| next)
       (return *next-index*))
     (setq edge (- next 1.))
     (cond ((> *max-index* edge) (go ok)))
   clear
     (when (== *max-index* edge) (go ok))
     (setf (aref *result-array* edge) nil)
     (decf edge)
     (go clear)
   ok
     (setq *next-index* next)
     (return next))) 

(defun $value (v)
  (cond ((> *next-index* *size-result-array*)
         (%warn '|index too large| *next-index*))
        (t (and (> *next-index* *max-index*)
                (setq *max-index* *next-index*))
           (setf (aref *result-array* *next-index*) v)
           (incf *next-index*)))) 

(defun $assert nil
  (setq *last* (use-result-array))
  (add-to-wm *last* nil))

(defun $parametercount () *max-index*)

(defun $parameter (k)
  (cond ((or (not (numberp k))
             (> k *size-result-array*) (< k 1.))
         (%warn '|illegal parameter number | k)
         nil)
        ((> k *max-index*) nil)
        (t (aref *result-array* k))))

(defun $ifile (x) 
  (when (symbolp x)
    (gethash x *inputfile-table*)))

(defun $ofile (x) 
  (when (symbolp x) 
    (gethash x *outputfile-table*)))

(defun use-result-array ()
  ;;"Use-result-array returns the contents of the result array as a list."
  ;; is *max-index* acting like a fill-pointer? Then we can't just use
  ;; coerce, unless we change *result-array* to use a fill pointer.
  ;; Also, note that index 0 of the array is ignored.
  (prog (k r)
     (setq k *max-index*)
     (setq r nil)
   top
     (and (== k 0.) (return r))
     (setq r (cons (aref *result-array* k) r))
     (decf k)
     (go top))) 

(defun eval-function (form)
  (if (not *in-rhs*)
      (%warn '|functions cannot be used at top level| (car form))
      (eval form)))

;;;; WM maintaining functions

;;; The order of operations in the following two functions is critical.
;;; add-to-wm order: (1) change wm (2) record change (3) match 
;;; remove-from-wm order: (1) record change (2) match (3) change wm
;;; (back will not restore state properly unless wm changes are recorded
;;; before the cs changes that they cause)  (match will give errors if 
;;; the thing matched is not in wm at the time)
(defun add-to-wm (wme override)
  (prog (fa z part timetag port)
     (setq *critical* t)
     (setq *current-wm* (1+ *current-wm*))
     (and (> *current-wm* *max-wm*) (setq *max-wm* *current-wm*))
     (setq *action-count* (1+ *action-count*))
     (setq fa (wm-hash wme))
     (or (member fa *wmpart-list*)
	       (setq *wmpart-list* (cons fa *wmpart-list*)))
     (setq part (gethash fa *wmpart*-table*))
     (cond (override (setq timetag override))
           (t (setq timetag *action-count*)))
     (setq z (cons wme timetag))
     (setf (gethash fa *wmpart*-table*) (cons z part))
     (record-change '=>wm *action-count* wme)
     (match 'new wme)
     (setq *critical* nil)
     (cond ((and *in-rhs* *wtrace*)
            (setq port (trace-file))
            (terpri port)
            (princ '|=>wm: | port)
            (ppelm wme port))))) 

;;; remove-from-wm uses eq, not equal to determine if wme is present
(defun remove-from-wm (wme)
  (prog (fa z part timetag port)
     (setq fa (wm-hash wme))
     (setq part (gethash fa *wmpart*-table*))
     (setq z (assoc wme part))
     (or z (return nil))
     (setq timetag (cdr z))
     (cond ((and *wtrace* *in-rhs*)
            (setq port (trace-file))
            (terpri port)
            (princ '|<=wm: | port)
            (ppelm wme port)))
     (setq *action-count* (1+ *action-count*))
     (setq *critical* t)
     (setq *current-wm* (1- *current-wm*))
     (record-change '<=wm timetag wme)
     (match nil wme)
     ;; @vlad-km - :test #'equal not #'eq
     (setf (gethash fa *wmpart*-table*) (delete z part :test #'equal))
     (setq *critical* nil))) 

;;; mapwm maps down the elements of wm, applying fn to each element
;;; each element is of form (datum . creation-time)
(defun mapwm (fn)
  (dolist (wmpl *wmpart-list*)
    (mapc fn (gethash wmpl *wmpart*-table*))))

(defun ops-wm (a) 
  (mapc #'(lambda (z) (terpri) (ppelm z *standard-output*)) 
	      (get-wm a))
  nil) 

(defun creation-time (wme)
  (cdr (assoc wme (gethash (wm-hash wme) *wmpart*-table*)))) 

;;; @vlad-km note: check member
(defun get-wm (z)
  (setq *wm-filter* z)
  (setq *wm* nil)
  (mapwm #'(lambda (elem) 
             (when (or (null *wm-filter*)
                     (member (cdr elem) *wm-filter*)) ;test #'equal
               (push (car elem) *wm*))))
  (prog2 nil *wm* (setq *wm* nil))) 

(defun wm-hash (x)
  (cond ((not x) '<default>)
        ((not (car x)) (wm-hash (cdr x)))
        ((symbolp (car x)) (car x))
        (t (wm-hash (cdr x))))) 

;;; @vlad-km note: Where is used?
(defun refresh ()
  (setq *old-wm* nil)
  (mapwm #'refresh-collect)
  (mapc #'refresh-del *old-wm*)
  (mapc #'refresh-add *old-wm*)
  (setq *old-wm* nil)) 

(defun refresh-collect (x) (push x *old-wm*)) 

(defun refresh-del (x) (remove-from-wm (car x))) 

(defun refresh-add (x) (add-to-wm (car x) (cdr x))) 

#+ops5
(in-package :cl-user)

;;; *EOF*
