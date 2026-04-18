#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Spring 2026

 Homework 7.
 Due: 4/18 (Midnight)

 For this assignment, work in groups of 1-3. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 7".

 The group members are:

Reilly Teeter
 
 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/. 

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit) 

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or 
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing 

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include
 
 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham
 
|#
;AI use: Claude helped write a lot of the tests, and generate and debug a fair amount of the code

(in-package "ACL2S")

(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

:q

#| 

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code. 

 Here are some examples you can try. 

 acl2s-compute is the form you use when you are using ACL2s to compute
 something, e.g., running a function on some input. 

 (acl2s-compute '(+ 1 2))

 acl2s-query is the form you use when you are querying ACL2s, e.g., a
 property without a name. If the property has a name, then that is not
 a query, but an event and you have to use acl2s-event.

 (acl2s-query 'acl2s::(property (p q :all)
                        (iff (=> p q)
                             (v (! p) q))))

 acl2s-arity is a function that determines if f is a function defined
 in ACL2s and if so, its arity (number of arguments). If f is not a
 function, then the arity is nil. Otherwise, the arity is a natural
 number. Note that f can't be a macro.

 (acl2s-arity 'acl2s::app)     ; is nil since app is a macro
 (acl2s-arity 'acl2s::bin-app) ; is 2

|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

(import 'acl2s::(acl2s-compute acl2s-query))
(import 'acl2s-interface-extras::(acl2s-arity))


#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t  )
    (not     :arity 1 :identity -   :idem nil :sink -  )
    (implies :arity 2 :identity -   :idem nil :sink -  )
    (iff     :arity - :identity t   :idem nil :sink -  )
    (if      :arity 3 :identity -   :idem nil :sink -  )))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))
(defparameter *fo-quantifiers* '(forall exists))
(defparameter *booleans* '(t nil))
(defparameter *fo-keywords*
  (append *p-funs* *booleans* *fo-quantifiers*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defun booleanp (x)
  (in x *booleans*))

(defun no-dupsp (l)
  (or (endp l)
      (and (not (in (car l) (cdr l)))
           (no-dupsp (cdr l)))))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))


#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun to-acl2s (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2S"))
    ((list 'iff) t)
    ((list 'iff p) (to-acl2s p))
    ((list* 'iff args)
     (acl2s::xxxjoin 'acl2s::iff
                     (mapcar #'to-acl2s args)))
    ((cons x xs)
     (mapcar #'to-acl2s f))
    (_ f)))

#|

 A FO term is either a 

 constant symbol: a symbol whose name starts with "C" and is
 optionally followed by a natural number with no leading 0's, e.g., c0,
 c1, c101, c, etc are constant symbols, but c00, c0101, c01, etc are
 not. Notice that (gentemp "C") will create a new constant. Notice
 that symbol names  are case insensitive, so C1 is the same as c1.

 quoted constant: anything of the form (quote object) for any object

 constant object: a rational, boolean, string, character or keyword

 variable: a symbol whose name starts with "X", "Y", "Z", "W", "U" or
 "V" and is optionally followed by a natural number with no leading
 0's (see constant symbol). Notice that (gentemp "X") etc will create
 a new variable.

 function application: (f t1 ... tn), where f is a
 non-constant/non-variable/non-boolean/non-keyword symbol. The arity
 of f is n and every occurrence of (f ...)  in a term or formula has
 to have arity n. Also, if f is a defined function in ACL2s, its arity
 has to match what ACL2s expects. We allow functions of 0-arity.
 
|#

(defun char-nat-symbolp (s chars)
  (and (symbolp s)
       (let ((name (symbol-name s)))
         (and (<= 1 (len name))
              (in (char name 0) chars)
              (or (== 1 (len name))
                  (let ((i (parse-integer name :start 1 :junk-allowed t)))
                    (and (integerp i)
                         (<= 0 i)
                         (string= (format nil "~a~a" (char name 0) i)
                                  name))))))))

(defun constant-symbolp (s)
  (char-nat-symbolp s '(#\C)))

(defun variable-symbolp (s)
  (char-nat-symbolp s '(#\X #\Y #\Z #\W #\U #\V)))

(defun quotep (c)
  (and (consp c)
       (== (car c) 'quote)))

(defun constant-objectp (c)
  (typep c '(or boolean rational simple-string standard-char keyword)))

#|

Examples

(constant-objectp #\a)
(constant-objectp 0)
(constant-objectp 1/221)
(constant-objectp "hi there")
(constant-objectp t)
(constant-objectp nil)
(constant-objectp :hi)
(constant-objectp 'a)

(quotep '1)  ; recall that '1 is evaluated first
(quotep ''1) ; but this works
(quotep '(1 2 3))  ; similar to above
(quotep ''(1 2 3)) ; similar to above
(quotep (list 'quote (list 1 2 3))) ; verbose version of previous line

|#

(defun function-symbolp (f)
  (and (symbolp f)
       (not (in f *fo-keywords*))
       (not (keywordp f))
       (not (constant-symbolp f))
       (not (variable-symbolp f))))

#|

(function-symbolp 'c)
(function-symbolp 'c0)
(function-symbolp 'c00)
(function-symbolp 'append)
(function-symbolp '+)

|#

(defmacro mv-and (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a ,b (values nil ,fsig ,rsig)))

(defmacro mv-or (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a (values t ,fsig ,rsig) ,b))

(defun fo-termp (term &optional (fsig nil) (rsig nil))
  (match term
    ((satisfies constant-symbolp) (values t fsig rsig))
    ((satisfies variable-symbolp) (values t fsig rsig))
    ((satisfies quotep) (values t fsig rsig))
    ((satisfies constant-objectp) (values t fsig rsig))
    ((list* f args)
     (mv-and 
      (and (function-symbolp f) (not (get-alist f rsig)))
      (let* ((fsig-arity (get-alist f fsig))
             (acl2s-arity
              (or fsig-arity
                  (acl2s-arity (to-acl2s f))))
             (arity (or acl2s-arity (len args)))
             (fsig (if fsig-arity fsig (acons f arity fsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

(defun fo-termsp (terms fsig rsig)
  (mv-or (endp terms)
         (let+ (((&values res fsig rsig)
                 (fo-termp (car terms) fsig rsig)))
           (mv-and res
                   (fo-termsp (cdr terms) fsig rsig)))))

#|

Examples

(fo-termp '(f d 2))
(fo-termp '(f c 2))
(fo-termp '(f c0 2))
(fo-termp '(f c00 2))
(fo-termp '(f '1 '2))
(fo-termp '(f (f '1 '2)
              (f v1 c1 '2)))


(fo-termp '(binary-append '1 '2))
(fo-termp '(binary-append '1 '2 '3))
(fo-termp '(binary-+ '1 '2))
(fo-termp '(+ '1 '2)) 
(fo-termp '(- '1 '2))

|#

#|

 A FO atomic formula is either an 

 atomic equality: (= t1 t2), where t1, t2 are FO terms.

 atomic relation: (P t1 ... tn), where P is a
 non-constant/non-variable symbol. The arity of P is n and every
 occurrence of (P ...) has to have arity n. Also, if P is a defined
 function in ACL2s, its arity has to match what ACL2s expects.  We do
 not check that if P is a defined function then it has to return a
 Boolean. Make sure that you do not use such examples.

|#

(defun relation-symbolp (f)
  (function-symbolp f))

#|

Examples

(relation-symbolp '<)
(relation-symbolp '<=)
(relation-symbolp 'binary-+)

|#

(defun fo-atomic-formulap (f &optional (fsig nil) (rsig nil))
  (match f
    ((list '= t1 t2)
     (fo-termsp (list t1 t2) fsig rsig))
    ((list* r args)
     (mv-and 
      (and (relation-symbolp r) (not (get-alist r fsig)))
      (let* ((rsig-arity (get-alist r rsig))
             (acl2s-arity
              (or rsig-arity
                  (acl2s::acl2s-arity (to-acl2s r))))
             (arity (or acl2s-arity (len args)))
             (rsig (if rsig-arity rsig (acons r arity rsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a propositional formula. We allow
 Booleans.
 
|#

(defun pfun-fo-argsp (pop args fsig rsig)
  (mv-and (p-funp pop)
          (let ((arity (get-key :arity (get-alist pop *p-ops*))))
            (mv-and (or (== arity '-)
                        (== (len args) arity))
                    (fo-formulasp args fsig rsig)))))

(defun p-fo-formulap (f fsig rsig)
  (match f
    ((type boolean) (values t fsig rsig))
    ((list* pop args)
     (if (p-funp pop)
         (pfun-fo-argsp pop args fsig rsig)
       (values nil fsig rsig)))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a quantified formula. 

 The quantified variables can be a variable 
 or a non-empty list of variables with no duplicates.
 Examples include

 (exists w (P w y z x))
 (exists (w) (P w y z x))
 (forall (x y z) (exists w (P w y z x)))

 But this does not work

 (exists c (P w y z x))
 (forall () (exists w (P w y z x)))
 (forall (x y z x) (exists w (P w y z x)))

|#

(defun quant-fo-formulap (f fsig rsig)
  (match f
    ((list q vars body)
     (mv-and (and (in q *fo-quantifiers*)
                  (or (variable-symbolp vars)
                      (and (consp vars)
                           (no-dupsp vars)
                           (every #'variable-symbolp vars))))
             (fo-formulap body fsig rsig)))
    (_ (values nil fsig rsig))))

(defun mv-seq-first-fun (l)
  (if (endp (cdr l))
      (car l)
    (let ((res (gensym))
          (f (gensym))
          (r (gensym)))
      `(multiple-value-bind (,res ,f ,r)
           ,(car l)
         (if ,res
             (values t ,f ,r)
           ,(mv-seq-first-fun (cdr l)))))))

(defmacro mv-seq-first (&rest rst)
  (mv-seq-first-fun rst))
  
(defun fo-formulap (f &optional (fsig nil) (rsig nil))
  (mv-seq-first
   (fo-atomic-formulap f fsig rsig)
   (p-fo-formulap f fsig rsig)
   (quant-fo-formulap f fsig rsig)
   (values nil fsig rsig)))

(defun fo-formulasp (fs fsig rsig)
  (mv-or (endp fs)
         (let+ (((&values res fsig rsig)
                 (fo-formulap (car fs) fsig rsig)))
           (mv-and res
                   (fo-formulasp (cdr fs) fsig rsig)))))

#|

 We can use fo-formulasp to find the function and relation
 symbols in a formula as follows.
 
|#

(defun fo-f-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car fsig)))

(defun fo-r-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car rsig)))

#|

Examples

(fo-formulap 
 '(forall (x y z) (exists w (P w y z x))))

(fo-formulap 
 '(forall (x y z x) (exists w (P w y z x))))

(quant-fo-formulap 
 '(forall (x y z) (exists y (P w y z x))) nil nil)

(fo-formulap
 '(exists w (P w y z x)))

(fo-atomic-formulap
 '(exists w (P w y z x)) nil nil)

(quant-fo-formulap 
 '(exists w (P w y z x)) nil nil)

(fo-formulap 
 '(P w y z x))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (p1 x1 w) (q c1) (r c2)))
                     (p '2 y w))))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q2 z) (r2 z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall x1 (iff (p1 x1 w) (q c1) (r c2))))

(fo-formulap
 '(iff (p1 x1 w) (q c1) (r c2)))

(fo-atomic-formulap
 '(p1 x1 w))

(variable-symbolp 'c1)
(fo-termp 'x1)
(fo-termp 'w1)
(fo-termp '(x1 w) nil nil)
(fo-termsp '(x1 w) nil nil)

|#

#|
 
 Where appropriate, for the problems below, modify your solutions from
 homework 4. For example, you already implemented most of the
 simplifications in Question 1 in homework 4.
 
|#


#|
 
 Question 1. (25 pts)

 Define function fo-simplify that given a first-order (FO) formula
 returns an equivalent FO formula with the following properties.

 A. The returned formula is either a constant or does not include any
 constants. For example:

 (and (p x) t (q t y) (q y z)) should be simplified to 
 (and (p x) (q t y) (q y z)) 

 (and (p x) t (q t b) nil) should be simplified to nil

 B. Expressions are flattened, e.g.:

 (and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) is not flat, but this is
 (and (p c) (= c '1) (r) (s) (or (r1) (r2)))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t.

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain (where f is a formula)
 
 (not (not f))

 E. Simplify formulas so that no subexpressions of the following form
 remain 

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or (f) (f1) (p a b) (not (p a b)) (= w z)) should be simplified to 

 t 
 
 F. Simplify formulas so there are no vacuous quantified formulas.
 For example, 

 (forall (x w) (P y z))  should be simplified to
 
 (P y z)

 and 

 (forall (x w) (P x y z))  should be simplified to
 
 (forall (x) (P x y z)) 

 G. Simplify formulas by using ACL2s to evaluate, when possible, terms
 of the form (f ...) where f is an ACL2s function all of whose
 arguments are either constant-objects or quoted objects.

 For example,

 (P (binary-+ 4 2) 3)

 should be simplified to

 (P 6 3)

 Hint: use acl2s-compute and to-acl2s. For example, consider

 (acl2s-compute (to-acl2s '(binary-+ 4 2)))

 On the other hand,

 (P (binary-+ 'a 2) 3)

 does not get simplified because 
 
 (acl2s-compute (to-acl2s '(binary-+ 'a 2)))

 indicates an error (contract/guard violation). See the definition of
 acl2s-compute to see how to determine if an error occurred.

 H. Test your definitions using at least 10 interesting formulas.  Use
 the acl2s code, if you find it useful.  Include deeply nested
 formulas, all of the Boolean operators, quantified formulas, etc.

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast. 

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. 

|#

(defun free-vars-term (term bound)
  (cond
    ((variable-symbolp term)
     (if (in term bound) nil (list term)))
    ((quotep term) nil)
    ((constant-symbolp term) nil)
    ((constant-objectp term) nil)
    ((consp term)
     (let ((args (cdr term)))
       (mapcan (lambda (a) (free-vars-term a bound)) args)))
    (t nil)))

(defun free-vars (f &optional (bound nil))
  (match f
    ((type boolean) nil)
    ((satisfies constant-symbolp) nil)
    ((satisfies variable-symbolp)
     (if (in f bound) nil (list f)))
    ((satisfies quotep) nil)
    ((satisfies constant-objectp) nil)
    ((list* 'forall rest)
     (let* ((vars  (if (listp (car rest)) (car rest) (list (car rest))))
            (body  (cadr rest))
            (new-bound (append vars bound)))
       (free-vars body new-bound)))
    ((list* 'exists rest)
     (let* ((vars  (if (listp (car rest)) (car rest) (list (car rest))))
            (body  (cadr rest))
            (new-bound (append vars bound)))
       (free-vars body new-bound)))
    ((list* _op args)
     (remove-dups (mapcan (lambda (a) (free-vars a bound)) args)))
    (_ nil)))

(defun ground-term-p (term)
  (cond
    ((variable-symbolp term) nil)
    ((constant-symbolp term) nil)
    ((quotep term) t)
    ((constant-objectp term) t)
    ((consp term)
     (every #'ground-term-p (cdr term)))
    (t nil)))

(defun call-acl2s-compute (expr)
  (let* ((ret (acl2s-compute expr))
         (erp (car ret))
         (val (cadr ret)))
    (values val (null erp))))

(defun try-eval-term (term)
  (if (and (consp term)
           (function-symbolp (car term))
           (acl2s-arity (to-acl2s (car term)))
           (every #'ground-term-p (cdr term)))
      (multiple-value-bind (result okp)
          (call-acl2s-compute (to-acl2s term))
        (if okp result term))
    term))

(defun simplify-terms (args)
  (mapcar (lambda (a)
            (if (and (consp a)
                     (function-symbolp (car a))
                     (acl2s-arity (to-acl2s (car a)))
                     (every #'ground-term-p (cdr a)))
                (multiple-value-bind (result okp)
                    (call-acl2s-compute (to-acl2s a))
                  (if okp result a))
              a))
          args))

(defun flatten-op (op args)
  (mapcan (lambda (a)
            (if (and (consp a) (== (car a) op))
                (cdr a)
              (list a)))
          args))

(defun op-identity (op)
  (get-key :identity (get-alist op *p-ops*)))

(defun op-sink (op)
  (get-key :sink (get-alist op *p-ops*)))

(defun remove-identity (op args)
  (let ((id (op-identity op)))
    (if (booleanp id)
        (remove id args :test #'equal)
      args)))

(defun check-sink (op args)
  (let ((sink (op-sink op)))
    (if (and (booleanp sink) (in sink args))
        (values t sink)
      (values nil nil))))

(defun simplify-not (arg)
  (match arg
    ((list 'not inner) inner)
    ((type boolean)    (not arg))
    (_                 (list 'not arg))))

(defun complement-of (p q)
  (or (== p (list 'not q))
      (== q (list 'not p))))

(defun remove-dups-and-complements (op args)
  (let ((deduped (remove-duplicates args :test #'equal)))
    (block found
      (loop for x in deduped do
        (loop for y in deduped do
          (when (and (not (eq x y)) (complement-of x y))
            (cond
              ((== op 'or)  (return-from found :sink-t))
              ((== op 'and) (return-from found :sink-nil))
              ((== op 'iff) (return-from found :sink-nil))
              (t            (return-from found :sink-nil))))))
      deduped)))

(defun collapse-unary (op args)
  (cond
    ((null args)        (op-identity op))
    ((null (cdr args))  (car args))
    (t                  (cons op args))))

(defun simplify-implies (p q)
  (cond
    ((== p nil) t)
    ((== p t)   q)
    ((== q t)   t)
    ((== q nil) (simplify-not p))
    ((== p q)   t)
    (t          (list 'implies p q))))

(defun simplify-if (test then else)
  (cond
    ((== test t)   then)
    ((== test nil) else)
    ((== then else) then)
    (t (list 'if test then else))))

(defun normalize-vars (vars)
  (if (listp vars) vars (list vars)))

(defun simplify-quant (quant vars body)
  (let* ((varlist  (normalize-vars vars))
         (fv       (free-vars body))
         (used     (remove-if-not (lambda (v) (in v fv)) varlist))
         (used     (remove-duplicates used :test #'equal)))
    (cond
      ((null used)   body)
      ((null (cdr used))
       (list quant (car used) body))
      (t
       (list quant used body)))))

(defun simplify-atom (f args)
  (let* ((args (simplify-terms args))
         (expr (cons f args)))
    (if (and (function-symbolp f)
             (acl2s-arity (to-acl2s f))
             (every #'ground-term-p args))
        (try-eval-term expr)
      expr)))

(defun fo-simplify (f)
  (cond
    ((booleanp f)            f)
    ((constant-symbolp f)    f)
    ((variable-symbolp f)    f)
    ((quotep f)              f)
    ((constant-objectp f)    f)
    ((atom f)                f)

    ((and (consp f)
          (p-funp (car f))
          (eq (get-key :arity (get-alist (car f) *p-ops*)) '-))
     (let* ((op     (car f))
            (args   (cdr f))
            (sargs  (mapcar #'fo-simplify args))
            (flat   (flatten-op op sargs))
            (no-id  (remove-identity op flat)))
       (multiple-value-bind (foundsink sink) (check-sink op no-id)
         (if foundsink
             sink
           (let ((cleaned (remove-dups-and-complements op no-id)))
             (cond
               ((eq cleaned :sink-t)   t)
               ((eq cleaned :sink-nil) nil)
               (t (collapse-unary op cleaned))))))))

    ((and (consp f) (== (car f) 'not) (== (length f) 2))
     (simplify-not (fo-simplify (cadr f))))

    ((and (consp f) (== (car f) 'implies) (== (length f) 3))
     (simplify-implies (fo-simplify (cadr f)) (fo-simplify (caddr f))))

    ((and (consp f) (== (car f) 'if) (== (length f) 4))
     (simplify-if (fo-simplify (cadr f))
                  (fo-simplify (caddr f))
                  (fo-simplify (cadddr f))))

    ((and (consp f) (in (car f) *fo-quantifiers*) (== (length f) 3))
     (simplify-quant (car f) (cadr f) (fo-simplify (caddr f))))

    ((consp f)
     (simplify-atom (car f) (mapcar #'fo-simplify (cdr f))))

    (t f)))


(defun run-tests ()
  (let ((pass 0) (fail 0))
    (flet ((check (label input expected)
             (let ((result (fo-simplify input)))
               (if (equal result expected)
                   (progn (incf pass)
                          (format t "PASS ~a~%" label))
                   (progn (incf fail)
                          (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                                  label input expected result))))))

      (check "T1: and-identity"
             '(and (p x) t (q t y) (q y z))
             '(and (p x) (q t y) (q y z)))

      (check "T2: and-sink"
             '(and (p x) t (q t b) nil)
             nil)

      (check "T3: and-flatten"
             '(and (p c) (= c '1) (and (r) (s) (or (r1) (r2))))
             '(and (p c) (= c '1) (r) (s) (or (r1) (r2))))

      (check "T4: not-not"
             '(not (not (p x)))
             '(p x))

      (check "T5: or-complement"
             '(or (f) (f1) (p a b) (not (p a b)) (= w z))
             t)

      (check "T6: vacuous-forall"
             '(forall (x w) (p y z))
             '(p y z))

      (check "T7: partial-quant"
             '(forall (x w) (p x y z))
             '(forall x (p x y z)))

      (check "T8: ground-eval"
             '(p (binary-+ 4 2) 3)
             '(p 6 3))

      (check "T9: non-ground-stays"
             '(p (binary-+ 'a 2) 3)
             '(p (binary-+ 'a 2) 3))

      (check "T10: nested-quant"
             '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
                   (exists w (implies (forall x1
                                              (iff (= (p1 x1 w) c2)
                                                   (q c1)
                                                   (r c2)))
                                      (p '2 y w))))
             '(and (forall (x y z) (or (not (= (q z) (r z))) (p '1 x y)))
                   (exists w (implies (forall x1
                                              (iff (= (p1 x1 w) c2)
                                                   (q c1)
                                                   (r c2)))
                                      (p '2 y w)))))

      (check "T11: empty-or"
             '(or)
             nil)

      (check "T12: empty-and"
             '(and)
             t)

      (check "T13: unary-and"
             '(and (p x))
             '(p x))

      (check "T14: implies-nil-ante"
             '(implies nil (p x))
             t)

      (check "T15: implies-t-ante"
             '(implies t (p x))
             '(p x))

      (check "T16: if-const-test"
             '(if t (p x) (q y))
             '(p x))

      (check "T17: and-dedup"
             '(and (p x) (p x) (q y))
             '(and (p x) (q y)))

      (check "T18: iff-complement"
             '(iff (p x) (not (p x)))
             nil)

      (check "T19: deep-double-not"
             '(and (not (not (p x))) (or (q y) nil))
             '(and (p x) (q y)))

      (check "T20: iff-flatten-identity"
             '(iff t (p x) (iff (q y) (r z)))
             '(iff (p x) (q y) (r z))))

    (format t "~%Results: ~a passed, ~a failed~%" pass fail)))

(run-tests)

#|

 Question 2. (10 pts)

 Define nnf, a function that given a FO formula, something that
 satisfies fo-formulap, puts it into negation normal form (NNF).

 The resulting formula cannot contain any of the following
 propositional connectives: implies, iff, if.

 Test nnf using at least 10 interesting formulas. Make sure you
 support quantification.

|#

(defun nnf-pairwise-iff (args)
  (if (null (cdr args))
      t
    (let ((conjuncts
           (loop for (a b) on args
                 while b
                 collect (list 'and
                               (list 'or (nnf-neg a) (nnf b))
                               (list 'or (nnf-neg b) (nnf a))))))
      (if (null (cdr conjuncts))
          (car conjuncts)
        (cons 'and conjuncts)))))

(defun nnf-neg-pairwise-iff (args)
  (if (null (cdr args))
      nil
    (let ((disjuncts
           (loop for (a b) on args
                 while b
                 collect (list 'or
                               (list 'and (nnf a) (nnf-neg b))
                               (list 'and (nnf b) (nnf-neg a))))))
      (if (null (cdr disjuncts))
          (car disjuncts)
        (cons 'or disjuncts)))))

(defun nnf-normalize-vars (vars)
  (if (listp vars) vars (list vars)))

(defun nnf (f)
  (cond
    ((booleanp f) f)
    ((or (variable-symbolp f) (constant-symbolp f)
         (constant-objectp f) (quotep f))
     f)
    ((and (consp f) (== (car f) 'not))
     (nnf-neg (cadr f)))
    ((and (consp f) (== (car f) 'and))
     (let ((args (mapcar #'nnf (cdr f))))
       (if (null args) t
         (if (null (cdr args)) (car args)
           (cons 'and args)))))
    ((and (consp f) (== (car f) 'or))
     (let ((args (mapcar #'nnf (cdr f))))
       (if (null args) nil
         (if (null (cdr args)) (car args)
           (cons 'or args)))))
    ((and (consp f) (== (car f) 'implies))
     (list 'or (nnf-neg (cadr f)) (nnf (caddr f))))
    ((and (consp f) (== (car f) 'iff))
     (nnf-pairwise-iff (cdr f)))
    ((and (consp f) (== (car f) 'if))
     (let ((test (cadr f)) (then (caddr f)) (els (cadddr f)))
       (list 'and
             (list 'or (nnf-neg test) (nnf then))
             (list 'or (nnf test)     (nnf els)))))
    ((and (consp f) (in (car f) *fo-quantifiers*))
     (let* ((quant (car f))
            (vars  (nnf-normalize-vars (cadr f)))
            (body  (nnf (caddr f))))
       (list quant vars body)))
    (t f)))

(defun nnf-neg (f)
  (cond
    ((booleanp f) (not f))
    ((and (consp f) (== (car f) 'not))
     (nnf (cadr f)))
    ((and (consp f) (== (car f) 'and))
     (let ((args (mapcar #'nnf-neg (cdr f))))
       (if (null args) nil
         (if (null (cdr args)) (car args)
           (cons 'or args)))))
    ((and (consp f) (== (car f) 'or))
     (let ((args (mapcar #'nnf-neg (cdr f))))
       (if (null args) t
         (if (null (cdr args)) (car args)
           (cons 'and args)))))
    ((and (consp f) (== (car f) 'implies))
     (list 'and (nnf (cadr f)) (nnf-neg (caddr f))))
    ((and (consp f) (== (car f) 'iff))
     (nnf-neg-pairwise-iff (cdr f)))
    ((and (consp f) (== (car f) 'if))
     (let ((test (cadr f)) (then (caddr f)) (els (cadddr f)))
       (list 'and
             (list 'or (nnf-neg test) (nnf-neg then))
             (list 'or (nnf test)     (nnf-neg els)))))
    ((and (consp f) (== (car f) 'forall))
     (let ((vars (nnf-normalize-vars (cadr f)))
           (body (nnf-neg (caddr f))))
       (list 'exists vars body)))
    ((and (consp f) (== (car f) 'exists))
     (let ((vars (nnf-normalize-vars (cadr f)))
           (body (nnf-neg (caddr f))))
       (list 'forall vars body)))
    (t (list 'not f))))

(defun nnf-p (f)
  (cond
    ((booleanp f) t)
    ((atom f) t)
    ((== (car f) 'not)
     (let ((arg (cadr f)))
       (and (consp arg)
            (not (in (car arg) (list 'not 'and 'or 'implies 'iff 'if
                                     'forall 'exists))))))
    ((in (car f) '(implies iff if)) nil)
    ((in (car f) '(and or forall exists))
     (every #'nnf-p (if (in (car f) '(forall exists))
                        (list (caddr f))
                      (cdr f))))
    (t t)))

(defun run-nnf-tests ()
  (let ((pass 0) (fail 0))
    (flet ((check (label input expected)
             (let ((result (nnf input)))
               (if (equal result expected)
                   (progn (incf pass) (format t "PASS ~a~%" label))
                   (progn (incf fail)
                          (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                                  label input expected result)))))
           (check-nnf-p (label input)
             (let ((result (nnf input)))
               (if (nnf-p result)
                   (progn (incf pass) (format t "PASS ~a (nnf-p check)~%" label))
                   (progn (incf fail)
                          (format t "FAIL ~a (nnf-p): ~s~%" label result))))))

      (check "N1: atom" '(p x y) '(p x y))

      (check "N2: double-neg" '(not (not (p x))) '(p x))

      (check "N3: not-and"
             '(not (and (p x) (q y)))
             '(or (not (p x)) (not (q y))))

      (check "N4: not-or"
             '(not (or (p x) (q y)))
             '(and (not (p x)) (not (q y))))

      (check "N5: implies"
             '(implies (p x) (q y))
             '(or (not (p x)) (q y)))

      (check "N6: not-implies"
             '(not (implies (p x) (q y)))
             '(and (p x) (not (q y))))

      (check "N7: iff-two"
             '(iff (p x) (q y))
             '(and (or (not (p x)) (q y))
                   (or (not (q y)) (p x))))

      (check "N8: if"
             '(if (p x) (q y) (r z))
             '(and (or (not (p x)) (q y))
                   (or (p x) (r z))))

      (check "N9: not-forall"
             '(not (forall (x y) (p x y)))
             '(exists (x y) (not (p x y))))

      (check "N10: not-exists"
             '(not (exists x (p x)))
             '(forall (x) (not (p x))))

      (check "N11: forall-implies"
             '(forall (x y) (implies (p x) (q y)))
             '(forall (x y) (or (not (p x)) (q y))))

      (check "N12: exists-iff"
             '(exists x (iff (p x) (q x)))
             '(exists (x) (and (or (not (p x)) (q x))
                               (or (not (q x)) (p x)))))

      (check "N13: not-nested"
             '(not (and (p x) (or (q y) (r z))))
             '(or (not (p x)) (and (not (q y)) (not (r z)))))

      (check-nnf-p "N14: nnf-p complex"
                   '(and (forall (x y z) (or (not (= (q z) (r z))) (p x y)))
                         (exists w (implies (p w) (q w)))))

      (check "N15: booleans"
             '(and (implies t (p x)) (not nil))
             '(and (or nil (p x)) t)))

    (format t "~%NNF Results: ~a passed, ~a failed~%" pass fail)))

(run-nnf-tests)

#|

 Question 3. (25 pts)

 Define simp-skolem-pnf-cnf, a function that given a FO formula,
 simplifies it using fo-simplify, then puts it into negation normal
 form, applies skolemization, then puts the formula in prenex normal
 form and finally transforms the matrix into an equivalent CNF
 formula.

 To be clear: The formula returned should be equi-satisfiable with the
 input formula, should contain no existential quantifiers, and if it
 has quantifiers it should be of the form

 (forall (...) matrix)

 where matrix is quantifier-free and in CNF. 

 The fewer quantified variables, the better.
 The fewer Skolem functions, the better.
 The smaller the arity of Skolem functions, the better.
 Having said that, correctness should be your primary consideration.

 Test your functions using at least 10 interesting formulas. 
 
|#

(defun skolem-term (var universal-vars body)
  (let* ((fv      (free-vars body))
         (relevant (remove-if-not (lambda (v) (in v fv)) universal-vars))
         (skolem-name (gentemp "SK")))
    (if (null relevant)
        skolem-name
      (cons skolem-name relevant))))
 
(defun subst-var (var replacement f)
  (cond
    ((== f var) replacement)
    ((atom f) f)
    ((and (consp f) (in (car f) *fo-quantifiers*))
     (let* ((quant (car f))
            (vars  (nnf-normalize-vars (cadr f)))
            (body  (caddr f)))
       (if (in var vars)
           f
         (list quant vars (subst-var var replacement body)))))
    ((consp f)
     (mapcar (lambda (x) (subst-var var replacement x)) f))
    (t f)))
 
(defun skolemize (f &optional (uvars nil))
  (cond
    ((atom f) f)
    ((== (car f) 'forall)
     (let* ((vars (nnf-normalize-vars (cadr f)))
            (body (skolemize (caddr f) (append uvars vars))))
       (list 'forall vars body)))
    ((== (car f) 'exists)
     (let* ((vars (nnf-normalize-vars (cadr f)))
            (body (caddr f))
            (new-body
             (reduce (lambda (b evar)
                       (let ((sk (skolem-term evar uvars b)))
                         (subst-var evar sk b)))
                     vars
                     :initial-value body)))
       (skolemize new-body uvars)))
    ((in (car f) '(and or not))
     (cons (car f) (mapcar (lambda (a) (skolemize a uvars)) (cdr f))))
    (t f)))
 
(defvar *var-counter* 0)
 
(defun fresh-var ()
  (incf *var-counter*)
  (intern (format nil "X~a" *var-counter*)))
 
(defun rename-bound (f &optional (subst nil))
  (cond
    ((atom f)
     (let ((rep (assoc f subst :test #'equal)))
       (if rep (cdr rep) f)))
    ((in (car f) *fo-quantifiers*)
     (let* ((quant (car f))
            (vars  (nnf-normalize-vars (cadr f)))
            (fresh (mapcar (lambda (v) (declare (ignore v)) (fresh-var)) vars))
            (new-subst (append (mapcar #'cons vars fresh) subst))
            (body  (rename-bound (caddr f) new-subst)))
       (list quant fresh body)))
    (t (mapcar (lambda (x) (rename-bound x subst)) f))))
 
(defun pull-quantifiers (f)
  (cond
    ((atom f) (values nil f))
    ((== (car f) 'forall)
     (let* ((vars (nnf-normalize-vars (cadr f))))
       (multiple-value-bind (inner-vars matrix)
           (pull-quantifiers (caddr f))
         (values (append vars inner-vars) matrix))))
    ((== (car f) 'and)
     (let ((all-vars nil)
           (matrices nil))
       (dolist (arg (cdr f))
         (multiple-value-bind (vs mat) (pull-quantifiers arg)
           (setf all-vars (append all-vars vs))
           (push mat matrices)))
       (values all-vars (cons 'and (nreverse matrices)))))
    ((== (car f) 'or)
     (let ((all-vars nil)
           (matrices nil))
       (dolist (arg (cdr f))
         (multiple-value-bind (vs mat) (pull-quantifiers arg)
           (setf all-vars (append all-vars vs))
           (push mat matrices)))
       (values all-vars (cons 'or (nreverse matrices)))))
    (t (values nil f))))
 
(defun make-pnf (f)
  (let ((f (rename-bound f)))
    (multiple-value-bind (vars matrix) (pull-quantifiers f)
      (let ((vars (remove-duplicates vars :test #'equal)))
        (if (null vars)
            matrix
          (list 'forall vars matrix))))))
 
(defun cnf-matrix (f)
  (cnf-render (cnf-clauses f)))
 
(defun cnf-clauses (f)
  (cond
    ((atom f) (list (list f)))
    ((and (== (car f) 'not) (atom (cadr f)))
     (list (list f)))
    ((and (== (car f) 'not) (consp (cadr f)))
     (list (list f)))
    ((== (car f) 'and)
     (mapcan #'cnf-clauses (cdr f)))
    ((== (car f) 'or)
     (reduce #'cnf-or-clauses
             (mapcar #'cnf-clauses (cdr f))
             :initial-value '(nil)))
    (t (list (list f)))))
 
(defun cnf-or-clauses (cls1 cls2)
  (mapcan (lambda (c1)
            (mapcar (lambda (c2)
                      (remove-duplicates (append c1 c2) :test #'equal))
                    cls2))
          cls1))
 
(defun cnf-render (clauses)
  (let ((rendered
         (mapcar (lambda (clause)
                   (cond
                     ((null clause) nil)
                     ((null (cdr clause)) (car clause))
                     (t (cons 'or clause))))
                 clauses)))
    (cond
      ((null rendered) t)
      ((null (cdr rendered)) (car rendered))
      (t (cons 'and rendered)))))
 
(defun simp-skolem-pnf-cnf (f)
  (let* ((simplified (fo-simplify f))
         (in-nnf     (nnf simplified))
         (skolemized (skolemize in-nnf))
         (in-pnf     (make-pnf skolemized))
         (vars       (if (and (consp in-pnf) (== (car in-pnf) 'forall))
                         (cadr in-pnf)
                       nil))
         (matrix     (if vars (caddr in-pnf) in-pnf))
         (cnf        (cnf-matrix matrix)))
    (if vars
        (list 'forall vars cnf)
      cnf)))
 
(defun run-sppc-tests ()
  (let ((pass 0) (fail 0))
    (labels
      ((no-exists-p (f)
         (cond ((atom f) t)
               ((== (car f) 'exists) nil)
               (t (every #'no-exists-p (cdr f)))))
       (literal-p (f)
         (or (atom f)
             (and (consp f)
                  (== (car f) 'not)
                  (let ((arg (cadr f)))
                    (or (atom arg)
                        (and (consp arg)
                             (not (in (car arg)
                                      '(not and or implies iff if
                                        forall exists)))))))
             (and (consp f)
                  (not (in (car f)
                           '(not and or implies iff if
                             forall exists))))))
       (clause-p (f)
         (or (literal-p f)
             (and (consp f) (== (car f) 'or)
                  (every #'literal-p (cdr f)))))
       (matrix-cnf-p (f)
         (or (clause-p f)
             (and (consp f) (== (car f) 'and)
                  (every #'clause-p (cdr f)))))
       (cnf-p (f)
         (if (and (consp f) (== (car f) 'forall))
             (matrix-cnf-p (caddr f))
           (matrix-cnf-p f)))
       (check (label input expected)
         (let ((result (simp-skolem-pnf-cnf input)))
           (if (equal result expected)
               (progn (incf pass) (format t "PASS ~a~%" label))
               (progn (incf fail)
                      (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                              label input expected result)))))
       (check-props (label input)
         (let* ((result   (simp-skolem-pnf-cnf input))
                (no-exists (no-exists-p result))
                (is-cnf    (cnf-p result)))
           (if (and no-exists is-cnf)
               (progn (incf pass)
                      (format t "PASS ~a  => ~s~%" label result))
               (progn (incf fail)
                      (format t "FAIL ~a  no-exists=~a cnf=~a  got: ~s~%"
                              label no-exists is-cnf result))))))
 
      (check "S1: ground-and"
             '(and (p c1) (q c2))
             '(and (p c1) (q c2)))
 
      (check-props "S2: simple-exists"
                   '(exists x (p x)))
 
      (check-props "S3: forall-only"
                   '(forall (x y) (or (p x) (q y))))
 
      (check-props "S4: forall-exists"
                   '(forall x (exists y (p x y))))
 
      (check-props "S5: forall-implies"
                   '(forall x (implies (p x) (q x))))
 
      (check-props "S6: forall-iff"
                   '(forall x (iff (p x) (q x))))
 
      (check-props "S7: nested-quants"
                   '(exists x (forall y (exists z (p x y z)))))
 
      (check "S8: distribution"
             '(or (p c1) (and (q c2) (r c3)))
             '(and (or (p c1) (q c2))
                   (or (p c1) (r c3))))
 
      (check "S9: simplify-first"
             '(and (exists x (p x)) nil)
             nil)
 
      (check-props "S10: complex"
                   '(forall (x y)
                            (and (implies (p x) (or (q y) (r x)))
                                 (exists z (and (s x z) (t y z))))))
 
      (check-props "S11: double-neg-forall"
                   '(not (not (forall x (p x)))))
 
      (check "S12: prop-cnf"
             '(or (and (p c1) (q c2)) (r c3))
             '(and (or (p c1) (r c3))
                   (or (q c2) (r c3))))
 
      (check "S13: already-cnf"
             '(and (or (p x) (q y)) (or (not (p x)) (r z)))
             '(and (or (p x) (q y)) (or (not (p x)) (r z))))
 
      (check-props "S14: vacuous-quant"
                   '(forall (x y) (p z)))
 
      (check-props "S15: deep-iff"
                   '(forall x
                            (iff (exists y (p x y))
                                 (forall z (q x z))))))
 
    (format t "~%SPPC Results: ~a passed, ~a failed~%" pass fail)))
 
 
(run-sppc-tests)


#|

 Question 4. (15 pts)

 Define unify, a function that given an a non-empty list of pairs,
 where every element of the pair is FO-term, returns an mgu (most
 general unifier) if one exists or the symbol 'fail otherwise.

 An assignment is a list of conses, where car is a variable, the cdr
 is a term and the variables (in the cars) are unique.

 Test your functions using at least 10 interesting inputs. 
 
|#

(defun apply-subst-term (subst term)
  (cond
    ((variable-symbolp term)
     (let ((binding (assoc term subst :test #'equal)))
       (if binding
           (apply-subst-term subst (cdr binding))
         term)))
    ((atom term) term)
    (t (mapcar (lambda (x) (apply-subst-term subst x)) term))))
 
(defun apply-subst-pairs (subst pairs)
  (mapcar (lambda (p)
            (cons (apply-subst-term subst (car p))
                  (apply-subst-term subst (cdr p))))
          pairs))
 
(defun occurs-p (var term)
  (cond
    ((equal var term) t)
    ((atom term) nil)
    (t (some (lambda (x) (occurs-p var x)) term))))
 
(defun unify-step (pairs subst)
  (if (null pairs)
      (values subst t)
    (let* ((pair (car pairs))
           (rest (cdr pairs))
           (s    (car pair))
           (t_   (cdr pair))
           (s    (apply-subst-term subst s))
           (t_   (apply-subst-term subst t_)))
      (cond
        ((equal s t_)
         (unify-step rest subst))
        ((variable-symbolp s)
         (if (occurs-p s t_)
             (values nil nil)
           (let ((new-subst (acons s t_ subst)))
             (unify-step rest new-subst))))
        ((variable-symbolp t_)
         (unify-step (cons (cons t_ s) rest) subst))
        ((and (consp s) (consp t_)
              (equal (car s) (car t_))
              (= (length s) (length t_)))
         (let ((new-pairs (mapcar #'cons (cdr s) (cdr t_))))
           (unify-step (append new-pairs rest) subst)))
        (t (values nil nil))))))
 
(defun normalize-pair (p)
  (if (and (consp p) (consp (cdr p)) (null (cddr p)))
      (cons (car p) (cadr p))
    p))
 
(defun unify (l)
  (let ((pairs (mapcar #'normalize-pair l)))
    (multiple-value-bind (subst ok)
        (unify-step pairs nil)
      (if ok subst 'fail))))
 
(defun run-unify-tests ()
  (let ((pass 0) (fail-count 0))
    (labels
      ((check (label input expected)
         (let ((result (unify input)))
           (if (equal result expected)
               (progn (incf pass) (format t "PASS ~a~%" label))
               (progn (incf fail-count)
                      (format t "FAIL ~a~%  input:    ~s~%  expected: ~s~%  got:      ~s~%"
                              label input expected result)))))
       (check-unifies (label input)
         (let ((result (unify input)))
           (if (eq result 'fail)
               (progn (incf fail-count)
                      (format t "FAIL ~a (got fail unexpectedly)~%" label))
             (let ((ok (every (lambda (p)
                                (equal (apply-subst-term result (car p))
                                       (apply-subst-term result (cdr p))))
                              (mapcar #'normalize-pair input))))
               (if ok
                   (progn (incf pass)
                          (format t "PASS ~a  mgu=~s~%" label result))
                   (progn (incf fail-count)
                          (format t "FAIL ~a  mgu does not unify: ~s~%"
                                  label result))))))))
 
      (check "U1: same-var"
             '((x . x))
             nil)
 
      (check "U2: var-const"
             '((x . c1))
             '((x . c1)))
 
      (check "U3: var-var"
             '((x . y))
             '((x . y)))
 
      (check-unifies "U4: var-compound"
                     '((x . (f c1 c2))))
 
      (check "U5: same-compound"
             '(((f x y) . (f x y)))
             nil)
 
      (check-unifies "U6: compound-vars"
                     '(((f x c1) . (f c2 y))))
 
      (check "U7: occurs-fail"
             '((x . (f x)))
             'fail)
 
      (check "U8: functor-clash"
             '(((f x) . (g x)))
             'fail)
 
      (check "U9: arity-clash"
             '(((f x y) . (f x)))
             'fail)
 
      (check-unifies "U10: multi-pair"
                     '((x . (f y)) (y . c1)))
 
      (check "U11: const-const-same"
             '((c1 . c1))
             nil)
 
      (check "U12: const-const-diff"
             '((c1 . c2))
             'fail)
 
      (check-unifies "U13: nested-compound"
                     '(((f (g x) y) . (f (g c1) (h z)))))
 
      (check-unifies "U14: composition"
                     '((x . (f y)) (x . (f c1))))
 
      (check-unifies "U15: triangle"
                     '((x . (f y)) (y . (g z)) (z . c1))))
 
    (format t "~%Unify Results: ~a passed, ~a failed~%" pass fail-count)))
 
(run-unify-tests)

#|

 Question 5. (25 pts)

 Define fo-no=-val, a function that given a FO formula, without equality,
 checks if it is valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement.

 Test your functions using at least 10 interesting inputs
 including the formulas from the following pages of the book: 178
 (p38, p34), 179 (ewd1062), 180 (barb), and 198 (the Los formula).


|#

(defun literal-pos-p (lit)
  (not (and (consp lit) (== (car lit) 'not))))
 
(defun lit-atom (lit)
  (if (and (consp lit) (== (car lit) 'not))
      (cadr lit)
    lit))
 
(defun lit-negate (lit)
  (if (and (consp lit) (== (car lit) 'not))
      (cadr lit)
    (list 'not lit)))
 
(defun rename-clause (clause)
  (let ((vars (remove-duplicates
               (mapcan (lambda (lit) (free-vars lit)) clause)
               :test #'equal))
        (subst nil))
    (dolist (v vars)
      (push (cons v (fresh-var)) subst))
    (mapcar (lambda (lit) (apply-subst-term subst lit)) clause)))
 
(defun unify-lits (l1 l2)
  (if (and (consp l1) (consp l2) (== (car l1) (car l2)))
      (let ((pairs (mapcar #'cons (cdr l1) (cdr l2))))
        (unify pairs))
    (if (equal l1 l2) nil 'fail)))
 
(defun apply-subst-clause (subst clause)
  (mapcar (lambda (lit) (apply-subst-term subst lit)) clause))
 
(defun match-terms (t1 t2 subst)
  (let ((t1 (apply-subst-term subst t1)))
    (cond
      ((equal t1 t2) subst)
      ((variable-symbolp t1)
       (if (occurs-p t1 t2)
           'fail
         (acons t1 t2 subst)))
      ((or (atom t1) (atom t2)) 'fail)
      ((and (equal (car t1) (car t2))
            (= (length t1) (length t2)))
       (reduce (lambda (s pair)
                 (if (eq s 'fail) 'fail
                   (match-terms (car pair) (cdr pair) s)))
               (mapcar #'cons (cdr t1) (cdr t2))
               :initial-value subst))
      (t 'fail))))
 
(defun match-lits (l1 l2)
  (unless (eq (literal-pos-p l1) (literal-pos-p l2))
    (return-from match-lits 'fail))
  (match-terms (lit-atom l1) (lit-atom l2) nil))
 
(defun subsumed-by-p (c2 c1)
  (subsumed-aux (rename-clause c1) c2 nil))
 
(defun subsumed-aux (c1-rest c2 subst)
  (if (null c1-rest)
      t
    (some (lambda (lit2)
            (let ((s (match-lits (apply-subst-term subst (car c1-rest))
                                 lit2)))
              (and (not (eq s 'fail))
                   (subsumed-aux (cdr c1-rest) c2 s))))
          c2)))
 
(defun forward-subsume (new-clause clause-set)
  (some (lambda (c) (subsumed-by-p new-clause c)) clause-set))
 
(defun backward-subsume (new-clause clause-set)
  (remove-if (lambda (c) (subsumed-by-p c new-clause)) clause-set))
 
(defun unit-propagate (unit-clause all-clauses)
  (let ((neg (lit-negate (car unit-clause))))
    (mapcar (lambda (c)
              (if (equal c unit-clause)
                  c
                (remove neg c :test #'equal)))
            all-clauses)))
 
(defun apply-unit-propagation (clauses)
  (let ((units (remove-if-not (lambda (c) (== (length c) 1)) clauses)))
    (reduce (lambda (cls u) (unit-propagate u cls))
            units :initial-value clauses)))
 
(defun resolve (c1 c2)
  (let ((c1r (rename-clause c1))
        (c2r (rename-clause c2))
        (results nil))
    (dolist (lit1 c1r)
      (dolist (lit2 c2r)
        (when (not (eq (literal-pos-p lit1) (literal-pos-p lit2)))
          (let ((mgu (unify-lits (lit-atom lit1) (lit-atom lit2))))
            (unless (eq mgu 'fail)
              (let* ((r1 (remove lit1 c1r :test #'equal :count 1))
                     (r2 (remove lit2 c2r :test #'equal :count 1))
                     (resolvent
                      (remove-duplicates
                       (apply-subst-clause mgu (append r1 r2))
                       :test #'equal)))
                (push resolvent results)))))))
    results))
 
(defun cnf->clauses (cnf)
  (let ((matrix (if (and (consp cnf) (== (car cnf) 'forall))
                    (caddr cnf)
                  cnf)))
    (cond
      ((== matrix t)   nil)
      ((== matrix nil) '(()))
      ((and (consp matrix) (== (car matrix) 'and))
       (mapcar (lambda (cl)
                 (if (and (consp cl) (== (car cl) 'or))
                     (cdr cl)
                   (list cl)))
               (cdr matrix)))
      ((and (consp matrix) (== (car matrix) 'or))
       (list (cdr matrix)))
      (t (list (list matrix))))))
 
(defparameter *resolution-limit* 10000)
 
(defun try-add-resolvent (r processed unprocessed)
  (cond
    ((null r)                        (values processed unprocessed t))
    ((forward-subsume r processed)   (values processed unprocessed nil))
    ((forward-subsume r unprocessed) (values processed unprocessed nil))
    (t
     (values (backward-subsume r processed)
             (cons r (backward-subsume r unprocessed))
             nil))))
 
(defun resolve-against-processed (c processed unprocessed total)
  (dolist (p processed (values processed unprocessed total nil))
    (unless (equal p c)
      (dolist (r (resolve c p))
        (incf total)
        (multiple-value-bind (np nu ep)
            (try-add-resolvent r processed unprocessed)
          (when ep
            (return-from resolve-against-processed
              (values processed unprocessed total t)))
          (setf processed np  unprocessed nu))))))
 
(defun resolution-loop (initial-clauses)
  (let* ((clauses (remove-duplicates initial-clauses :test #'equal))
         (clauses (apply-unit-propagation clauses)))
    (when (member nil clauses :test #'equal)
      (return-from resolution-loop 'valid))
    (let ((processed  nil)
          (unprocessed clauses)
          (total 0))
      (loop
        (when (> total *resolution-limit*) (return nil))
        (let ((c (or (find-if (lambda (x) (== (length x) 1)) unprocessed)
                     (car unprocessed))))
          (when (null c) (return nil))
          (setf unprocessed (remove c unprocessed :test #'equal :count 1))
          (setf processed (cons c processed))
          (let ((prop (apply-unit-propagation processed)))
            (when (member nil prop :test #'equal)
              (return-from resolution-loop 'valid))
            (setf processed prop))
          (multiple-value-bind (np nu nt ep)
              (resolve-against-processed c processed unprocessed total)
            (when ep (return-from resolution-loop 'valid))
            (setf processed np  unprocessed nu  total nt)))))))
 
(defun fo-no=-val-debug (f)
  (let* ((negated (list 'not f))
         (cnf     (simp-skolem-pnf-cnf negated))
         (clauses (cnf->clauses cnf)))
    (format t "CNF: ~s~%" cnf)
    (format t "Clauses: ~s~%" clauses)
    (when (>= (length clauses) 2)
      (let ((c1 (first clauses))
            (c2 (second clauses)))
        (format t "resolve ~s vs ~s => ~s~%"
                c1 c2 (resolve c1 c2))
        (format t "unify-lits ~s ~s => ~s~%"
                (lit-atom (car c1))
                (lit-atom (car c2))
                (unify-lits (lit-atom (car c1)) (lit-atom (car c2))))))))
 
(defun fo-no=-val (f)
  (let* ((negated (list 'not f))
         (cnf     (simp-skolem-pnf-cnf negated))
         (clauses (cnf->clauses cnf)))
    (if (resolution-loop clauses)
        'valid
      nil)))
 
(defun run-val-tests ()
  (let ((pass 0) (fail-count 0))
    (labels
      ((check-valid (label f)
         (let ((result (fo-no=-val f)))
           (if (eq result 'valid)
               (progn (incf pass) (format t "PASS ~a (valid)~%" label))
               (progn (incf fail-count)
                      (format t "FAIL ~a expected valid, got ~s~%" label result)))))
       (check-not-valid (label f)
         (let ((result (fo-no=-val f)))
           (if (null result)
               (progn (incf pass) (format t "PASS ~a (not valid)~%" label))
               (progn (incf fail-count)
                      (format t "FAIL ~a expected not-valid, got ~s~%" label result))))))
 
      (check-valid "V1: excluded-middle-prop"
                   '(or (p c1) (not (p c1))))
 
      (check-valid "V2: implies-self"
                   '(implies (p c1) (p c1)))
 
      (check-valid "V3: and-elim"
                   '(implies (and (p c1) (q c1)) (p c1)))
 
      (check-not-valid "V4: not-valid"
                       '(implies (p c1) (q c1)))
 
      (check-valid "V5: forall-to-exists"
                   '(implies (forall x (p x)) (exists x (p x))))
 
      (check-valid "V6: forall-and-elim"
                   '(implies (forall x (and (p x) (q x)))
                             (forall x (p x))))
 
      (check-valid "V7: p38"
                   '(implies
                     (and (forall x (implies (p x) (q x)))
                          (forall x (implies (q x) (r x))))
                     (forall x (implies (p x) (r x)))))
 
      (check-valid "V8: p34-drinker"
                   '(exists x (implies (d x) (forall y (d y)))))
 
      (check-valid "V9: ewd1062"
                   '(implies
                     (and (exists x (p x))
                          (forall x (implies (p x) (q x))))
                     (exists x (q x))))
 
      (check-not-valid "V10: barb-not-valid"
                       '(exists x (forall y (iff (shaves x y)
                                                 (not (shaves y y))))))
 
      (check-valid "V12: double-neg"
                   '(implies (not (not (p c1))) (p c1)))
 
      (check-valid "V13: modus-ponens"
                   '(implies (and (p c1) (implies (p c1) (q c1)))
                             (q c1)))
 
      (check-not-valid "V14: exists-not-forall"
                       '(implies (exists x (p x)) (forall x (p x)))))
 
    (format t "~%Validity Results: ~a passed, ~a failed~%" pass fail-count)))
 
(run-val-tests)

#|

 Question 6. Extra Credit (20 pts)

 Define fo-val, a function that given a FO formula, checks if it is
 valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement. This is an extension of question 5,
 where you replace equality with a new relation symbol and add
 the appropriate equivalence and congruence hypotheses.

|#

(defun fo-val (f) ...)
