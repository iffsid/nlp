(module nlp *
(import chicken scheme extras)
(use nondeterminism define-structure srfi-1 srfi-13 traversal irregex)

;;; these should be put elsewhere
(define (flatten* l)
 (if (null? l)
     '()
     (if (list? (car l))
	 (flatten* (append (car l) (cdr l)))
	 (cons (car l) (flatten* (cdr l))))))

;; (define (nondeterministic-map f l)
;;  (let loop ((c '()) (l l))
;;   (if (null? l) (reverse c) (loop (cons (f (first l)) c) (rest l)))))

;; (define (string-join delim l)
;;  (if (null? l) "" (foldl (lambda (a b) (string-append a delim b)) (cdr l) (car l))))

(define (fields str) (irregex-split 'whitespace str))

(define (o a b . c)
 (let ((fs (cons a (cons b c))))
  (lambda d (foldl (lambda (x f) (f x)) (rest (reverse fs)) (apply (last fs) d)))))

(define (maximump l p)
 (define (m p l x)
  (if (null? l) x
      (if (> (p (car l)) (p x)) (m p (cdr l) (car l)) (m p (cdr l) x))))
 (when (not (null? l)) (m p (cdr l) (car l))))

(define (initial-sublist? ref l)
 (and (> (length ref) (length l))
    (let loop ((l1 l) (l2 ref))
     (if (null? l1) #t (and (equal? (car l1) (car l2)) (loop (cdr l1) (cdr l2)))))))
;;; ------

(define-structure cfg rules)
(define-structure production-rule lhs rhs)
(define (create-cfg rules)
 (unless (and (not (some list? (map production-rule-lhs rules)))
	    (not (every list? (map production-rule-lhs rules))))
  (error "Production rule: NT (terminals* U NT*)"))
 (make-cfg rules))
(define p-lhs production-rule-lhs)
(define p-rhs production-rule-rhs)

(define (cfg:a-valid-rhs rhs)
 (qremove #f (nondeterministic-map (lambda (r) (if (list? r) (either #f (car r)) r)) rhs)))

(define (cfg:non-terminal? symbol cfg)
 (member symbol (map p-lhs (cfg-rules cfg))))

(define (cfg:terminal? symbol cfg)
 (not (cfg:non-terminal? symbol cfg)))

(define (cfg:terminals cfg)
 (qset-difference (flatten* (map p-rhs (cfg-rules cfg))) (map p-lhs (cfg-rules cfg))))

(define (cfg:non-terminals cfg)
 (qremove-duplicates (map p-lhs (cfg-rules cfg))))

(define (cfg:terminal-categories cfg)
 (qremove-duplicates
  (removeq
   #f
   (map (lambda (r) (and (not (some (lambda (t) (cfg:non-terminal? t cfg)) (p-rhs r))) (p-lhs r)))
	(cfg-rules cfg)))))

(define (cfg:optional-categories-with-rules cfg)
 (map
  (lambda (c) (list (caar c) (map second c)))
  (transitive-equivalence-classes
   (lambda (a b) (equal? (car a) (car b)))
   (map-reduce
    append
    '()
    (lambda (r) (map (lambda (a) (list (car a) r)) (remove-if-not list? (production-rule-rhs r))))
    (cfg-rules cfg)))))

(define (cfg:possible-rules lhs rules)
 (remove-if-not (lambda (r) (equal? (p-lhs r) lhs)) rules))

(define (cfg:lexicalized-terminals cfg)
 (map
  (lambda (rhs) (string-join " " (map symbol->string rhs)))
  (remove-if
   (lambda (r) (or (some list? r) (some (lambda (t) (cfg:non-terminal? t cfg)) r)))
   (map p-rhs (cfg-rules cfg)))))

(define (lexicalize es cfg . symbol)
 (let ((terminals (map string-downcase (cfg:lexicalized-terminals cfg)))
       (lex (lambda (l) (string-join (if (null? symbol) "-" (symbol->string (car symbol))) (fields l)))))
  (let loop ((ws (map (o string-downcase symbol->string) es)) (b "") (l '()))
   (if (null? ws)
       (map (o string->symbol string-downcase) (reverse (cons (lex b) l)))
       (if (member b terminals)
	   (loop ws "" (cons (lex b) l))
	   (loop (rest ws) (string-append b (if (equal? b "") "" " ") (car ws)) l))))))

(define (lexicalize-phrase phrase cfg)
 (string-join
  "_"
  (map (o string-downcase symbol->string)
       (lexicalize (map string->symbol (fields phrase)) cfg '+))))

;; optionally takes a start non-terminal to begin parsing from
(define (sentence:parse-sentence sentence cfg . start)
 (define rules (cfg-rules cfg))
 (define terminals (cfg:terminals cfg))
 (define tokens (map string->symbol (fields (string-downcase sentence))))
 (define (num-terminals p) (length (qintersection (flatten* p) terminals)))
 (define (longest-parse parses) (if (null? parses) '() (maximump parses num-terminals)))
 (find-if
  (lambda (p) (equal? (qintersection (flatten* p) terminals) tokens))
  (map
   (lambda (start-rule)
    (let loop ((rule start-rule) (stack (take tokens 1)) (tokens (cdr tokens)))
     (cond
      ((equal? (p-rhs rule) stack) (cons (p-lhs rule) stack))
      ((initial-sublist? (p-rhs rule) stack) (loop rule (append stack (take tokens 1)) (cdr tokens)))
      (else (longest-parse
	     (all-values
	      (cons (p-lhs rule)
		    (nondeterministic-map
		     (lambda (r)
		      (let* ((poss (cfg:possible-rules r rules))
			     (parse (if (null? poss) (fail) (loop (a-member-of poss) stack tokens))))
		       (if (null? parse)
			   (fail)
			   (begin
			    (local-set! tokens (drop tokens (- (num-terminals parse) (length stack))))
			    (unless (null? tokens)
			     (local-set! stack (take tokens 1))
			     (local-set! tokens (cdr tokens)))
			    parse))))
		     (cfg:a-valid-rhs (p-rhs rule))))))))))
   (remove-if-not (lambda (r) (eq? (p-lhs r) (if (null? start) 'S (car start)))) rules))))

(define (sentence:parse-sentence-any sentence cfg)
 (call/cc
  (lambda (return)
   (for-each
    (lambda (nt) (let ((parse (sentence:parse-sentence sentence cfg nt))) (when parse (return parse))))
    (cfg:non-terminals cfg)))))

;;; this needs the tree and zipper data structures

;; (define (theta-role-assignments sentence cfg semantics)
;;  (define parse (sentence:parse-sentence-any sentence cfg))
;;  (define terminal-categories (cfg:terminal-categories cfg))
;;  (define (head-noun ztree cfg)
;;   (let ((n (find-if (lambda (e) (eq? (car e) 'N)) (tree->leaves (zipper-tree ztree) ip-leaf?))))
;;    (unless n (error "head-noun: noun not pund in parse:~%~a~%" ztree))
;;    `#(,(car (lexicalize (take-until vector? (rest n)) cfg)) ,(vector->list (last n)))))
;;  (define (assign-roles ztree)
;;   (if (member (car (zipper-tree ztree)) terminal-categories)
;;       (let ((terminal (car (lexicalize (take-until vector? (cdr (zipper-tree ztree))) cfg))))
;;        (append
;; 	(list (car (zipper-tree ztree)) terminal)
;; 	(let loop ((ztree ztree) (terms '()) (l (length (semantics terminal))))
;; 	 (if (zero? l)
;; 	     terms
;; 	     (if (zipper:can-ascend? ztree)
;; 		 (let ((new-ztree (zipper:ascend ztree)))
;; 		  (loop new-ztree (cons (head-noun new-ztree cfg) terms) (- l 1)))
;; 		 (loop ztree (cons `#(thing (,l)) terms) (- l 1)))))))
;;       (cons (car (zipper-tree ztree))
;; 	    (all-values
;; 	     (assign-roles
;; 	      (zipper:descend ztree (an-integer-between 1 (- (length (zipper-tree ztree)) 1))))))))
;;  (unless parse (error "Failed parse~%  sentence: ~a~%" sentence))
;;  (tree->leaves (assign-roles (zipper:initialize (index-leaves parse p-leaf? '()))) ip-leaf?))

;;; examples

;; (define (*set1:semantics* lexical-entry)
;;  (let ((all-roles '(agent patient referent goal source)))
;;   (case lexical-entry
;;    ((to-the-left-of) `((agent patient) (referent)))
;;    ((to-the-right-of) `((agent patient) (referent)))
;;    ((picked-up) `((agent) (patient)))
;;    ((put-down) `((agent) (patient)))
;;    ((carried) `((agent) (patient)))
;;    ((approached) `((agent) (goal)))
;;    ((towards) `((agent patient) (goal)))
;;    ((away-from) `((agent patient) (source)))
;;    (else `(,all-roles)))))

;; (define *set1:cfg*
;;  (create-cfg
;;   (list (make-production-rule 'S '(NP VP))
;; 	(make-production-rule 'NP '(D (A) N (PP)))
;; 	(make-production-rule 'D '(an))
;; 	(make-production-rule 'D '(the))
;; 	(make-production-rule 'A '(blue))
;; 	(make-production-rule 'A '(red))
;; 	(make-production-rule 'N '(person))
;; 	(make-production-rule 'N '(backpack))
;; 	(make-production-rule 'N '(trash-can))
;; 	(make-production-rule 'N '(chair))
;; 	(make-production-rule 'N '(object))
;; 	(make-production-rule 'PP '(P NP))
;; 	(make-production-rule 'P '(to the left of))
;; 	(make-production-rule 'P '(to the right of))
;; 	(make-production-rule 'VP '(V NP (ADV) (PPM)))
;; 	(make-production-rule 'V '(picked up))
;; 	(make-production-rule 'V '(put down))
;; 	(make-production-rule 'V '(carried))
;; 	(make-production-rule 'V '(approached))
;; 	(make-production-rule 'ADV '(quickly))
;; 	(make-production-rule 'ADV '(slowly))
;; 	(make-production-rule 'PPM '(PM NP))
;; 	(make-production-rule 'PM '(towards))
;; 	(make-production-rule 'PM '(away from)))))

)
