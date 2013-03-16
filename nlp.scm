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

(define (fields str) (irregex-split 'whitespace str))

(define (dtrace s v) (format #t "~a: ~a~%" s v) v)

(define (o a b . c)
 (let ((fs (cons a (cons b c))))
  (lambda d (foldl (lambda (x f) (f x)) (apply (last fs) d) (rest (reverse fs))))))

(define (group-by f l)
 (transitive-equivalence-classes (lambda (a b) (equal? (f a) (f b))) l))

(define (take-until p l)
 (let loop ((l l) (a '())) (if (or (null? l) (p (car l))) (reverse a) (loop (cdr l) (cons (car l) a)))))

(define (drop-until p ls)
 (let loop ((ls ls)) (if (or (null? ls) (p (car ls))) ls (loop (cdr ls)))))

(define (v0 v) (vector-ref v 0))
(define (v1 v) (vector-ref v 1))
(define (v2 v) (vector-ref v 2))
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
 (delete #f (nondeterministic-map (lambda (r) (if (list? r) (either #f (car r)) r)) rhs)))

(define (cfg:non-terminal? symbol cfg)
 (member symbol (map p-lhs (cfg-rules cfg))))

(define (cfg:terminal? symbol cfg)
 (not (cfg:non-terminal? symbol cfg)))

(define (cfg:terminals cfg)
 (set-difference equal? (flatten* (map p-rhs (cfg-rules cfg))) (map p-lhs (cfg-rules cfg))))

(define (cfg:non-terminals cfg)
 (remove-duplicates equal? (map p-lhs (cfg-rules cfg))))

(define (cfg:terminal-categories cfg)
 (remove-duplicates
  equal?
  (removeq
   #f
   (map (lambda (r) (and (not (some (lambda (t) (cfg:non-terminal? t cfg)) (p-rhs r))) (p-lhs r)))
	(cfg-rules cfg)))))

(define (cfg:optional-categories-with-rules cfg)
 (map
  (lambda (c) (list (caar c) (map second c)))
  (group-by
   first
   (map-reduce
    append
    '()
    (lambda (r) (map (lambda (a) (list (car a) r)) (remove-if-not list? (production-rule-rhs r))))
    (cfg-rules cfg)))))

(define (cfg:possible-rules lhs rules)
 (remove-if-not (lambda (r) (equal? (p-lhs r) lhs)) rules))

(define (cfg:lexicalized-terminals cfg)
 (map
  (lambda (rhs) (string-join (map symbol->string rhs) " "))
  (remove-if
   (lambda (r) (or (some list? r) (some (lambda (t) (cfg:non-terminal? t cfg)) r)))
   (map p-rhs (cfg-rules cfg)))))

(define (lexicalize es cfg . symbol)
 (let ((terminals (map string-downcase (cfg:lexicalized-terminals cfg)))
       (lex (lambda (l) (string-join (fields l) (if (null? symbol) "-" (symbol->string (car symbol)))))))
  (let loop ((ws (map (o string-downcase symbol->string) es)) (b "") (l '()))
   (if (null? ws)
       (map (o string->symbol string-downcase) (reverse (cons (lex b) l)))
       (if (member b terminals)
	   (loop ws "" (cons (lex b) l))
	   (loop (rest ws) (string-append b (if (equal? b "") "" " ") (car ws)) l))))))

(define (lexicalize-phrase phrase cfg)
 (string-join
  (map (o string-downcase symbol->string)
       (lexicalize (map string->symbol (fields phrase)) cfg '+))
  "_"))

(define (match-prefix? ref l)
 (and (> (length ref) (length l))
    (let loop ((l1 l) (l2 ref))
     (if (null? l1) #t (and (equal? (car l1) (car l2)) (loop (cdr l1) (cdr l2)))))))

;; optionally takes a start non-terminal to begin parsing from
(define (nlp:parse-sentence sentence cfg . start)
 (define rules (cfg-rules cfg))
 (define terminals (cfg:terminals cfg))
 (define tokens (map string->symbol (fields (string-downcase sentence))))
 (define (num-terminals p) (length (set-intersection equal? (flatten* p) terminals)))
 (define (longest-parse parses) (if (null? parses) '() (maximum num-terminals parses)))
 (find-if
  (lambda (p) (equal? (set-intersection equal? (flatten* p) terminals) tokens))
  (map
   (lambda (start-rule)
    (let loop ((rule start-rule) (stack (take tokens 1)) (tokens (cdr tokens)))
     (cond
      ((equal? (p-rhs rule) stack) (cons (p-lhs rule) stack))
      ((match-prefix? (p-rhs rule) stack) (loop rule (append stack (take tokens 1)) (cdr tokens)))
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

(define (nlp:parse-sentence-any sentence cfg)
 (call/cc
  (lambda (return)
   (for-each
    (lambda (nt) (let ((parse (nlp:parse-sentence sentence cfg nt))) (when parse (return parse))))
    (cfg:non-terminals cfg)))))

;;; helpers specific to parse-tree
(define (p-leaf? l) (every symbol? l))
(define (ip-leaf? l)
 (let ((pre (take-until vector? l)) (post (drop-until vector? l)))
  (and (every symbol? pre) (every vector? post))))

(define (index-leaves tree leaf? prefix)
 (if (leaf? tree)
     (append tree (list (list->vector prefix)))
     (cons (car tree)
	   (all-values
	    (let ((i (an-integer-between 1 (length (cdr tree)))))
	     (index-leaves (list-ref tree i) leaf? (cons i prefix)))))))

(define (tree->leaves tree leaf?)
 (let ((leaves '()))
  (if (leaf? tree)
      (set! leaves (cons tree leaves))
      (let loop ((tree tree))
       (all-values
	(let ((t (a-member-of tree)))
	 (cond ((not (list? t)) (fail))
	       ((leaf? t) (set! leaves (cons t leaves)))
	       (else (loop t)))))))
  (reverse leaves)))

(define (nlp:theta-role-assignments sentence cfg semantics)
 (define parse (nlp:parse-sentence-any sentence cfg))
 (define terminal-categories (cfg:terminal-categories cfg))
 (define (head-noun ztree cfg)
  (let ((n (find-if (lambda (e) (eq? (car e) 'N)) (tree->leaves (zipper-tree ztree) ip-leaf?))))
   (unless n (error "head-noun: noun not pund in parse:~%~a~%" ztree))
   `#(,(car (lexicalize (take-until vector? (rest n)) cfg)) ,(vector->list (last n)))))
 (define (assign-roles ztree)
  (if (member (car (zipper-tree ztree)) terminal-categories)
      (let ((terminal (car (lexicalize (take-until vector? (cdr (zipper-tree ztree))) cfg))))
       (append
	(list (car (zipper-tree ztree)) terminal)
	(let loop ((ztree ztree) (terms '()) (l (length (semantics terminal))))
	 (if (zero? l)
	     terms
	     (if (zipper:can-ascend? ztree)
		 (let ((new-ztree (zipper:ascend ztree)))
		  (loop new-ztree (cons (head-noun new-ztree cfg) terms) (- l 1)))
		 (loop ztree (cons `#(thing (,l)) terms) (- l 1)))))))
      (cons (car (zipper-tree ztree))
	    (all-values
	     (assign-roles
	      (zipper:descend ztree (an-integer-between 1 (- (length (zipper-tree ztree)) 1))))))))
 (unless parse (error "Failed parse~%  sentence: ~a~%" sentence))
 (tree->leaves (assign-roles (zipper:initialize (index-leaves parse p-leaf? '()))) ip-leaf?))

(define (nlp:sentence->participants-and-roles sentence cfg semantics)
 (let* ((theta-roles (nlp:theta-role-assignments sentence cfg semantics))
	(all-roles '(agent patient referent goal source))
	(participant-role-pairs
	 (map
	  (lambda (g)
	   (let ((r (map-reduce (lambda (a b) (set-intersection equal? a b)) all-roles second g)))
	    (when (null? r) (error "Inconsistent role assignments: ~a" g))
	    (when (> (length r) 1) (format #t "Ambiguous role assignments: ~a~%" g))
	    (list (first r) (caar g))))
	  (group-by
	   first
	   (join
	    (map
	     (lambda (e)
	      (let* ((role-entities (drop-until vector? e)) (roles (semantics (second e))))
	       (unless (= (length roles) (length role-entities))
		(error "Semantics and assignments don't match!:~% semantics: ~a~% roles: ~a~%"
		       roles role-entities))
	       (map list role-entities roles)))
	     theta-roles))))))
  `(,(map (o string-downcase symbol->string v0 second) participant-role-pairs)
    ,(map list
	  (map first participant-role-pairs)
	  (map (o string-downcase symbol->string v0 second) participant-role-pairs)))))

)
