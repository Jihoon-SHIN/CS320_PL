#lang plai

(define-type BFAE
  [num (n number?)]
  {add (lhs BFAE?) (rhs BFAE?)}
  [sub (lhs BFAE?) (rhs BFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body BFAE?)]
  [app (fun-expr BFAE?) (arg-expr BFAE?)]
  [newbox (val-expr BFAE?)]
  [setbox (box-expr BFAE?) (val-expr BFAE?)]
  [openbox (box-expr BFAE?)]
  [seqn (arr list?)])

(define-type BFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body BFAE?) (ds DefrdSub?)]
  [boxV (address integer?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value BFAE-Value?) (rest DefrdSub?)])

(define-type Store
  [mtSto]
  [aSto (address integer?) (value BFAE-Value?) (rest Store?)])

(define-type Value*Store
  [v*s (value BFAE-Value?) (store Store?)])

;; parse : S-expr -> BFAE
(define (parse sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse (second sexp)) (parse (third sexp)))]
       [(-) (sub (parse (second sexp)) (parse (third sexp)))]
       [(fun) (fun (first (second sexp)) (parse (third sexp)))]
       [(newbox) (newbox (parse (second sexp)))]
       [(setbox) (setbox (parse (second sexp)) (parse (third sexp)))]
       [(openbox) (openbox (parse (second sexp)))]
       [(seqn) (seqn (map parse (cdr sexp)))]
       [else (app (parse (first sexp)) (parse (second sexp)))])]))

;; interp : BFAE DefrdSub Store -> Value*Store
(define (interp bcfae ds st)
  (type-case BFAE bcfae
    [num (n) (v*s (numV n) st)]
    [add (l r) (interp-two l r ds st
                           (lambda (v1 v2 st1) (v*s (num+ v1 v2) st1)))]
    [sub (l r) (interp-two l r ds st
                           (lambda (v1 v2 st1) (v*s (num- v1 v2) st1)))]
    [id (name) (v*s (lookup name ds) st)]
    [fun (param body-expr)
         (v*s (closureV param body-expr ds) st)]
    [app (fun-expr arg-expr)
         (interp-two fun-expr arg-expr ds st
                     (lambda (fun-val arg-val st1)
                       (interp (closureV-body fun-val)
                               (aSub (closureV-param fun-val)
                                     arg-val
                                     (closureV-ds fun-val))
                               st1)))]
    [newbox (expr)
            (type-case Value*Store (interp expr ds st)
              [v*s (val st1)
                   (local [(define a (malloc st1))]
                     (v*s (boxV a)
                          (aSto a val st1)))])]
    
    ;[setbox (bx-expr val-expr)
    ;        (type-case Value*Store (interp bx-expr ds st)
    ;          [v*s (val1 st1)
    ;               (local [(define a (boxV (+ 1 (boxV-address val1))))]
    ;                 (type-case Value*Store (interp val-expr ds (aSto (malloc st1) (aSto-value st1) (aSto-rest st1)))
    ;                   [v*s (val2 st2)
    ;                        (v*s val2
    ;                             (aSto (boxV-address a)
    ;                                   val1
    ;                                   (mtSto)))]))])]

    [setbox (bx-expr val-expr)
            (interp-two bx-expr val-expr ds st
                        (lambda (bx-val val st1)
                          (v*s (boxV (+ 1 (boxV-address bx-val)))
                               (aSto (+ 1 (boxV-address bx-val))
                                     val
                                     (mtSto)))))]
    [openbox (bx-expr)
             (type-case Value*Store (interp bx-expr ds st)
               [v*s (bx-val st1)
                    (print st1)
                    (print bx-val)
                    (print (boxV-address bx-val))
                    (v*s (store-lookup (boxV-address bx-val)
                                       st1)
                         st1)])]
    [seqn (a b) (interp-two a b ds st
                            (lambda (v1 v2 st1) (v*s v2 st1)))]))

;; interp-two : BFAE BFAE DefrdSub Store (Value Value Store -> Value*Store
;; -> Value*Store
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         (type-case Value*Store (interp expr2 (if (setbox? expr1)
                                                  (aSub (aSub-name ds) (boxV (+ 1 (boxV-address (aSub-value ds)))) (aSub-rest ds))
                                                  ds) st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)])]))

;; num-op : (number number -> number) -> (BFAE-Value BFAE-Value -> BFAE-Value)
(define (num-op op x y)
  (numV (op (numV-n x) (numV-n y))))
(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))

;; malloc : Store -> integer
(define (malloc store)
  (type-case Store store
    [mtSto () 1]
    [aSto (addr val rest) (+ addr 1)]))

;; lookup : symbol DefrdSub -> BFAE-Value
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error "free variable")]
    [aSub (sub-name val rest-ds)
          (if (symbol=? sub-name name)
              val
              (lookup name rest-ds))]))

;; store-lookup : number Store -> BFAE-Value
(define (store-lookup addr st)
  (type-case Store st
    [mtSto () (error "unallocated")]
    [aSto (sto-addr val rest-st)
          (if (= addr sto-addr)
              val
              (store-lookup addr rest-st))]))


(test (interp (parse '{{fun {b}
                          {seqn
                           {setbox b 2}
                           {openbox b}}}
                         {newbox 1}})
                (mtSub)
                (mtSto))
        (v*s (numV 2)
             (aSto 1 (numV 2) (mtSto))))
