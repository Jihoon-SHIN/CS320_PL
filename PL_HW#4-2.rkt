#lang plai


;20150441 Ji hoon ,Shin

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))


;num-op : FWAE FWAE -> FWAE-Value
;to calulate the '+ and '- and it have to version num+ and num-
;(num+ (num 3) (num 5)) should produce (numV 8)
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))


; define type FWAE
(define-type FWAE
  [num (n number?)]
  [add (lhs FWAE?) (rhs FWAE?)]
  [sub (lhs FWAE?) (rhs FWAE?)]
  [with (name symbol?) (named-expr FWAE?) (body FWAE?)]
  [id (name symbol?)]
  [fun (param (listof FWAE?)) (body FWAE?)]
  [app (ftn FWAE?) (arg (listof FWAE?))]
  [record (arr list?)]
  [getField (rec FWAE?) (arg FWAE?)])



; parse-sexpr : sexpr -> FWAE
;; to convert s-expressions into FWAE
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?) (id sexp)]
    [(list 'fun (list a ...) b) (if (check-duplicates a)
                                    (error "bad syntax")
                                    (fun (map parse-sexpr a) (parse-sexpr b)))]
    [(list 'record x ...) (if (check-duplicate x) (record (map Recparse x))      
                              (error "duplicate fields"))]
    [(list 'getField x y) (getField (parse-sexpr x) (parse-sexpr y))]           
    [(list a b ...) (app (parse-sexpr a) (map parse-sexpr b))]
    [else (error 'parse "bad syntax: ~a" sexp)]))


; Recparse : lst -> lst
; to parsing the record. 'record는 (a b)와 같은 원소를 포함하므로 각각을 parse 시켜주어야해서 parse함수를 새로 정의했다.
(define (Recparse lst)                                                           
  (list (parse-sexpr (first lst)) (parse-sexpr (last lst))))

; parse
; string을 sexpression으로 바꾼후에 위에서 정의한 parse-sexpr을 이용하여
; string을 FWAE로 parsing해주는 작업을 진행한다.
(define (parse str)
  (parse-sexpr (string->sexpr str)))


;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
;; subst is not used because i use defrdsub.
(define (subst fwae x val)
  (type-case FWAE fwae
    [num (n) fwae]
    [add (l r) (add (subst l x val) (subst r x val))]
    [sub (l r) (sub (subst l x val) (subst r x val))]
    [with (y i b) (with y
                        (subst i x val)
                        (if (symbol=? y x) b
                            (subst b x val)))]
    [id (name) (cond [(equal? name x) val]
                     [else exp])]
    [app (f arg) (app (subst f x val)
                      (subst arg x val))]
    [record (x) fwae]
    [getField (x y) fwae]
    [fun (id body) (if (equal? x id)
                       fwae
                       (fun id (subst body x val)))]))

; lookup : symbol DefrdSub -> number
; defrdsub에 input으로 들어오는 symbol과 같은 symbol을 가진 값이 있는지 확인하고 있으면 저장한 value를 return하고
; 그렇지 않다면 뒤에거를 확인한다. 만약 확인하다가 mtsub가 나오면 그것은 free identifier라고 선언해준다.

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier")]
    [aSub (x val rest)
          (if (symbol=? x name)
              val
              (lookup name rest))]))

; check-duplicate list -> boolean
; recording하는 변수들이 중복되어있는지 확인.
; 중복되어있다면 #f 를 중복되어있지 않다면 #t를 반환
(define (check-duplicate exp)
  (if (null? exp) '()
      (not (check-duplicates (make-lst exp)))))

; make-lst list -> list
; record함수에서 제가 원하는 id 들만 뽑아내는 함수입니다.
(define (make-lst exp)
  (if (null? exp) '()
      (cons (caar exp) (make-lst (cdr exp)))))

; Defrdsub
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FWAE-Value?) (ds DefrdSub?)])


; checkf : symbol FWAE -> list of FWAE
; record list안에 들어있는 찾고자하는 getField의 변수를 찾아서 그것을 리턴한다.
; 여기서 no such field도 걸러낼 수 있다.
; (checkf (id 'a) (recordV  (list (list (id 'a) (num 10))))) should produce (numV 10)
(define (checkf rec y ds)
  (let ((lst (filter (lambda (x) (symbol=? (id-name rec)
                                           (id-name (first x))))
             (recordV-lst y))))
    (if (empty? lst) (error "no such field")
        (interp (last (first lst)) ds))))

(define-type FWAE-Value
  [numV (n number?)]
  [closureV (param (listof FWAE?)) (body FWAE?) (ds DefrdSub?)]
  [recordV (lst list?)])

; chage FWAE-Value -> FWAE
; to covert FWAE-Value into FWAE
; (chage (numV 5)) should produce (num 5)
(define (change lst)
  (type-case FWAE-Value lst
    [numV (n) (num n)]
    [closureV (param body ds) (fun param body)]
    [recordV (lst) (record lst)]))

; interp : FWAE -> FWAE-Value
; caculate the FWAE and return proper FWAE-Value.
; (interp (add (num 5) (num 6))) should produce (numV 11)
(define (interp fwae ds)
  (type-case FWAE fwae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [with (x i b) (interp b (aSub x (interp i ds) ds))]
    [id (s) (lookup s ds)]
    [fun (x b) (closureV x b ds)]
    [record (x) (recordV (map (lambda (r) (list (car r) (change (interp (cadr r) ds)))) x))]                            
    [getField (x y) (if (number? (checkf y (interp x ds) ds))
                        (numV (checkf y (interp x ds) ds))
                        (checkf y (interp x ds) ds))]
    [app (f a) (local [(define f-val (interp f ds))
                       (define (recul a b ds)
                         (cond ((null? a)
                                (if (null? b)
                                    ds
                                    (error "wrong arity")))
                               ((empty? b)
                                (if (null? a)
                                    ds
                                    (error "wrong arity")))
                               (else  
                                (recul (cdr a) (cdr b) (aSub (id-name (car a)) (car b) ds)))))]
                 (interp (closureV-body f-val)
                         (recul (closureV-param f-val)
                                (map (lambda (x) (interp x ds)) a) ds)))]))

; run string -> FWAE-value or number
; run the function in the proper way case by case.
(define (run str)                                              
  (cond ((closureV? (interp (parse str) (mtSub))) 'function)
        ((recordV? (interp (parse str) (mtSub))) 'record)
        ((numV? (interp (parse str) (mtSub))) (numV-n (interp (parse str) (mtSub))))
        (else (interp (parse str) (mtSub)))))


(interp (parse "{record {a 2} {b {- 3 2}}}") (mtSub))

;;;My test;;;
(test (run "{fun {+ x 1} x}") 'function)
(test/exn (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}} {getField {f 1 2 3 4} c}}") "wrong arity")
(test (run "{record {a 2} {b {- 3 2}}}") 'record)
(test (run "{with {h {fun {x y z w} {+ x w}}}
                  {h 100 200 300 400}}") 500) 
(test/exn (run "{getField {record {a {record {b 0}}}} b}")
          "no such field")
(test/exn (run "{getField {record {a 10} {b {+ 1 2}} {a 20}} b}")
          "duplicate fields")


;;;Test code;;;
(test (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}} {getField {f 1 2 3 4 5} c}}") 3)
(test (run "{with {f {fun {a b c} {record {a a} {b b} {c c}}}}
                  {getField {f 1 2 3} b}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} y}}") 2)
(test (run "{record {a 10} {b {+ 1 2}}}")
      'record)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}")
      3)
(test/exn (run "{getField {record {b 10} {b {+ 1 2}}} b}")
          "duplicate fields")
(test/exn (run "{getField {record {a 10}} b}")
          "no such field")
(test (run "{with {g {fun {r} {getField r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}")
      12)
(test (run "{getField {record {r {record {z 0}}}} r}")
      'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}")
      0)
(test/exn (run "{record {z {getField {record {z 0}} y}}}")
          "no such field")
(test (run "{with {f {fun {a b} {+ a b}}}
                  {with {g {fun {x} {- x 5}}}
                        {with {x {f 2 5}} {g x}}}}") 2)
(test (run "{with {f {fun {x y} {+ x y}}} {f 1 2}}") 3)
(test (run "{with {f {fun {} 5}}
                  {+ {f} {f}}}") 10)
(test (run "{with {h {fun {x y z w} {+ x w}}}
                  {h 1 4 5 6}}") 7) 
(test (run "{with {f {fun {} 4}}
                  {with {g {fun {x} {+ x x}}}
                        {with {x 10} {- {+ x {f}} {g 4}}}}}") 6)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {x 3} {with {y 5} {getField {record {a x} {b y}} a}}}") 3)
(test (run "{with {f {fun {a b} {+ {getField a a} b}}}
                  {with {g {fun {x} {+ 5 x}}}
                        {with {x {f {record {a 10} {b 5}} 2}} {g x}}}}") 17)
(test (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}}
                  {getField {f 1 2 3 4 5} c}}") 3)
(test (run "{with {f {fun {a b c} {record {a a} {b b} {c c}}}}
                  {getField {f 1 2 3} b}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} y}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} d}}") 2)
(test (run "{with {f {fun {x} {+ 5 x}}}
                  {f {getField {getField {record {a {record {a 10} {b {- 5 2}}}} {b {getField {record {x 50}} x}}} a} b}}}") 8)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{record {a 10}}") 'record)
(test (run "{getField {record {a 10}} a}") 10)
(test (run "{getField {record {a {+ 1 2}}} a}") 3)
(test (run "{fun {x} x}") 'function)
(test (run "{getField {record {a {record {b 10}}}} a}") 'record)
(test (run "{getField {getField {record {a {record {a 10}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{+ {getField {record {a 10}} a} {getField {record {a 20}} a}}") 30)
(test (run "{+ {getField {record {a 10}} a} {getField {record {a 20}} a}}") 30)
(test (run "{record {a 10}}") 'record)
(test (run "{record {a {- 2 1}}}") 'record)
(test (run "{getField {record {a 10}} a}") 10)
(test (run "{getField {record {a {- 2 1}}} a}") 1)
(test (run "{getField {record {a {record {b 10}}}} a}") 'record)
(test (run "{getField {getField {record {a {record {a 10}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {getField y y}}") 2)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {getField y z}}") 3)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{with {g {fun {r} {getField r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)