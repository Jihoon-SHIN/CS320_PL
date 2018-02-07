#lang plai


;20150441 Jihoon,Shin

;;For String to S-exp

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


;syntax of KCFAE
; fun takes a multile parameter, app takes a multiple argument
;add the try*catch and throw
(define-type KCFAE
  [num (n number?)]
  [add (lhs KCFAE?)
       (rhs KCFAE?)]
  [sub (lhs KCFAE?)
       (rhs KCFAE?)]
  [id (name symbol?)]
  [fun (param (listof symbol?))
       (body KCFAE?)]
  [app (fun-expr KCFAE?)
       (arg-expr (listof KCFAE?))]
  [if0 (test KCFAE?)
       (then KCFAE?)
       (else KCFAE?)]
  [withcc (name symbol?)
          (body KCFAE?)]
  [try*catch (try KCFAE?)
             (catch KCFAE?)]
  [throw])

(define-type KCFAE-Value
  [numV (n number?)]
  [closureV (param (listof symbol?))
            (body KCFAE?)
            (sc DefrdSub?)]
  [contV (proc procedure?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value KCFAE-Value?)
        (rest DefrdSub?)])

;; ----------------------------------------

;; parse : S-expr -> KCFAE
(define (parse-sexpr sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (if (symbol=? 'throw sexp) (throw)
                        (id sexp))]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse-sexpr (second sexp)) (parse-sexpr (third sexp)))]
       [(-) (sub (parse-sexpr (second sexp)) (parse-sexpr (third sexp)))]
       ;[(fun) (fun (first (second sexp)) (parse-sexpr (third sexp)))]
       [(fun) (fun (second sexp) (parse-sexpr (third sexp)))] ;adjust the fun
       [(if0) (if0 (parse-sexpr (second sexp))
                   (parse-sexpr (third sexp))
                   (parse-sexpr (fourth sexp)))]
       [(withcc) (withcc (second sexp) (parse-sexpr (third sexp)))]
       [(try) (try*catch (parse-sexpr (second sexp)) (parse-sexpr (fourth sexp)))]
       [else (app (parse-sexpr (first sexp)) (app-parse (cdr sexp)))])]))


; app-parse list -> list
; parse the list and makes the KCFAE list.
; (app-parse '(1 2)) should produce (list (num 1) (num 2))
(define (app-parse sexp)
  (cond [(empty? sexp) empty]
        [else
         (cons (parse-sexpr (first sexp)) (app-parse (cdr sexp)))]))

(define (parse str)
  (parse-sexpr (string->sexpr str)))


;(test (parse 3) (num 3))
;(test (parse 'x) (id 'x))
;(test (parse '{+ 1 2}) (add (num 1) (num 2)))
;(test (parse '{- 1 2}) (sub (num 1) (num 2)))
;(test (parse '{fun {x} x}) (fun 'x (id 'x)))
;(test (parse '{1 2}) (app (num 1) (num 2)))
;(test (parse '{if0 0 1 2}) (if0 (num 0) (num 1) (num 2)))
;(test (parse '{withcc x 2}) (withcc 'x (num 2)))




;; ----------------------------------------

;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) -> alpha
(define (interp a-fae ds k cat)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num+ v1 v2))) cat)) cat)]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num- v1 v2))) cat)) cat)]
    [id (name) (k (lookup name ds))]
    [fun (param body-expr)
         (k (closureV param body-expr ds))]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (interp2 arg-expr ds
                           (lambda (arg-val)
                             (type-case KCFAE-Value fun-val
                               [closureV (param body ds)
                                         (if (not (= (length param) (length arg-val))) (error "Number of arg-val different from number of param") ;;when number of argument of function is different from number of parameter.
                                         (interp body
                                                 ;(aSub param
                                                 ;      arg-val
                                                 ;      ds)
                                                 (makesub param arg-val ds)
                                                 k cat))]
                               [contV (k)
                                      (k (first arg-val))]
                               [else (error 'interp "not a function")])) cat)) cat)]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (numzero? v)
                       (interp then-expr ds k cat)
                       (interp else-expr ds k cat))) cat)]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id
                          (contV k)
                          ds)
                    k cat)]
    [try*catch (try catch)
               (interp try ds k
                       (lambda ()
                         (interp catch ds k cat)))]
    [throw () (cat)]))

;interp2: arg-expr(KCFAE) defrdSub procedure procedure -> procedure
;app의 arg-expr이 여러 개의 input이라면, procedure k의 값에 넘겨 줄 때, interp된 값들을 넘겨주어야하므로 interp2함수가 필요하다.
(define (interp2 arg ds k cat)
  [cond [(empty? arg) (k empty)]
        [else
         (interp (first arg) ds
                 (lambda (v1)
                   (interp2 (cdr arg) ds
                            (lambda (v2) (k (cons v1 v2))) cat)) cat)]])


; makesub: id (listof FWAE) ds -> defrdSub
; In the app, if param and arg-val is a list, we need to make a multiple defrdSub.
; (maekSub '(x y) (list (num 1) (num 2))) (mtSub)) should produce (aSub 'x (numV 1) (aSub 'y (numV 2) (mtSub)))
(define (makesub param arg-val ds)
  (cond [(empty? param) ds]
        [else
         (aSub (first param) (first arg-val) (makesub (cdr param) (cdr arg-val) ds))]))

;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-sc)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-sc))]))

;(test/exn (lookup 'x (mtSub)) "free variable")
;(test (lookup 'x (aSub 'x (numV 9) (mtSub))) (numV 9))
;(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 9) (mtSub)))) (numV 9))


;; interp-expr : KCFAE -> KCFAE-Value
(define (interp-expr a-fae)
  (type-case KCFAE-Value (interp a-fae (mtSub) (lambda (x) x) (lambda () (error "there is undefined throw"))) ;when there is no lambda in throw.
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]))

;; run : str -> KCFAE-Value
(define (run str)
  (interp-expr (parse str)))

;; My own test;;
(test/exn (run "{{fun {x y z} {+ x y z}} 1 2}") "Number of arg-val different from number of param")
(test/exn (run "{try {throw} catch {throw}}") "there is undefined throw") 
(test (run "{{fun {z} z} {withcc esc {{fun {a b} a} 1 {esc {{fun {x y} {- y x}} 10 12}} 10}}}") 2)
(test (run "{try {try {try {throw} catch {throw}} catch {throw}} catch 15}") 15)
(test (run "{- 20 {withcc k {- 15 {k {{fun {} 6}}}}}}") 14)
(test (run "{fun {x y} {+ x y}}") 'function)


;; Test code;; 
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(run "{withcc esc {{fun {x y} x} 1 {esc 3}}}")

(test (run "{try 7 catch 8}")
      7)
(test (run "{try {throw} catch 8}")
      8)
(test (run "{try {+ 1 {throw}} catch 8}")
      8)
(test (run "{{fun {f} {try {f 3} catch 8}}
               {fun {x} {throw}}}")
      8)
(test (run "{try {try {throw} catch 8} catch 9}")
      8)
(test (run "{try {try {throw} catch {throw}} catch 9}")
      9)
(test (run "{try {try 7 catch {throw}} catch 9}")
      7)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}}
               {fun {x} {throw}}}")
      8)

; multiple arguments (5)
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)

; exceptions (35)
(test (run "{+ {withcc k {k 5}} 4}" ) 9)
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}") 55) ; recursive function
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}") 100) ; exit from recursive function using continuation
(test (run "{withcc k {- 0 {k 100}}}" ) 100)
(test (run "{withcc k {k {- 0 100}}}" ) -100)
(test (run "{withcc k {k {+ 100 11}}}" ) 111)
(test (run "{{fun {a b c} {- {+ {withcc k {+ {k 100} a}} b} c}} 100 200 300}" ) 0)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{{withcc esc {{fun {x y} {fun {z} {+ z y}}} 1 {withcc k {esc k}}}} 10}") 20)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {+ y {g g {- y 1}}}}} 10} catch 110}") 110) ; exit from recursive function using try-catch
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch y}}} 10}") 54) ; equal? for multiple recursive try-catch
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {done y}}}} 10}}") 2)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {throw}}}} 10} catch 20110464}") 20110464) ; recursive try-catch throwing (1)
(test (run "{try {{fun {x y z} {a b c}} 1 2 {throw}} catch 0}") 0)
(test (run "{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}") 8)
(test (run "{try {- 0 {withcc k {+ 3 {k {throw}}}}} catch 89}") 89)
(test (run "{try {+ 3 {withcc k {+ 1000 {k {throw}}}}} catch 11}") 11)
(test (run "{{fun {x y z} {try {+ 1 {+ x {throw}}} catch {+ y z}}} 1 2 3}") 5)
(test (run "{+ {try {- 10 {throw}} catch 3} 10}") 13)
(test (run "{try {if0 0 {throw} {+ 1 2}} catch {if0 10 1 {try {throw} catch 54}}}") 54)
(test (run "{try {withcc a {+ 1 {withcc b {throw}}}} catch 10}") 10)
(test (run "{try {- 0 {throw}} catch 5}") 5)
(test (run "{try {if0 {throw} 3 4} catch 5}") 5)
(test (run "{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}") -1)
(test (run "{try {try {throw} catch {throw}} catch 9}") 9)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}") 5)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}") 10)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}") 42)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}") 3)
(test (run "{withcc esc {try {+ {throw} {esc 3}} catch 4}}") 4)
(test (run "{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}") 15)
(test (run "{try {withcc x {+ {x 1} {throw}}} catch 0}") 1)
(test (run "{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}") 19)

; multiple arguments (6)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x done}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}") 1099)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}") 11053)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {+ y {g g {- y 1} z}}}} 10}}}") 0)
(test (run "{withcc done {{fun {f x} {f f x {fun {x} {if0 x {fun {y} {fun {x} {+ x y}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}}") 64)
(test (run "{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}} 5}") 'function)
(test (run "{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}}") 42)

; exceptions (4)
(test (run "{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}} catch 4242}") 4242)
(test (run "{withcc esc {{try {withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} catch esc} 33}}") 33)
(test (run "{try {try {throw} catch {try {throw} catch {try {throw} catch {+ {withcc k {try {throw} catch {k 0}}} {throw}}}}} catch 0}") 0)
(test (run "{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {throw}}}}} catch 4242}") 4242)