#lang plai
;20150441 Jihoon,Shin

; pre-defined Function
(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

(define (symbol<? a b) (string<? (symbol->string a) (symbol->string b)))

;1
; free-ids : WAE -> list-of-sym
; to find a free identifier
; (free-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) should produce '(a)


(define (free-ids wae)
  (type-case WAE wae
    [num (n) '()]
    [add (l r) (sort (remove-duplicates (append (free-ids l) (free-ids r))) symbol<?)]
    [sub (l r) (sort (remove-duplicates (append (free-ids l) (free-ids r))) symbol<?)]
    [with (y i b) (sort (remove-duplicates (append (free-ids i) (check y b))) symbol<?)]
    [id (s) (list s)]))
; check : symbol WAE -> list-of-sym
; free-ids 에서 거르지 못한 free-identifier들을 걸러내주는 역할을 한다. 
(define (check x wae)
  (type-case WAE wae
    [num (n) '()]
    [add (l r) (sort (remove-duplicates (append (check x l) (check x r))) symbol<?)]
    [sub (l r) (sort (remove-duplicates (append (check x l) (check x r))) symbol<?)]
    [with (y i b) (remove x (sort (remove-duplicates (append (free-ids i) (check y b))) symbol<?))]
    [id (s) (if (symbol=? s x)
                '()
                (list s))]))
    
;2
; binding-ids : WAE -> list-of-sym
; to find a binding occurences
; (binding-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) should produce '(x y)
(define (binding-ids wae)
  (type-case WAE wae
    [num (n) '()]
    [add (l r) (sort (remove-duplicates (append (binding-ids l) (binding-ids r))) symbol<?)]
    [sub (l r) (sort (remove-duplicates (append (binding-ids l) (binding-ids r))) symbol<?)]
    [with (y i b) (sort (remove-duplicates (append (list y) (binding-ids i) (binding-ids b))) symbol<?)]
    [id (s) '()]))

;3
; bound-ids : WAE -> list-of-sym
; to find a bound occurences
; (bound-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) should produce '(x)

(define (bound-ids wae)
  (type-case WAE wae
    [num (n) '()]
    [add (l r) (sort (remove-duplicates (append (bound-ids l) (bound-ids r))) symbol<?)]
    [sub (l r) (sort (remove-duplicates (append (bound-ids l) (bound-ids r))) symbol<?)]
    [with (y i b) (sort (remove-duplicates (append (check_bound y b) (if (id? i) '() (bound-ids i)))) symbol<?)]
    [id (s) '()]))

; check-bound : symbol WAE -> list-of-sym
; bound-ids 함수에서 찾지 못하는 bound occurences들을 찾아내준다.
(define (check_bound x wae)
  (type-case WAE wae
    [num (n) '()]
    [add (l r) (sort (remove-duplicates (append (check_bound x l) (check_bound x r))) symbol<?)]
    [sub (l r) (sort (remove-duplicates (append (check_bound x l) (check_bound x r))) symbol<?)]
    [with (y i b) (sort (remove-duplicates (append (check_bound x i) (check_bound y b) (check_bound x b))) symbol<?)]
    [id (s) (if (symbol=? s x)
                (list s)
                '())]))
; free-ids own test
(test (free-ids (with 'x (with 'x (num 3) (with 'y (num 5) (sub (id 'x) (id 'a)))) (add (id 'k) (id 'y)))) '(a k y))
(test (free-ids (with 'x (num 5) (with 'y (num 3) (add (num 3) (id 'z))))) '(z))
(test (free-ids (add (with 'y (id 'x) (sub (num 3) (id 'k))) (num 5))) '(k x))
;binding-ids own test
(test (binding-ids (id 'x)) '())
(test (binding-ids (with 'x (num 6) (with 'y (id 'y) (add (num 3) (id 'y))))) '(x y))
;bound-ids own test
(test (bound-ids (id 'x)) '())
(test (bound-ids (with 'x (num 5) (add (num 5) (id 'x)))) '(x))
(test (bound-ids (add (with 'y (id 'x) (add (id 'y) (id 'y))) (with 'k (num 5) (add (id 'k) (num 1))))) '(k y))
;; free-ids
(test (free-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x))))) '())
(test (free-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(a))
(test (free-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b)))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b y))
(test (free-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b t y))
(test (free-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))) '(x y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a)))) '(a b c y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(b c d y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(b c d y z))
;; binding-ids
(test (binding-ids (add (num 3) (sub (id 'x) (id 'y)))) '())
(test (binding-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(x y))
(test (binding-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y))))) '(y))
(test (binding-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))) '(x y))
(test (binding-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(w z))
;; bound-ids
(test (bound-ids (with 'x (num 3) (add (id 'y) (num 3)))) '())
(test (bound-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) '(x))
(test (bound-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y)))))) '(x y))
(test (bound-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y))))) '(x y))
(test (bound-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7)))))) '(x))
(test (bound-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x)))))))) '(x z))
(test (bound-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(y))
(test (bound-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z)))))))) '(x y z))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(x))
