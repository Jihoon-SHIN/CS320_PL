#lang plai


;BFAE = FAE + Boxes
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
  [seqn (seqn (listof BFAE?))]
  [rec (arr list?)]
  [get (rec BFAE?) (arg BFAE?)]
  [sett (first BFAE?) (second BFAE?) (third BFAE?)])

; BFAE-Value
(define-type BFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body BFAE?) (ds DefrdSub?)]
  [boxV (address integer?)]
  [recordV (lst list?)])

; DefrdSub
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value BFAE-Value?) (rest DefrdSub?)])
; Store
(define-type Store
  [mtSto]
  [aSto (address integer?) (value BFAE-Value?) (rest Store?)])
; Value*Store
(define-type Value*Store
  [v*s (value BFAE-Value?) (store Store?)])


;; parse : S-expr -> BFAE
;; Parsing the S-expression and make the BFAE.
;; (parse '{{fun {r} {get r x}} {rec {x 1}}}) should produce (app (fun 'r (get (id 'r) (id 'x))) (rec (list (list (id 'x) (num 1)))))
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
       [(seqn)  (seqn (map parse (cdr sexp)))]
       [(rec) (rec (map recparse (cdr sexp)))]
       [(get) (get (parse (second sexp)) (parse (third sexp)))]
       [(set) (sett (parse (second sexp)) (parse (third sexp)) (parse (fourth sexp)))]
       [else (app (parse (first sexp)) (parse (second sexp)))])]))


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


;; recparse : sexpr-list -> BFAE
;; {rec {x 1} {y 2}} rec은 다음과 같은 형태를 취하기 때문에
;; {x 1} 과 같은 형태를 parse하기 위해 recparse를 만들었다.
(define (recparse lst)
  (list (parse (first lst)) (parse (last lst))))

;; interp-expr : bcfae -> value
;; interp-expr로 나오는 BFAE-Value를 value로 바꿔주거나, 'func 'record 'box 와 같은 값을 리턴할 수 있게 해준다.
;; interp-expr은 오직 interp-e를 통해서만 사용된다.
(define (interp-expr bcfae)
  (local [(define answer1 (interp-e bcfae (mtSub) (mtSto)))
          (define answer (v*s-value (interp-e bcfae (mtSub) (mtSto))))]
  (cond [(closureV? answer) 'func]
        [(recordV? answer) 'record]
        [(boxV? answer) (if (recordV? (store-lookup (boxV-address answer) (v*s-store answer1)))
                            'record
                            'box)]
        [(numV? answer) (numV-n answer)]
        [(v*s? answer) (numV-n (v*s-value answer))]
        [else answer])))
    

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
         (v*s (closureV param body-expr ds) st)         ]
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

    [setbox (bx-expr val-expr)
            (interp-two bx-expr val-expr ds st
                        (lambda (bx-val val st1)
                          (v*s val
                               (store-change (boxV-address bx-val) st1 bx-val val)
                               )))]
    [openbox (bx-expr)
             (type-case Value*Store (interp bx-expr ds st)
               [v*s (bx-val st1)
                    (v*s (store-lookup (boxV-address bx-val)
                                       st1)
                         st1)])]
    [seqn (x) (if (not (= 1 (length x))) (interp-list (car x) (cdr x) ds st
                                         (lambda (v1 v2 st1) (v*s v2 st1)))
                  (interp (car x) ds st))]
    [rec (x) bcfae]
    [get (x y) bcfae]
    [sett (x y z) bcfae]))

; store-change : integer aSto BFAE-value BFAE-value -> aSto
; (setbox (be-expr val-expr)) 에서 setbox는 현재 주소에 있는 값을
; val-expr로 바꿔주어야하므로, store-change 함수가 필요하다.
; (store-change 1 (aSto 1 (numV 1) (mtSto)) (boxV 1) (numV 2)) should produce (aSto 1 (numV 2) (mtSto))
(define (store-change addr st bx-val val1)
  (type-case Store st
    [mtSto () st]
    [aSto (sto-addr val rest-st)
                 (if (= addr sto-addr)
                     (aSto addr val1 rest-st)
                     (aSto sto-addr val (store-change addr rest-st bx-val val1)))]))

;; interp-two : BFAE BFAE DefrdSub Store (Value Value Store -> Value*Store
;; -> Value*Store
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         (type-case Value*Store (interp expr2 (if (setbox? expr1)
                                                  (aSub (aSub-name ds) (boxV (boxV-address (aSub-value ds))) (aSub-rest ds))
                                                  ds) st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)])]))

;; interp-list : BFAE (listof BFAE) DefrdSub Store (Value Value Store -> Value*Store
;; -> Value*Store
;; to calute seqn. seqn has a list argument so interp-two is not working well in some cases.
(define (interp-list expr1 list1 ds st handle)
  (cond [(= 1 (length list1))
         (type-case Value*Store (interp expr1 ds st)
           [v*s (val1 st2)
                (type-case Value*Store (interp (car list1) (if (setbox? expr1)
                                                         (aSub (aSub-name ds) (boxV (boxV-address (aSub-value ds))) (aSub-rest ds))
                                                         ds) st2)
                  [v*s (val2 st3)
                       (handle val1 val2 st3)])])]
        [else
         (type-case Value*Store (interp expr1 ds st)
           [v*s (val1 st2)
                (interp-list (car list1) (cdr list1) (if (setbox? expr1)
                                                         (aSub (aSub-name ds) (boxV (boxV-address (aSub-value ds))) (aSub-rest ds))
                                                         ds) st2 handle)])]))

; interp에서 rec, get, set을 추가한 형태로 interp-expr에만 사용된다.
;; interp-e : BFAE DefrdSub Store -> Value*Store
(define (interp-e bcfae ds st)
  (type-case BFAE bcfae
    [num (n) (v*s (numV n) st)]
    [add (l r) (interp-twoe l r ds st
                           (lambda (v1 v2 st1) (v*s (num+ v1 v2) st1)))]
    [sub (l r) (interp-twoe l r ds st
                           (lambda (v1 v2 st1) (v*s (num- v1 v2) st1)))]
    [id (name) (v*s (lookup name ds) st)]
    [fun (param body-expr)
         (v*s (closureV param body-expr ds) st)]
    [rec (x)
      (local [(define recv (recordV
            (map (lambda (r) (list (car r) (interp-e (cadr r) ds st))) x)))
              (define a (malloc st))]
        (v*s (boxV a) (aSto a recv st)))]
    [get (x y)
         (type-case Value*Store (interp-e x ds st)
           [v*s (val st1)
                (local [(define recv
                          (store-lookup (boxV-address val) st1))]
                  (if (recordV? recv) (checkget y recv ds st1)
                      (v*s val st1))
                  )])]
    [sett (x y z)
          (type-case Value*Store (interp-e x ds st)
            [v*s (val st1)
                 (type-case Value*Store (interp-e z ds st1)
                   [v*s (val1 st2)
                        (local [(define a (change-e (boxV-address val) st2 y (interp-e z ds st1)))]
                          (v*s (v*s-value (interp-e z ds st2)) a))])])]
    
    [app (fun-expr arg-expr)
         (interp-twoe fun-expr arg-expr ds st
                     (lambda (fun-val arg-val st1)
                       (interp-e (closureV-body fun-val)
                                
                               (aSub (closureV-param fun-val)
                                     arg-val
                                     (closureV-ds fun-val))
                               st1)))]
    [newbox (expr)
            (type-case Value*Store (interp-e expr ds st)
              [v*s (val st1)                   
                   (local [(define a (malloc st1))]
                     (v*s (boxV a)
                          (aSto a val st1)))])]
    [setbox (bx-expr val-expr)
            (interp-twoe bx-expr val-expr ds st
                        (lambda (bx-val val st1)
                          (v*s val
                               (store-change (boxV-address bx-val) st1 bx-val val)
                               )))]
    [openbox (bx-expr)
             (type-case Value*Store (interp-e bx-expr ds st)
               [v*s (bx-val st1)
                    (v*s (store-lookup (boxV-address bx-val)
                                       st1)
                         st1)])]
    [seqn (x) (if (< 1  (length x)) (interp-liste (car x) (cdr x) ds st
                                         (lambda (v1 v2 st1) (v*s v2 st1)))
                  (interp-e (first x) ds st))]))

;; interp-two : BFAE BFAE DefrdSub Store (Value Value Store -> Value*Store
;; -> Value*Store
(define (interp-twoe expr1 expr2 ds st handle)
  (type-case Value*Store (interp-e expr1 ds st)
    [v*s (val1 st2)
         (type-case Value*Store (interp-e expr2 ds st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)])]))

;; interp-list : BFAE (listof BFAE) DefrdSub Store (Value Value Store -> Value*Store
;; -> Value*Store
;; to calute seqn more than two or equal.
(define (interp-liste expr1 list1 ds st handle)
  (cond [(= 1 (length list1))
         (type-case Value*Store (interp-e expr1 ds st)
           [v*s (val1 st2)
                (type-case Value*Store (interp-e (car list1) (if (setbox? expr1)
                                                         (aSub (aSub-name ds) (boxV (boxV-address (aSub-value ds))) (aSub-rest ds))
                                                         ds) st2)
                  [v*s (val2 st3)
                       (handle val1 val2 st3)])])]
        [else
         (type-case Value*Store (interp-e expr1 ds st)
           [v*s (val1 st2)
                (interp-liste (car list1) (cdr list1) (if (setbox? expr1)
                                                         (aSub (aSub-name ds) (boxV (boxV-address (aSub-value ds))) (aSub-rest ds))
                                                         ds) st2 handle)])]))


; change-e : address aSto id BFAE-value -> aSto
; (set x y z) 에서 aSto의 value의 값을 바꿔주어야하는데, aSto의 형태를 유지시켜주어야하므로, change-e를 사용하여 재귀해주고,
; aSto 의 value값은 chane-val을 실행하여 바꿔준다.
(define (change-e addr st x val)
  (type-case Store st
    [mtSto () st]
    [aSto (sto-addr val1 rest-st)
          (if (= addr sto-addr)
              (aSto addr (recordV (change-val (recordV-lst val1) x val)) rest-st)
              (aSto sto-addr val1 (change-e addr rest-st x val)))]))

; change-val : list id BFAE-value -> list
; set에서 왔으므로 이것은 recordV일 것이므로, (recordV (list (list ( ) ( ))) 이와 같은 형태를 가지고 있고 change-val에서의 list는
; (list (list () ())) 이고, 이 리스트에서 id와 일치하는 값을 BFAE-val(val)로 바꿔주고 이 형태를 유지해주어야한다.
; 따라서 change-val로 형태를 유지하여 주면서 helper 함수를 통해 값을 바꾸어준다.
(define (change-val lst x val)
  (if (null? lst) '()
    (append (helper (first lst) x val) (change-val (cdr lst) x val))))


; helper : list id BFAE-value -> list
; recordV에서 id와 같은 값이 나오면 그 id에 대응하는 값을 BFAE-value로 바꾸어준다. 같은 값이 아니면 인자로 받은 list 그 자체를 리턴해준다.
(define (helper lst x val)
    (cond [(null? lst) '()]
          [else
           (if (symbol=? (id-name (first lst)) (id-name x))
               (list (list x (v*s (v*s-value val) (v*s-store (last lst)))))
               (list lst))]))

; checkget : id recordV defrdSub Store -> Value*Store
; get함수에서 id와 같은 값을 찾아내어, Value*Store의 형태로 리턴해준다.
; id와 같은 값이 없으면 "no such field"라는 오류 메시지를 프린트한다.
(define (checkget y rec ds st)
  (let ((lst (filter (lambda (x) (symbol=? (id-name y)
                                           (id-name (first x))))
                     (recordV-lst rec))))
    (if (empty? lst) (error "no such field")
        (v*s (v*s-value (last (first lst))) st))))


;;;;;my-own test code;;;;;;
(test (interp (parse '{seqn 2 4})
              (mtSub)
              (mtSto))
      (v*s (numV 4) (mtSto)))

(test/exn (interp-expr (parse '{{fun {r}
                                 {get r y}}
                            {rec {x 1}}}))
      "no such field")

(test/exn (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 z}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {rec {a 0} {b 2}}}                ; r1
                            {rec {a 3} {b 4}}}))               ; r2
      "no such field")


(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b {+ 2 (openbox b)}}
                             {setbox b {- 3 (openbox b)}}
                             {setbox b {+ 4 (openbox b)}}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
        (v*s (numV 4)
             (aSto 1 (numV 4) (mtSto))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b 2}
                             {setbox b 5}
                             {setbox b 6}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
      (v*s (numV 6)
           (aSto 1 (numV 6) (mtSto))))

(test (interp-expr (parse '{{fun {r} {- {setbox {get r x} 3} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 0)

(test/exn (interp (parse '{openbox x})
                  (aSub 'x (boxV 5) (mtSub))
                  (mtSto))
          "unallocated")


;;;;;test code;;;;;;;;;
(test (interp (parse '{seqn 1 2})
              (mtSub)
              (mtSto))
      (v*s (numV 2) (mtSto)))

(test (interp (parse '{{fun {b} {openbox b}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 1 (numV 10) (mtSto))))

(test (interp (parse '{{fun {b} {seqn
                                 {setbox b 12}
                                 {openbox b}}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 12)
           (aSto 1
                 (numV 12)
                 (mtSto))))

(test (interp-expr (parse '{{fun {b} {seqn
                                      {setbox b 12}
                                      {openbox b}}}
                            {newbox 10}}))
      12)

(test (interp (parse '{{fun {b} {openbox b}}
                       {seqn
                        {newbox 9}
                        {newbox 10}}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))

(test (interp (parse '{{{fun {b}
                             {fun {a}
                                  {openbox b}}}
                        {newbox 9}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 9)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))
(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b 2}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
      (v*s (numV 2)
           (aSto 1 (numV 2) (mtSto))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b {+ 2 (openbox b)}}
                             {setbox b {+ 3 (openbox b)}}
                             {setbox b {+ 4 (openbox b)}}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))


(test/exn (interp (parse '{openbox x})
                  (aSub 'x (boxV 1) (mtSub))
                  (mtSto))
          "unallocated")

;; records

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {rec {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {rec {x 1}}}))
      5)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {rec {a 0} {b 2}}}                ; r1
                            {rec {a 3} {b 4}}}))               ; r2
      5)

(test (interp-expr (parse '{fun {x} x}))
      'func)
(test (interp-expr (parse '{newbox 1}))
      'box)
(test (interp-expr (parse '{rec}))
      'record)

(test (interp (parse '{{fun {b} {setbox b 2}} {seqn {newbox 0} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {b} {setbox b 2}} {newbox 0}}) (mtSub) (aSto 1 (numV 0) (mtSto))) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{{fun {a} {fun {b} {setbox a 2}}} {newbox 1}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 0) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{+ {{fun {b} {setbox b 2}} {newbox 0}} {{fun {b} {setbox b 2}} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 4) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{newbox {{fun {b} {setbox b 2}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (boxV 2) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 3 (numV 3) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{seqn {newbox 0} {setbox x 1} {openbox x}}) (aSub 'x (boxV 1) (mtSub)) (aSto 1 (numV 0) (mtSto))) (v*s (numV 1) (aSto 2 (numV 0) (aSto 1 (numV 1) (mtSto)))))
(test (interp (parse '{{fun {b} {+ {openbox b} {seqn {setbox b 2} {openbox b}}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 1 (numV 2) (mtSto))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b {- {openbox b} 1}} {setbox a {+ {openbox a} 1}} {newbox 0} {openbox b}}} {newbox 1}}} {newbox 2}}) (aSub 'a (boxV 0) (mtSub)) (mtSto)) (v*s (numV 0) (aSto 3 (numV 0) (aSto 2 (numV 0) (aSto 1 (numV 3) (mtSto))))))
(test (interp (parse '{seqn {newbox 1}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (numV 1) (mtSto))))
(test (interp (parse '{setbox {{fun {b} {seqn {newbox b} {newbox b}}} 0} 1}) (mtSub) (mtSto)) (v*s (numV 1) (aSto 2 (numV 1) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b 2} {setbox a {fun {c} {+ c 1}}} {{openbox a} {openbox b}}}} {openbox a}}} {newbox {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (closureV 'c (add (id 'c) (num 1)) (aSub 'b (boxV 1) (aSub 'a (boxV 2) (mtSub)))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{seqn 1 {fun {x} {+ x 1}} {newbox 2} {{fun {x} {setbox x {newbox 1}}} {newbox 3}}}) (mtSub) (mtSto)) (v*s (boxV 3) (aSto 3 (numV 1) (aSto 2 (boxV 3) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{{fun {b} {seqn {setbox b b} {openbox b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {openbox {setbox b b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {- {openbox b} {seqn {setbox b b} {setbox {openbox b} 1} {openbox b}}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV -1) (aSto 1 (numV 1) (mtSto))))
(test (interp-expr (parse '{{fun {b} {{fun {a} {seqn {set a x {openbox b}} {setbox b 1} {set a y {openbox b}} {get a x}}} {rec {x 1} {y 2}}}} {newbox 0}})) 0)
(test (interp-expr (parse '{set {rec {x 1}} x 0})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r1} {{fun {r} {seqn {set r x 0} {get r1 x}}} {rec {x 1} {y 2}}}} {rec {x 3} {y 4}}})) 3)
(test (interp-expr (parse '{{fun {r} {+ {get r x} {seqn {set r x 2}}}} {rec {z 3} {y 2} {x 1}}})) 3)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {openbox {get {openbox b} y}}}} {newbox {rec {x 1} {y 2}}}})) 'record)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {get {openbox {get {openbox b} y}} y}}} {newbox {rec {x 1} {y 2}}}})) 'box)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {+ {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 4)
