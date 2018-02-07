#lang plai-typed

(define (num-op op x y)
  (numV (op (numV-n x) (numV-n y))))

(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))


(define-type EXPR
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : EXPR) (rhs : EXPR)]
  [sub (lhs : EXPR) (rhs : EXPR)]
  [equ (lhs : EXPR) (rhs : EXPR)]
  [id (name : symbol)]
  [fun (param : symbol) (paramty : TE) (body : EXPR)]
  [app (fun-expr : EXPR) (arg-expr : EXPR)]
  [ifthenelse (test-expr : EXPR) (then-expr : EXPR) (else-expr : EXPR)]
  [rec (name : symbol) (ty : TE) (named-expr : EXPR) (body : EXPR)]
  [with-type (name : symbol)
             (var1-name : symbol) (var1-ty : TE)
             (var2-name : symbol) (var2-ty : TE)
             (body-expr : EXPR)]
  [cases (name : symbol)
         (dispatch-expr : EXPR)
         (var1-name : symbol) (bind1-name : symbol) (rhs1-expr : EXPR)
         (var2-name : symbol) (bind2-name : symbol) (rhs2-expr : EXPR)]
  [tfun (name : symbol) (expr : EXPR)]
  [tapp (body : EXPR) (type : TE)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (param : TE) (result : TE)]
  [polyTE (forall : symbol) (body : TE)]
  [idTE (name : symbol)]
  [tvTE (name : symbol)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (param : Type) (result : Type)]
  [polyT (forall : symbol) (body : Type)]
  [idT (name : symbol)]
  [tvT (name : symbol)])

(define-type EXPR-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : symbol) (body : EXPR) (ds : DefrdSub)]
  [variantV (right? : boolean) (val : EXPR-Value)]
  [constructorV (right? : boolean)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol) (value : EXPR-Value) (rest : DefrdSub)]
  [aRecSub (name : symbol) (valuebox : (boxof 'a)) (rest : DefrdSub)])

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest-ds)
          (if (symbol=? sub-name name)
              val
              (lookup name rest-ds))]
    [aRecSub (sub-name val-box rest-ds)
             (if (symbol=? sub-name name)
                 (unbox val-box)
                 (lookup name rest-ds))]))

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol) (type : Type) (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol) (var1-type : Type)
         (var2-name : symbol) (var2-type : Type)
         (rest : TypeEnv)])


;interp expr defrdsub -> EXPR-value
; 전의 숙제에서 짜던 interp함수의 내용이 대부분입니다.

(define (interp expr ds)
  (type-case EXPR expr
    [num (n) (numV n)]
    [bool (b) (boolV b)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [equ (l r) (if (= (numV-n (interp l ds)) (numV-n (interp r ds)))
                   (boolV true)
                   (boolV false))]
    [id (x) (lookup x ds)]
    [fun (param te body) (closureV param body ds)]
    [app (fun-expr arg-expr)
         (local [(define fun-val (interp fun-expr ds))
                 (define arg-val (interp arg-expr ds))]
           (type-case EXPR-Value fun-val
             [closureV (param body ds)
                       (interp body (aSub param arg-val ds))]
             [constructorV (right?)
                           (variantV right? arg-val)]
             [else (error 'interp "not applicable")]))]
    [ifthenelse (test then els) (if (boolV-b (interp test ds))
                                    (interp then ds)
                                    (interp els ds))]
    [rec (bound-id type named-expr body-expr)
      (local [(define value-holder (box (numV 42)))
              (define new-ds
                (aRecSub bound-id value-holder ds))]
        (begin
          (set-box! value-holder (interp named-expr new-ds))
          (interp body-expr new-ds)))]
    [with-type (type-name var1-name var1-te
                          var2-name var2-te
                          body-expr)
      (interp body-expr
              (aSub var1-name
                    (constructorV false)
                    (aSub var2-name
                          (constructorV true)
                          ds)))]
    [cases (ty dispatch-expr
               var1-name var1-id var1-rhs
               var2-name var2-id var2-rhs)
      (type-case EXPR-Value (interp dispatch-expr ds)
        [variantV (right? val)
                  (if (not right?)
                      (interp var1-rhs (aSub var1-id val ds))
                      (interp var2-rhs (aSub var2-id val ds)))]
        [else (error 'interp "not a variant result")])]
    [tfun (sy body) (interp body ds) ]
    [tapp (tfn ty)  (interp tfn ds)]))

; validtype : type environment -> environment
(define (validtype ty env)
  (type-case Type ty
    [numT () (mtEnv)]
    [boolT () (mtEnv)]
    [arrowT (a b) (begin (validtype a env)
                         (validtype b env))]
    [idT (id) (find-type-id id env)]
    [polyT (forall body) (validtype body (aBind forall (tvT forall) env))]
    [tvT (name) (if (numT? (get-type name env)) (mtEnv)
                    (mtEnv))
         ;(find-type-id name env)
         ]))

; parse-type : TE -> TYPE
; 유저가 입력한 TE를
; 컴퓨터의 방식인 TYPE으로 바꾸어줍니다.
(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (arg result) (arrowT (parse-type arg) (parse-type result))]
    [polyTE (forall body) (polyT forall (parse-type body))]
    [idTE (name) (idT name)]
    [tvTE (name) (tvT name)]))


(define (find-type-id name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'abc "free type name, so no type")]
    [aBind (name ty rest)
           (find-type-id name-to-find rest)]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (if (symbol=? name-to-find name)
               env
               (find-type-id name-to-find rest))]))

(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (get-type name-to-find rest)]))

;equalty : type1 type2 -> bool
; 두 type끼리 같은지 다른지를 확인해 주는 함수 입니다.
; (equalty (numT) (numT)) should produce True.
(define (equalty te1 te2)
  (type-case Type te1
    [numT () (numT? te2)]
    [boolT () (boolT? te2)]
    [arrowT (param arg)
            (type-case Type te2
              [arrowT (param1 arg1)
                      (and (equalty param param1) (equalty arg arg1))]
              [else #f])]
    [polyT (a b)
           (type-case Type te2
             [polyT (c d) (equalty b d)]
             [else #f])]
    [tvT (name)
         (type-case Type te2
           [tvT (name1) #t]
           [else #f])]
    [idT (name)
         (type-case Type te2
           [idT (name1) #t]
           [else #f])]))


; typecheck : Expr environment -> type
(define typecheck1 : (EXPR TypeEnv -> Type)
  (lambda (expr env)
    (type-case EXPR expr
      [num (n) (numT)]
      [add (l r)
           (type-case Type (typecheck1 l env)
             [numT ()
                   (type-case Type (typecheck1 r env)
                     [numT () (numT)]
                     [else (error 'add "no")])]
             [else (error 'add "no")])]
      [bool (l) (boolT)]
      [sub (l r)
           (type-case Type (typecheck1 l env)
             [numT ()
                   (type-case Type (typecheck1 r env)
                     [numT () (numT)]
                     [else (error 'sub "no")])]
             [else (error 'sub "no")])]
      [equ (l r)
           (type-case Type (typecheck1 l env)
             [numT ()
                   (type-case Type (typecheck1 r env)
                     [numT () (boolT)]
                     [else (error 'equ "no")])]
             [else (error 'equ "no")])]
      [id (name) (get-type name env)]
      [fun (name te body)
           (local [(define param-type (parse-type te))]
             (begin
               ;(type-case Type param-type
                ; [tvT (name) (mtEnv)]
                 ;[polyT (param name) (mtEnv)]
                 ;[else (validtype param-type env)])
               ;(validtype param-type env)
               (arrowT param-type
                       (typecheck1 body (aBind name param-type env)))))]
      [app (fn arg)
           (type-case Type (typecheck1 fn env)
             [arrowT (param-type result-type)
                     (if (equalty param-type (typecheck1 arg env))
                         result-type
                         (error 'app "no"))]
             [else (error 'fn "no")])]
      
      [ifthenelse (test-expr then-expr else-expr)
           (type-case Type (typecheck1 test-expr env)
             [boolT () (local [(define test-ty (typecheck1 then-expr env))]
                        (if (equalty test-ty (typecheck1 else-expr env))
                            test-ty
                            (error 'else-expr (to-string test-ty))))]
             [else (error 'test-expr "no")])]
      
      [rec (name ty rhs-expr body-expr)
        (local [(define rhs-ty (parse-type ty))
                (define new-env (aBind name rhs-ty env))]
          (begin
            (validtype rhs-ty env)
            (if (equal? rhs-ty (typecheck1 rhs-expr new-env))
                (typecheck1 body-expr new-env)
                (error 'rhs-expr "no"))))]
      [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
        (local [(define var1-ty (parse-type var1-te))
                (define var2-ty (parse-type var2-te))
                (define new-env (tBind type-name
                                       var1-name var1-ty
                                       var2-name var2-ty env))]
          (begin
            (validtype var1-ty new-env)
            (validtype var2-ty new-env)
            (typecheck1 body-expr
                       (aBind var1-name
                              (arrowT var1-ty
                                      (idT type-name))
                              (aBind var2-name
                                     (arrowT var2-ty
                                             (idT type-name))
                                     new-env)))))]
      [cases (type-name dispatch-expr var1-name var1-id var1-rhs
                        var2-name var2-id var2-rhs)
        (local [(define bind (find-type-id type-name env))]
          (if (and (equal? var1-name (tBind-var1-name bind))
                   (equal? var2-name (tBind-var2-name bind)))
              (type-case Type (typecheck1 dispatch-expr env)
                [idT (name)
                     (if (equal? name type-name)
                         (local [(define rhs1-ty
                                   (typecheck1 var1-rhs
                                              (aBind var1-id (tBind-var1-type bind) env)))
                                 (define rhs2-ty
                                   (typecheck1 var2-rhs
                                              (aBind var2-id (tBind-var2-type bind) env)))]
                           (if (equal? rhs1-ty rhs2-ty)
                               rhs1-ty
                               (error 'var2-rhs "no")))
                         (error 'dispatch-expr "no"))]
                [else (error 'dispatch-expr "no")])
              (error 'expr "no")))]
      [tfun (name expr)
            ;(type-case Type (polyT name (typecheck1 expr env))
            ;  [polyT (param arg)
            ;         (type-case Type arg
            ;           [arrowT (a b)
            ;                   (if (and (equalty param a) (equalty param b))
            ;                     (polyT name (typecheck1 expr env))
            ;                     (error 'zz "free"))]
            ;           [else (numT)])]
            ;  [else (error 'a "fun")])]
           (begin
             ;(validtype (typecheck1 expr env) (aBind name (tvT name) env))
              (polyT name (typecheck1 expr env)))]
      [tapp (body te)
            (local [(define te1 (parse-type te))
                    (define bodytype (typecheck1 body env))]
              (type-case Type bodytype
                [polyT (forall body)
                       (local [(define new-env (aBind forall te1 env))]
                         (type-case Type body
                           [arrowT (param arg)
                                   (arrowT (change-polyt param new-env)
                                           (change-polyt arg new-env))]
                           [polyT (a1 a2)
                                  (if (symbol=? a1 forall)
                                      (polyT a1 a2)
                                      (polyT a1 (change-polyt a2 new-env)))]
                           [else (error 'tapp "no")]))]
                [else (error 'tapp "no")]))])))
;contains? : tvT list -> bool
; tvT 가 list에 있는 지 없는 지를 검사합니다.
; list에 없으면 free입니다.
(define (include? forall lst)
  (cond ((empty? lst) #f)
        ((symbol=? forall (first lst)) #t)
        (else (include? forall (rest lst)))))

; validornot : list forall env list -> environment
; valid 인지 아닌지를 검사.
(define (validornot rest forall env lst)
  (type-case Type rest
    [arrowT (a b) (begin (validornot a forall env lst)
                         (validornot b forall env lst))]
    [tvT (id)
         (if (include? id lst)
             env
             (error 'validornot "free"))]
    [polyT (a rest) (validornot rest a env (append (list a) lst))]
    [else (mtEnv)]))

;typecheck : expr environment -> TYPE
; 마지막에 값을 내기 전에 free 의 경우를 checking합니다.
(define (typecheck expr env)
  (local [(define checking (typecheck1 expr env))]
    (type-case Type checking
      [polyT (forall rest) (begin (validornot rest forall env (list forall)) checking)]
      [arrowT (from to) (cond ((polyT? from) (begin (validornot (polyT-body from) (polyT-forall from) env (list (polyT-forall from))) checking))
                              ((polyT? to) (begin (validornot (polyT-body to) (polyT-forall to) env (list (polyT-forall to))) checking))
                              (else checking))]
      [else checking])))
;change-polyt : type environment -> type
; tapp에서 arrowT의 parameter 와 body 부분의 type에 alpha가 나왔을 경우를 해결해줍니다.
(define (change-polyt te env)
  (type-case Type te
    [tvT (name)
         (get-type name env)]
    [arrowT (param arg)
            (arrowT (change-polyt param env)
                    (change-polyt arg env))]
    [else te]))

;;;;;MY own test;;;;;;;
(test/exn (typecheck (tapp (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))) (numTE)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'beta (fun 'x (tvTE 'beta) (tfun 'beta (fun 'y (tvTE 'beta) (add (id 'x) (id 'y)))))) (mtEnv)) "no")

(test/exn (typecheck (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv)) "free")

(test (typecheck (tfun 'beta (tfun 'alpha (num 5))) (mtEnv))
      (polyT 'beta (polyT 'alpha (numT))))

(test (typecheck (tfun 'beta (fun 'x (tvTE 'beta) (id 'x))) (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))
(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

;;;;;;test;;;;;;;;;;;
(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))
 
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))
 
(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
 
(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha)))
                                         (polyT 'alpha (polyT 'beta (tvT 'alpha)))))))

(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv)) (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv)) (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

(test/exn (typecheck (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'beta))) (id 'x)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (id 'f) (numTE)) (aBind 'f (arrowT (numT) (numT)) (mtEnv))) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (numTE)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (tfun 'beta (fun 'y (tvTE 'beta) (add (id 'x) (id 'y)))))) (mtEnv)) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))

(test (interp (app (fun 'x (numTE)
                        (app (fun 'f (arrowTE (numTE) (numTE))
                                  (add (app (id 'f) (num 1))
                                       (app (fun 'x (numTE)
                                                 (app (id 'f)
                                                      (num 2)))
                                            (num 3))))
                             (fun 'y (numTE)
                                  (add (id 'x) (id 'y)))))
                   (num 0))
              (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (polyT 'alpha (tvT 'alpha))) (mtEnv)))
      (polyT 'alpha (tvT 'alpha)))
      
(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (numTE))
              (mtSub))
      (closureV 'x (id 'x) (mtSub)))
      
(test (typecheck
       (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
             (polyTE 'beta (arrowTE (tvTE 'beta) (tvTE 'beta))))
       (mtEnv))
      (arrowT (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))
              (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))))
              
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (interp (tfun 'alpha (tfun 'beta (num 3))) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
      
(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))  (mtEnv)) (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (equ (num 8) (num 8))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (interp (app
               (tapp (ifthenelse (bool true)
                                 (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                                 (tfun 'beta (fun 'x (tvTE 'beta) (id 'x))))
                     (numTE)) (num 30)) (mtSub))
      (numV 30))
      
(test (interp
       (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                 (app (tapp (id 'x) (numTE)) (num 10)))
        (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))) (mtSub)) (numV 10))
        
(test (typecheck
       (tfun 'alpha
             (fun 'alpha (arrowTE (numTE) (numTE))
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (polyT 'alpha (arrowT (arrowT (numT) (numT)) (arrowT (tvT 'alpha) (tvT 'alpha)))))
      
(test (typecheck
       (fun 'alpha (arrowTE (numTE) (numTE))
            (tfun 'alpha
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (arrowT (arrowT (numT) (numT)) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtSub)) (closureV 'x (num 5) (mtSub)))

(test (interp (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (typecheck (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtEnv)) (arrowT (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtEnv)) (arrowT (numT) (numT)))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'beta)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'alpha (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'alpha)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))
(test (typecheck (ifthenelse (equ (num 8) (num 10))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (fun 'y (tvTE 'beta) (id 'y)))))
                             (tfun 'beta (tfun 'alpha (fun 'x (tvTE 'beta) (fun 'y (tvTE 'alpha) (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (arrowT (tvT 'beta) (tvT 'beta))))))

(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (arrowTE (numTE) (numTE)))
          (mtEnv)) (arrowT (arrowT (numT) (numT)) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'alpha
                                                                                        (fun 'alpha (tvTE 'alpha)
                                                                                             (id 'alpha)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))


(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (typecheck (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (num 42)) (id 'f)) (aBind 'f (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))) (mtEnv))) (numT))

;;; tests on noah 234th article
(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv))
      (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

;;; tests on noah 236th article
(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv))
      (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtEnv)) (numT))
(test (interp (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtSub)) (numV 10))