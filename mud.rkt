#lang racket
(require racket/stxparam (for-syntax racket/syntax))

;;anaphoric macros

(define-syntax-parameter @
  (λ (stx) (error "@ must be used within an anaphoric macro")))

(define-syntax-rule (aif i t e)
  (let ([x i])
    (if x (syntax-parameterize ([@ (make-rename-transformer #'x)]) t)
        e)))

;feeds forward the previous result with "@" or short circuits, effectively making this
;Haskell's maybe monad given expressions that produce #f | value
;skip is used to avoid auto-binding @ for that expression, e.g.
;(aand 3       (odd? @))  => #t
;(aand 3 (skip (odd? @))) => 3
(define-syntax aand
  (syntax-rules (skip)
    [(_) #t]
    [(_ x) x]
    [(_ x1 (skip x2) xs ...) (aand x1 (and x2 @) xs ...)]
    [(_ x1 x2 xs ...) (aif x1 (aand x2 xs ...) #f)]))

;; utility functions

;map & apply -- "f" interprets data in table form
(define (mapp f xs)
  (map (λ (x) (apply f x)) xs))

;maybe assoc -- returns snd of pair if found
;a * [a,b] * opt: (a * a -> ?) -> #f | b
(define (massoc x t [f equal?])
  (aand (assoc x t f) (cdr @)))

;;primary data types

;symbol * real[0,1]
(struct item (id %))

;[item] * gold = int
(struct room (is g) #:transparent)

;[item] * gold
(struct player (is g) #:transparent)

;player * coords = [int] * level = hash[coord,room]
(struct state (p c l)
  #:methods gen:custom-write
  [(define (write-proc s port m)
     (fprintf port "~a~n~a~n~a" (state-c s) (state-p s) (find-room (state-c s) (state-l s))))])

;; constants

(define MAX-ROOM-GOLD 10)
(define ITEMS (mapp item '([sledge 0.7] [ladder 0.1])))

;; coordinate functions

;string -> maybe coord = #f | coord
(define dir->coord
  (let ([t '([("east" "e") 1 0 0]
             [("north" "n") 0 0 -1]
             [("west" "w") -1 0 0]
             [("south" "s") 0 0 1]
             [("up" "u") 0 1 0]
             [("down" "d") 0 -1 0])])
    (λ (s) (massoc s t member))))

;string * state -> maybe coord
(define (neighbor s st)
  (aand (dir->coord s) (map + @ (state-c st))))

;; item functions

;-> [item]
(define (rand-items)
  (append-map (λ (i) (if (< (random) (item-% i))
                         (list (item-id i))
                         '()))
              ITEMS))

;; room/level functions

;coord * level -> room
(define (find-room c l)
  (hash-ref l c))

;coord * level * room -> level
(define (set-room c l r)
  (hash-set l c r))

;coord * level -> maybe coord
(define (room-at? c l)
  (and (hash-has-key? l c) c))

;coord * level -> level
(define (rand-room c l)
  (set-room c l (room (rand-items) (random (add1 MAX-ROOM-GOLD)))))

;;legal move macros

;depending on whether the adjacent room exists, do one of two things
;string * state * (code => state) * (code => state) -> state
(define-syntax-rule (aif-neighbor dir s i t e)
  (aand (neighbor dir s) (skip i)
        (if (room-at? @ (state-l s)) t e)))

(define-syntax-rule (awhen-neighbor dir s i t ...)
  (aif-neighbor dir s i (begin t ...) s))

(define-syntax-rule (aunless-neighbor dir s i e ...)
  (aif-neighbor dir s i s (begin e ...)))

;; user command type

;int * statef = (state * rest ... -> state)
(struct action (n-args f))

;associates user commands with actions
;assoc[[string] , action]
(define actions '())

;[string] * action -> effect: mutate action table
(define-syntax-rule (add-action! (s ...) a)
  (set! actions (cons (cons (s ...) a) actions)))

;string -> maybe action
(define (get-action s)
  (massoc s actions member))

;string * rest ... -> state
(define (run-action s . args)
  (aand (get-action s)
        (skip (= (length args) (action-n-args @)))
        (apply (action-f @) args)))

;[string] * [id] * code -> effect: mutate action table
(define-syntax (defaction stx)
  (syntax-case stx ()
    [(_ (str ...) (param ...) body ...)
     (with-syntax ([p (length (syntax->list #'(param ...)))])
       #'(add-action! (list str ...) (action p (λ (param ...) body ...))))]))

;; the commands and state functions

;symbol * state -> ?
(define (has-item? i s)
  (member i (player-is (state-p s))))

;(player * room -> player) * (player * room -> room) -> statef = (state -> state)
(define ((take/drop fp fr) s)
  (match-let* ([(state p c l) s]
               [r (find-room c l)])
    (state (fp p r) c (set-room c l (fr p r)))))

;should be performed automatically upon entering a room
;statef
(define take-gold
  (take/drop (λ (p r) (player (player-is p)
                              (+ (player-g p) (room-g r))))
             (λ (p r) (room (room-is r) 0))))

;used to drop the ladder when moving up
;symbol -> statef
(define (drop i)
  (take/drop (λ (p r) (player (remove i (player-is p)) (player-g p)))
             (λ (p r) (room (cons i (room-is r)) (room-g r)))))

(defaction ("take" "t") (s)
  ((take/drop (λ (p r) (player (append (room-is r) (player-is p))
                               (player-g p)))
              (λ (p r) (room '() (room-g r))))
   s))

(defaction ("drop") (s)
  ((take/drop (λ (p r) (player '() (player-g p)))
              (λ (p r) (room (append (room-is r) (player-is p))
                             (room-g r))))
   s))

;attack is in effect "create a room"
(defaction ("attack" "a") (s dir)
  (aunless-neighbor dir s (has-item? 'sledge s)
    (state (state-p s) (state-c s) (rand-room @ (state-l s)))))

;can move when the room exists and either the direction isn't up or player has a ladder
(defaction ("move" "m") (s dir)
  (awhen-neighbor dir s (or (not (equal? @ '(0 1 0)))
                            (has-item? 'ladder s))
    (let ([s ((drop 'ladder) s)])
      (take-gold (state (state-p s) @ (state-l s))))))

;starting state configuration
(define state0
  (let* ([c0 '(0 0 0)]
         [cg '(1 1 5)]
         [l0 (hash c0 (room '(sledge) 5)
                   cg (room '(princess) 100))]
         [p0 (player '() 0)])
    (take-gold (state p0 c0 l0))))

;-> side-effects: text IO
(define (run)
  (define (prompt) (display "> "))
  (let main-loop ([s state0])
    (displayln s)
    (prompt)
    (match (string-split (read-line))
      ['() (main-loop s)]
      [(list cmd args ...) (unless (ormap (λ (s) (string=? s cmd)) '("quit" "q"))
                             (main-loop (or (apply run-action cmd s args) s)))])))