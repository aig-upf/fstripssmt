;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; A simple grid problem, STRIPS encoding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (domain simple-grid)
    (:requirements :strips)
    (:predicates (at ?x) (adjacent ?x ?y))

    (:action move
        :parameters (?from ?to)
        :precondition
            (and (at ?from) (adjacent ?from ?to))
        :effect
           (and (not (at ?from)) (at ?to))
    )
)
