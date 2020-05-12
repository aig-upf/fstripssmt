;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; A simple grid problem, FSTRIPS / numeric encoding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (domain simple-grid-fn)
    (:requirements :strips)
    (:predicates (at ?x) (adjacent ?x ?y))

    (:functions
        (x) - number
        (y) - number
        (max_x) - number
        (max_y) - number
    )

    (:action move_r :parameters ()
        :precondition
            (and (< (x) (max_x)))
        :effect
           (and (increase (x)))
    )

    (:action move_l :parameters ()
        :precondition
            (and (> (x) 0))
        :effect
           (and (decrease (x)))
    )


    (:action move_u :parameters ()
        :precondition
            (and (< (y) (max_y)))
        :effect
           (and (increase (y)))
    )

    (:action move_d :parameters ()
        :precondition
            (and (> (y) 0))
        :effect
           (and (decrease (y)))
    )
)
