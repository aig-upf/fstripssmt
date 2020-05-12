;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The array-sort problem: Sort an array by only using swap operations.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;

(define (domain array-sort-fn)
    (:requirements :typing)
    (:types
        position - int
        value    - int
    )

    (:functions
        (val ?i - position) - value ;; The value of the given position of the vector
    )

    ;; Swap the values of the two given array positions
    (:action swap
        :parameters (?i ?j - position)
        :precondition (and (< ?i ?j))
        :effect       (and
            (assign (val ?i) (val ?j))
            (assign (val ?j) (val ?i))
        )
    )
)
