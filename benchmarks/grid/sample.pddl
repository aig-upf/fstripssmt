(define (problem 4cells)
(:domain simple-grid)
(:objects
    pos0-0 pos0-1 pos1-0 pos1-1
)
(:init
    (adjacent pos0-0 pos1-0)
    (adjacent pos0-0 pos0-1)
    (adjacent pos0-1 pos1-1)
    (adjacent pos0-1 pos0-0)
    (adjacent pos1-0 pos1-1)
    (adjacent pos1-0 pos0-0)
    (adjacent pos1-1 pos0-1)
    (adjacent pos1-1 pos1-0)

    (at pos0-0)
)

(:goal
    (at pos1-1)
)
)
