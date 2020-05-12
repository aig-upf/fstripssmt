(define (problem sample)
  (:domain array-sort-fn)
  (:objects )

  (:init
	(= (val 1) 3)
	(= (val 2) 8)
	(= (val 3) 2)
	(= (val 4) 5)
  )

  (:goal (and
  	(<= (val 1) (val 2))
  	(<= (val 2) (val 3))
  	(<= (val 3) (val 4))
  ))

  (:bounds (value - int[0..10]) (position - int[1..4]))
)
