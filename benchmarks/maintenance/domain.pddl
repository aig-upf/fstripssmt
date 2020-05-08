; There are mechanics who on any day may work at one
; of several cities where the airplane maintenance
; company has facilities. There are airplanes each of
; which has to be maintained during the given time period.
; The airplanes are guaranteed to visit some of the cities
; on given days. The problem is to schedule the presence
; of the mechanics so that each plane will get maintenance.

(define (domain maintenance-fn)
 (:requirements :typing)

 (:types plane day airport)

 (:predicates
    (at ?p - plane ?d - day ?c - airport)
 )

  (:functions
    (loc ?d - day) - airport
 )

 (:action dummy :parameters ()
  :precondition (and  )
  :effect (and))
)