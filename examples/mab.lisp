
;;;======================================================
;;;   Monkees and Bananas Sample Problem
;;;
;;;     This is an extended version of a
;;;     rather common AI planning problem.
;;;     The point is for the monkee to find
;;;     and eat some bananas.
;;;
;;;     Modified version of CLIPS Version
;;;     6.0 Example to work with MPS.
;;;
;;;     To execute, merely load, reset and run.
;;;======================================================
             
;;;***********
;;;* STRUCTS *
;;;***********

(defstruct monkey 
  (location green-couch
	    :type SYMBOL)
  (on-top-of floor
	     :type SYMBOL)
  (holding nothing
	   :type SYMBOL))

(defstruct thing 
  (name nil
	:type SYMBOL)
  (location nil
	    :type SYMBOL)
  (on-top-of floor
	     :type SYMBOL)
  (weight light ; allowed-symbols: light heavy
	  :type SYMBOL))

(defstruct chest
  (name nil
	:type SYMBOL)
  (contents nil
	    :type SYMBOL)
  (unlocked-by nil
	       :type SYMBOL))

(defstruct goal-is-to
  (action nil ; allowed-symbols: hold unlock eat move on walk-to
	  :type SYMBOL)
  (arguments nil
	     :type SYMBOL))

;;;*************************
;;;* CHEST UNLOCKING RULES *
;;;*************************

(defrule hold-chest-to-put-on-floor
  (goal-is-to (action unlock) (arguments ?chest))
  (thing (name ?chest) (on-top-of ~floor) (weight light))
  (monkey (holding ~?chest))
  (not (goal-is-to (action hold) (arguments ?chest)))
  =>
  (assert (goal-is-to (action hold) (arguments ?chest))))

(defrule put-chest-on-floor
  (goal-is-to (action unlock) (arguments ?chest))
  ?monkey <- (monkey (location ?place) (on-top-of ?on) (holding ?chest))
  ?thing <- (thing (name ?chest))
  =>
  (format t "Monkey throws the ~A off the ~A onto the floor." ?chest ?on)
  (modify ?monkey (holding blank))
  (modify ?thing (location ?place) (on-top-of floor)))

(defrule get-key-to-unlock
  (goal-is-to (action unlock) (arguments ?obj))
  (thing (name ?obj) (on-top-of floor))
  (chest (name ?obj) (unlocked-by ?key))
  (monkey (holding ~?key))
  (not (goal-is-to (action hold) (arguments ?key)))
  =>
  (assert (goal-is-to (action hold) (arguments ?key))))

(defrule move-to-chest-with-key
  (goal-is-to (action unlock) (arguments ?chest))
  (monkey (location ?mplace) (holding ?key))
  (thing (name ?chest) (location ?cplace&~?mplace) (on-top-of floor))
  (chest (name ?chest) (unlocked-by ?key))
  (not (goal-is-to (action walk-to) (arguments ?cplace)))
  =>
  (assert (goal-is-to (action walk-to) (arguments ?cplace))))

(defrule unlock-chest-with-key
  ?goal <- (goal-is-to (action unlock) (arguments ?name))
  ?chest <- (chest (name ?name) (contents ?contents) (unlocked-by ?key))
  (thing (name ?name) (location ?place) (on-top-of ?on))
  (monkey (location ?place) (on-top-of ?on) (holding ?key))
  =>
  (format t "Monkey opens the ~A with the ~A revealing the ~A." ?name ?key ?contents)
  (modify ?chest (contents nothing))
  (assert (thing (name ?contents) (location ?place) (on-top-of ?name)))
  (retract ?goal))

;;;*********************
;;;* HOLD OBJECT RULES * 
;;;*********************

(defrule unlock-chest-to-hold-object
  (goal-is-to (action hold) (arguments ?obj))
  (chest (name ?chest) (contents ?obj))
  (not (goal-is-to (action unlock) (arguments ?chest)))
  =>
  (assert (goal-is-to (action unlock) (arguments ?chest))))

(defrule use-ladder-to-hold
  (goal-is-to (action hold) (arguments ?obj))
  (thing (name ?obj) (location ?place) (on-top-of ceiling) (weight light))
  (not (thing (name ladder) (location ?place)))
  (not (goal-is-to (action move) (arguments ladder ?place)))
  =>
  (assert (goal-is-to (action move) (arguments ladder ?place))))

(defrule climb-ladder-to-hold
  (goal-is-to (action hold) (arguments ?obj))
  (thing (name ?obj) (location ?place) (on-top-of ceiling) (weight light))
  (thing (name ladder) (location ?place) (on-top-of floor))
  (monkey (on-top-of ~ladder))
  (not (goal-is-to (action on) (arguments ladder)))
  =>
  (assert (goal-is-to (action on) (arguments ladder))))

(defrule grab-object-from-ladder
  ?goal <- (goal-is-to (action hold) (arguments ?name))
  ?thing <- (thing (name ?name) (location ?place) 
		   (on-top-of ceiling) (weight light))
  (thing (name ladder) (location ?place))
  ?monkey <- (monkey (location ?place) (on-top-of ladder) (holding blank))
  =>
  (format t "Monkey grabs the ~A." ?name)
  (modify ?thing (location held) (on-top-of held))
  (modify ?monkey (holding ?name))
  (retract ?goal))

(defrule climb-to-hold
  (goal-is-to (action hold) (arguments ?obj))
  (thing (name ?obj) (location ?place) (on-top-of ?on&~ceiling) (weight light))
  (monkey (location ?place) (on-top-of ~?on))
  (not (goal-is-to (action on) (arguments ?on)))
  =>
  (assert (goal-is-to (action on) (arguments ?on))))

(defrule walk-to-hold
  (goal-is-to (action hold) (arguments ?obj))
  (thing (name ?obj) (location ?place) (on-top-of ~ceiling) (weight light))
  (monkey (location ~?place))
  (not (goal-is-to (action walk-to) (arguments ?place)))
  =>
  (assert (goal-is-to (action walk-to) (arguments ?place))))

(defrule drop-to-hold
  (goal-is-to (action hold) (arguments ?obj))
  (thing (name ?obj) (location ?place) (on-top-of ?on) (weight light))
  (monkey (location ?place) (on-top-of ?on) (holding ~blank))
  (not (goal-is-to (action hold) (arguments blank)))
  =>
  (assert (goal-is-to (action hold) (arguments blank))))

(defrule grab-object
  ?goal <- (goal-is-to (action hold) (arguments ?name))
  ?thing <- (thing (name ?name) (location ?place) 
		   (on-top-of ?on) (weight light))
  ?monkey <- (monkey (location ?place) (on-top-of ?on) (holding blank))
  =>
  (format t "Monkey grabs the ~A." ?name)
  (modify ?thing (location held) (on-top-of held))
  (modify ?monkey (holding ?name))
  (retract ?goal))

(defrule drop-object
  ?goal <- (goal-is-to (action hold) (arguments blank))
  ?monkey <- (monkey (location ?place) 
                     (on-top-of ?on) 
                     (holding ?name&~blank))
  ?thing <- (thing (name ?name))
  =>
  (format t "Monkey drops the ~A." ?name)
  (modify ?monkey (holding blank))
  (modify ?thing (location ?place) (on-top-of ?on))
  (retract ?goal))

;;;*********************
;;;* MOVE OBJECT RULES * 
;;;*********************

(defrule unlock-chest-to-move-object
  (goal-is-to (action move) (arguments ?obj ?))
  (chest (name ?chest) (contents ?obj))
  (not (goal-is-to (action unlock) (arguments ?chest)))
  =>
  (assert (goal-is-to (action unlock) (arguments ?chest))))

(defrule hold-object-to-move
  (goal-is-to (action move) (arguments ?obj ?place))
  (thing (name ?obj) (location ~?place) (weight light))
  (monkey (holding ~?obj))
  (not (goal-is-to (action hold) (arguments ?obj)))
  =>
  (assert (goal-is-to (action hold) (arguments ?obj))))

(defrule move-object-to-place
  (goal-is-to (action move) (arguments ?obj ?place))
  (monkey (location ~?place) (holding ?obj))
  (not (goal-is-to (action walk-to) (arguments ?place)))
  =>
  (assert (goal-is-to (action walk-to) (arguments ?place))))

(defrule drop-object-once-moved
  ?goal <- (goal-is-to (action move) (arguments ?name ?place))
  ?monkey <- (monkey (location ?place) (holding ?obj))
  ?thing <- (thing (name ?name) (weight light))
  =>
  (format t "Monkey drops the ~A." ?name)
  (modify ?monkey (holding blank))
  (modify ?thing (location ?place) (on-top-of floor))
  (retract ?goal))

(defrule already-moved-object
  ?goal <- (goal-is-to (action move) (arguments ?obj ?place))
  (thing (name ?obj) (location ?place))
  =>
  (retract ?goal))

;;;***********************
;;;* WALK TO PLACE RULES *
;;;***********************

(defrule already-at-place
  ?goal <- (goal-is-to (action walk-to) (arguments ?place))
  (monkey (location ?place))
  =>
  (retract ?goal))

(defrule get-on-floor-to-walk
  (goal-is-to (action walk-to) (arguments ?place))
  (monkey (location ~?place) (on-top-of ~floor))
  (not (goal-is-to (action on) (arguments floor)))
  =>
  (assert (goal-is-to (action on) (arguments floor))))

(defrule walk-holding-nothing
  ?goal <- (goal-is-to (action walk-to) (arguments ?place))
  ?monkey <- (monkey (location ~?place) (on-top-of floor) (holding blank))
  =>
  (format t "Monkey walks to ~A." ?place)
  (modify ?monkey (location ?place))
  (retract ?goal))

(defrule walk-holding-object
  ?goal <- (goal-is-to (action walk-to) (arguments ?place))
  ?monkey <- (monkey (location ~?place) (on-top-of floor) (holding ?obj&~blank))
  =>
  (format t "Monkey walks to ~A holding the ~A." ?place ?obj)
  (modify ?monkey (location ?place))
  (retract ?goal))

;;;***********************
;;;* GET ON OBJECT RULES * 
;;;***********************

(defrule jump-onto-floor
  ?goal <- (goal-is-to (action on) (arguments floor))
  ?monkey <- (monkey (on-top-of ?on&~floor))
  =>
  (format t "Monkey jumps off the ~A onto the floor." ?on)
  (modify ?monkey (on-top-of floor))
  (retract ?goal))

(defrule walk-to-place-to-climb
  (goal-is-to (action on) (arguments ?obj))
  (thing (name ?obj) (location ?place))
  (monkey (location ~?place))
  (not (goal-is-to (action walk-to) (arguments ?place)))
  =>
  (assert (goal-is-to (action walk-to) (arguments ?place))))

(defrule drop-to-climb
  (goal-is-to (action on) (arguments ?obj))
  (thing (name ?obj) (location ?place))
  (monkey (location ?place) (holding ~blank))
  (not (goal-is-to (action hold) (arguments blank)))
  =>
  (assert (goal-is-to (action hold) (arguments blank))))

(defrule climb-indirectly
  (goal-is-to (action on) (arguments ?obj))
  (thing (name ?obj) (location ?place) (on-top-of ?on))
  (monkey (location ?place) (on-top-of ~?on&~?obj) (holding blank))
  (not (goal-is-to (action on) (arguments ?on)))
  =>
  (assert (goal-is-to (action on) (arguments ?on))))

(defrule climb-directly
  ?goal <- (goal-is-to (action on) (arguments ?obj))
  (thing (name ?obj) (location ?place) (on-top-of ?on))
  ?monkey <- (monkey (location ?place) (on-top-of ?on) (holding blank))
  =>
  (format t "Monkey climbs onto the ~A." ?obj)
  (modify ?monkey (on-top-of ?obj))
  (retract ?goal))

(defrule already-on-object
  ?goal <- (goal-is-to (action on) (arguments ?obj))
  (monkey (on-top-of ?obj))
  =>
  (retract ?goal))

;;;********************
;;;* EAT OBJECT RULES * 
;;;********************

(defrule hold-to-eat
  (goal-is-to (action eat) (arguments ?obj))
  (monkey (holding ~?obj))
  (not (goal-is-to (action hold) (arguments ?obj)))
  =>
  (assert (goal-is-to (action hold) (arguments ?obj))))

(defrule satisfy-hunger
  ?goal <- (goal-is-to (action eat) (arguments ?name))
  ?monkey <- (monkey (holding ?name))
  ?thing <- (thing (name ?name))
  =>
  (format t "Monkey eats the ~A." ?name)
  (modify ?monkey (holding blank))
  (retract ?goal ?thing))
 
;;;**********************
;;;* INITIAL STATE RULE * 
;;;**********************

(defrule startup
  =>
  (assert (monkey (location t5-7) (on-top-of green-couch) (holding blank)))
  (assert (thing (name green-couch) (location t5-7) (weight heavy)))
  (assert (thing (name red-couch) (location t2-2) (weight heavy)))
  (assert (thing (name big-pillow) (location t2-2) (on-top-of red-couch)))
  (assert (thing (name red-chest) (location t2-2) (on-top-of big-pillow)))
  (assert (chest (name red-chest) (contents ladder) (unlocked-by red-key)))
  (assert (thing (name blue-chest) (location t7-7) (on-top-of ceiling)))
  (assert (chest (name blue-chest) (contents bananas) (unlocked-by blue-key)))
  (assert (thing (name blue-couch) (location t8-8) (weight heavy)))
  (assert (thing (name green-chest) (location t8-8) (on-top-of ceiling)))
  (assert (chest (name green-chest) (contents blue-key) (unlocked-by red-key)))
  (assert (thing (name red-key) (location t1-3)))
  (assert (goal-is-to (action eat) (arguments bananas))))
