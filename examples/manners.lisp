;;; The Manners Benchmark

;;; This version is based on the CLIPS version, available at
;;; http://clipsrules.sourceforge.net

;;; #############
;;; Defparameters
;;; #############

(defparameter ?*output* nil) ; Disabled = nil Enabled = t

;;; ##########
;;; Defstructs
;;; ##########

(defstruct guest 
   name
   sex
   hobby)
   
(defstruct last_seat 
   seat)
   
(defstruct seating 
   seat1
   name1 
   name2
   seat2
   id
   pid
   path_done)
   
(defstruct context
   state)

(defstruct path 
   id
   name
   seat)
   
(defstruct chosen 
   id
   name
   hobby)
   
(defstruct count 
   c)

;;; ########
;;; Defrules
;;; ########

;;; *****************
;;; assign_first_seat
;;; *****************

(defrule assign_first_seat
   ?f1 <- (context (state start))
   (guest (name ?n))
   ?f3 <- (count (c ?c))
   =>
   (assert (seating (seat1 1) (name1 ?n) (name2 ?n) (seat2 1) (id ?c) (pid 0) (path_done yes)))
   (assert (path (id ?c) (name ?n) (seat 1)))
   (modify ?f3 (c (+ ?c 1)))
   (format ?*output* "seat 1 ~A ~A 1 ~A 0 1" ?n ?n ?c)
   (modify ?f1 (state assign_seats)))

;;; ************
;;; find_seating
;;; ************

(defrule find_seating
   ?f1 <- (context (state assign_seats))
   (seating (seat1 ?seat1) (seat2 ?seat2) (name2 ?n2) (id ?id) (pid ?pid) (path_done yes))
   (guest (name ?n2) (sex ?s1) (hobby ?h1))
   (guest (name ?g2) (sex ~?s1) (hobby ?h1))
   ?f5 <- (count (c ?c))
   (not (path (id ?id) (name ?g2)))
   (not (chosen (id ?id) (name ?g2) (hobby ?h1)))
   =>
   (assert (seating (seat1 ?seat2) (name1 ?n2) (name2 ?g2) (seat2 (+ ?seat2 1)) (id ?c) (pid ?id) (path_done no)))
   (assert (path (id ?c) (name ?g2) (seat (+ ?seat2 1))))
   (assert (chosen (id ?id) (name ?g2) (hobby ?h1)))
   (modify ?f5 (c (+ ?c 1)))
   (format ?*output* "seat ~A ~A ~A" ?seat2 ?n2 ?g2)
   (modify ?f1 (state make_path)))

;;; *********
;;; make_path
;;; *********

(defrule make_path
   (context (state make_path))
   (seating (id ?id) (pid ?pid) (path_done no))
   (path (id ?pid) (name ?n1) (seat ?s))
   (not (path (id ?id) (name ?n1)))
   =>
   (assert (path (id ?id) (name ?n1) (seat ?s))))

;;; *********
;;; path_done
;;; *********

(defrule path_done
   ?f1 <- (context (state make_path))
   ?f2 <- (seating (path_done no))
   =>
   (modify ?f2 (path_done yes))
   (modify ?f1 (state check_done)))

;;; ***********
;;; are_we_done
;;; ***********

(defrule are_we_done
   ?f1 <- (context (state check_done))
   (last_seat (seat ?l_seat))
   (seating (seat2 ?l_seat))
   =>
   (format ?*output* "~%Yes, we are done!!")
   (modify ?f1 (state print_results)))

;;; ********
;;; continue
;;; ********

(defrule continue
   ?f1 <- (context (state check_done))
   =>
   (modify ?f1 (state assign_seats)))

;;; *************
;;; print_results
;;; *************

(defrule print_results
   (context (state print_results))
   (seating (id ?id) (seat2 ?s2))
   (last_seat (seat ?s2))
   ?f4 <- (path (id ?id) (name ?n) (seat ?s))
   =>
   (retract ?f4)
   (format ?*output* "~A ~A" ?n ?s))

;;; ********
;;; all_done
;;; ********

(defrule all_done
   (context (state print_results))
   =>
   (halt))
