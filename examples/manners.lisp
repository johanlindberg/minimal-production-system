;;; The Ms Manners Benchmark

;;; This version is based on the CLIPS version, available at
;;; http://clipsrules.sourceforge.net

(defparameter ?*output* nil) ; Disabled = nil Enabled = t

;;; Structs

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

;;; Guests

(deffacts guests
  #S(guest :name 'n1 :sex 'm :hobby 'h3)
  #S(guest :name 'n1 :sex 'm :hobby 'h2)
  #S(guest :name 'n2 :sex 'm :hobby 'h1)
  #S(guest :name 'n2 :sex 'm :hobby 'h2)
  #S(guest :name 'n2 :sex 'm :hobby 'h3)
  #S(guest :name 'n3 :sex 'f :hobby 'h3)
  #S(guest :name 'n3 :sex 'f :hobby 'h2)
  #S(guest :name 'n4 :sex 'f :hobby 'h1)
  #S(guest :name 'n4 :sex 'f :hobby 'h2)
  #S(guest :name 'n4 :sex 'f :hobby 'h3)
  #S(last_seat :seat 4)
  #S(count :c 1)
  #S(context :state 'start))

;;; Rules

(defrule assign_first_seat
   ?f1 <- (context (state 'start))
   (guest (name ?n))
   ?f3 <- (count (c ?c))
   =>
   (assert-facts #S(seating :seat1 1 :name1 ?n :name2 ?n :seat2 1 :id ?c :pid 0 :path_done 'yes)
                 #S(path :id ?c :name ?n :seat 1))
   (modify-facts (?f3 (c (+ ?c 1))))
   (modify-facts (?f1 (state 'assign_seats))))

(defrule find_seating
   ?f1 <- (context (state 'assign_seats))
   (seating (seat1 ?seat1) (seat2 ?seat2) (name2 ?n2) (id ?id) (pid ?pid) (path_done 'yes))
   (guest (name ?n2) (sex ?s1) (hobby ?h1))
   (guest (name ?g2) (sex ?s2 (not (equal ?s1 ?s2))) (hobby ?h1))
   ?f5 <- (count (c ?c))
   (not (path (id ?id) (name ?g2)))
   (not (chosen (id ?id) (name ?g2) (hobby ?h1)))
   =>
   (assert-facts #S(seating :seat1 ?seat2 :name1 ?n2 :name2 ?g2 :seat2 (+ ?seat2 1) :id ?c :pid ?id :path_done 'no))
   (assert-facts #S(path :id ?c :name ?g2 :seat (+ ?seat2 1)))
   (assert-facts #S(chosen :id ?id :name ?g2 :hobby ?h1))
   (modify-facts (?f5 (c (+ ?c 1))))
   (format ?*output* "seat ~A ~A ~A" ?seat2 ?n2 ?g2)
   (modify-facts (?f1 (state 'make_path))))

(defrule make_path
   (salience 1)
   (context (state 'make_path))
   (seating (id ?id) (pid ?pid) (path_done 'no))
   (path (id ?pid) (name ?n1) (seat ?s))
   (not (path (id ?id) (name ?n1)))
   =>
   (assert-facts #S(path :id ?id :name ?n1 :seat ?s)))

(defrule path_done
   ?f1 <- (context (state 'make_path))
   ?f2 <- (seating (path_done 'no))
   =>
   (modify-facts (?f2 (path_done 'yes)))
   (modify-facts (?f1 (state 'check_done))))

(defrule are_we_done
   ?f1 <- (context (state 'check_done))
   (last_seat (seat ?l_seat))
   (seating (seat2 ?l_seat))
   =>
   (format ?*output* "~%Yes, we are done!!")
   (modify-facts (?f1 (state 'print_results))))

(defrule continue
   ?f1 <- (context (state 'check_done))
   =>
   (modify-facts (?f1 (state 'assign_seats))))

(defrule print_results
   (salience 1)
   (context (state 'print_results))
   (seating (id ?id) (seat2 ?s2))
   (last_seat (seat ?s2))
   ?f4 <- (path (id ?id) (name ?n) (seat ?s))
   =>
   (retract-facts ?f4)
   (format ?*output* "~A ~A" ?n ?s))

(defrule all_done
   (context (state 'print_results))
   =>
   (halt))

(defun halt ()
  (format ?*output* "HALT"))