;;; The Ms Manners Benchmark

;;; This version is based on the CLIPS version, available at
;;; http://clipsrules.sourceforge.net

(defparameter ?*output* t) ; Disabled = nil Enabled = t

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
   
(defstruct cnt
   c)

;;; Rules

(defrule assign_first_seat
   (?f1 (context (state 'start)))
   (guest (name ?n))
   (?f3 (cnt (c ?c)))
   =>
   (assert-facts (make-seating :seat1 1 :name1 ?n :name2 ?n :seat2 1
			       :id ?c :pid 0 :path_done 'yes)
                 (make-path :id ?c :name ?n :seat 1))
   (modify-facts #'(lambda (fact)
		     (setf (cnt-c fact) (+ ?c 1)))
		 ?f3)
   (format ?*output* "~&seat 1 ~A ~A 1 ~A 0 1" ?n ?n ?c)
   (modify-facts #'(lambda (fact)
		     (setf (context-state fact) 'assign_seats))
		 ?f1))

(defrule find_seating
   (?f1 (context (state 'assign_seats)))
   (seating (seat1 ?seat1) (seat2 ?seat2) (name2 ?n2) (id ?id)
	    (pid ?pid) (path_done 'yes))
   (guest (name ?n2) (sex ?s1) (hobby ?h1))
   (guest (name ?g2) (sex ?s2 (not (equal ?s1 ?s2))) (hobby ?h1))
   (?f5 (cnt (c ?c)))
   (not (path (id ?id) (name ?g2)))
   (not (chosen (id ?id) (name ?g2) (hobby ?h1)))
   =>
   (assert-facts (make-seating :seat1 ?seat2 :name1 ?n2 :name2 ?g2
			       :seat2 (+ ?seat2 1) :id ?c :pid ?id
			       :path_done 'no))
   (assert-facts (make-path :id ?c :name ?g2 :seat (+ ?seat2 1)))
   (assert-facts (make-chosen :id ?id :name ?g2 :hobby ?h1))
   (modify-fact #'(lambda (fact)
		    (setf (cnt-c fact) (+ ?c 1)))
		?f5)
   (format ?*output* "~&seat ~A ~A ~A" ?seat2 ?n2 ?g2)
   (modify-facts #'(lambda (fact)
		    (setf (context-state fact) 'make_path))
		?f1))

(defrule make_path
   (salience 1)

   (context (state 'make_path))
   (seating (id ?id) (pid ?pid) (path_done 'no))
   (path (id ?pid) (name ?n1) (seat ?s))
   (not (path (id ?id) (name ?n1)))
   =>
   (assert-facts (make-path :id ?id :name ?n1 :seat ?s)))

(defrule path_done
   (?f1 (context (state 'make_path)))
   (?f2 (seating (path_done 'no)))
   =>
   (modify-facts #'(lambda (fact)
		     (setf (seating-path_done fact) 'yes))
		 ?f2)
   (modify-facts #'(lambda (fact)
		     (setf (context-state fact) 'check_done))
		 ?f1))

(defrule are_we_done
   (?f1 (context (state 'check_done)))
   (last_seat (seat ?l_seat))
   (seating (seat2 ?l_seat))
   =>
   (format ?*output* "~&Yes, we are done!!")
   (modify-facts #'(lambda (fact)
		     (setf (context-state fact) 'print_results))
		 ?f1))

(defrule continue
   (?f1 (context (state 'check_done)))
   =>
   (modify-facts #'(lambda (fact)
		     (setf (context-state fact) 'assign_seats))
		 ?f1))

(defrule print_results
   (salience 1)
   
   (context (state 'print_results))
   (seating (id ?id) (seat2 ?s2))
   (last_seat (seat ?s2))
   (?f4 (path (id ?id) (name ?n) (seat ?s)))
   =>
   (retract-facts ?f4)
   (format ?*output* "~&~A ~A" ?n ?s))

(defrule all_done
   (context (state 'print_results))
   =>
   (halt))
