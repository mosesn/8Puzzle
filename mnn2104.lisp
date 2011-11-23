;Results from the three heuristics:
;Manhattan Displaced BetterManhattan
;1046          17926    1046
;3106          27668    1789
;3141          31388    3034
;3191          26642    3191
;376           6673     801
;As expected, since BetterManhattan is not very different from Manhattan
;there is usually no difference between it and Manhattan.
;Also as expected, Displaced is always the worst. However, something that
;was somewhat unexpected was that in one case, BetterManhattan is
;two times worse than Manhattan!  The special case that BetterManhattan
;guards against must have been the precise case that led to a fast solution.


;;;; The Queue datatype

;;; We can remove elements form the front of a queue.  We can add elements in
;;; three ways: to the front (LIFO, or stack), to the back (FIFO, or simple queue), or by priority (priority queue).
;;; This is done with the following enqueing functions specified when we make the queue, which make use of the
;;; following implementations of the elements:
;;;   ENQUEUE-LIFO - elements are a list
;;;   ENQUEUE-FIFO   - elements are a list
;;;   ENQUEUE-PRIORITY - elements are a heap, implemented as an array
;;; The best element in the queue is always in position 0.
;;; For priority queues, we can specify a key function that should return the priority value of an element.
;;; For FIFO queues, we maintain a pointer to the last element for efficient enqueuing.

(defstruct q
  (enqueue #'enqueue-FIFO)
  (key #'identity)
  (last nil)
  (elements nil))

;;;; Operations on Queues

(defun q-emptyp (q)
  "Returns T if queue is empty."
  (= (length (q-elements q)) 0))       ; (length x) works for both lists and arrays with fill-pointers

(defun q-front (q)
  "Returns the element at the front of the queue."
  (elt (q-elements q) 0))              ; (elt x n) works for both lists and arrays

(defun q-remove (q)
  "Removes the element from the front of the queue and returns it."
  (if (listp (q-elements q))
      (pop (q-elements q))             ; (pop x) alters x by removing the car, then returns the item removed
    (heap-pop (q-elements q) (q-key q))))

(defun q-insert (q items)
  "Inserts the items into the queue, according to the queue's enqueuing function."
  (funcall (q-enqueue q) q items)
  q)

;;;; The Three Enqueing Functions

(defun enqueue-LIFO (q items)
  "Adds a list of items to the front of the queue."
  (setf (q-elements q) (nconc items (q-elements q)))  ; (nconc x y) is destructive version of (append x y)
  items
  )

(defun enqueue-FIFO (q items)
  "Adds a list of items to the end of the queue."
  (if (q-emptyp q) 
      (setf (q-elements q) items)
    (setf (cdr (q-last q)) items))
  (setf (q-last q) (last items))
  items
  )

(defun enqueue-priority (q items)
  "Inserts the items by priority determined by the queue's key function."
  ;; If first insert, create the heap
  (when (null (q-elements q))
    (setf (q-elements q) (make-heap)))
  ;; Now insert the items
  (mapc (lambda (item)
	  (heap-insert (q-elements q) item (q-key q)))
	items)
  )

;;;; The Heap Implementation of Priority Queues

;;; The idea is to store a heap in an array so that the heap property is
;;; maintained for all elements: heap[Parent(i)] <= heap[i].  Note that we
;;; start at index 0, not 1, and that we put the lowest value at the top of
;;; the heap, not the highest value.

(defun heap-val (heap i key) (funcall key (elt heap i)))
(defun heap-parent (i) (floor (1- i) 2))
(defun heap-left (i) (+ 1 i i))
(defun heap-right (i) (+ 2 i i))
(defun heap-leafp (heap i) (> i (1- (floor (length heap) 2))))

(defun heapify (heap i key)
  "Assume that the children of i are heaps, but that heap[i] may be 
  larger than its children.  If it is, moves heap[i] down where it belongs."
  (unless (heap-leafp heap i)
    (let ((l (heap-left i))
	  (r (heap-right i)))
      (let ((smaller-child (if (and (< r (length heap))
				    (< (heap-val heap r key) (heap-val heap l key)))
			       r l)))
	(when (> (heap-val heap i key) (heap-val heap smaller-child key))
	  (rotatef (elt heap i) (elt heap smaller-child))    ; (rotatef x y) swaps values of x and y
	  (heapify heap smaller-child key))))
    ))

(defun heap-pop (heap key)
  "Pops the best (lowest valued) item off the heap."
  (let ((min (elt heap 0)))
    (setf (elt heap 0) (elt heap (1- (length heap))))
    (decf (fill-pointer heap))        ; (decf x) decrements x
    (heapify heap 0 key)
    min))

(defun heap-insert (heap item key)
  "Puts an item into a heap."
  (vector-push-extend nil heap)       ; (vector-push-extend value array) adds the value to the next
                                      ; available position in the array, incrementing the fill-pointer
                                      ; and increasing the size of the array if necessary.
  (setf (elt heap (heap-find-pos heap (1- (length heap)) (funcall key item) key)) 
	item)

  )

(defun heap-find-pos (heap i val key)
  "Bubbles up from i to find position for val, moving items down in the process."
  (cond ((or (zerop i) (< (heap-val heap (heap-parent i) key) val))
	 i)
	(t
	 (setf (elt heap i) (elt heap (heap-parent i)))
	 (heap-find-pos heap (heap-parent i) val key))
	))

(defun make-heap (&optional (size 100))
  (make-array size :fill-pointer 0 :adjustable t))


;(defun general-search (initial-state 
;                       successor 
;                       goalp 
;                       &key (enqueue #'enqueue-LIFO)
;			     (key #'identity))
;  (let ((fringe (make-q :enqueue enqueue :key key)))
;    (q-insert fringe (list (make-node :state initial-state)))
;    (tree-search fringe successor goalp)))

(defun tree-search (fringe successor goalp)
  (unless (q-emptyp fringe)
    (let ((node (q-remove fringe)))
      (if (funcall goalp (node-state node))
        (action-sequence node)
        (tree-search (q-insert fringe (expand successor node))
                     successor goalp))
      )))

(defun expand (successor node)
  (let ((triples (funcall successor (node-state node))))
    (mapcar (lambda (action-state-cost)
	      (let ((action (car action-state-cost))
		    (state (cadr action-state-cost))
		    (cost (caddr action-state-cost)))
		(make-node :state state 
			   :parent node
			   :action action 
			   :path-cost (+ (node-path-cost node) cost)
			   :depth (1+ (node-depth node)))
		))
	    triples)
    ))

(defun action-sequence (node &optional (actions nil))
  (if (node-parent node)
    (action-sequence (node-parent node) (cons (node-action node) actions))
    actions
    ))



(defstruct node 
  (state nil)
  (parent nil)
  (action nil)
  (path-cost 0)
  (depth 0))

(defvar *expanded-nodes*)

(defun general-search (initial-state successor goalp
		       &key (samep #'eql)
		            (enqueue #'enqueue-LIFO) 
		            (key #'identity))
  (setf *expanded-nodes* 0)
  (let ((fringe (make-q :enqueue enqueue :key key)))
    (q-insert fringe (list (make-node :state initial-state)))
    (values 
     (graph-search fringe nil successor goalp samep)
     *expanded-nodes*)
    ))

(defun graph-search (fringe closed successor goalp samep)
  (unless (q-emptyp fringe)
    (let ((node (q-remove fringe)))
      (cond ((funcall goalp (node-state node)) 
	     (action-sequence node))
            ((member (node-state node) closed 
		     :test samep :key #'node-state)
	     (graph-search fringe closed successor goalp samep))
            (t 
	     (let ((successors (expand successor node)))
	       (setf *expanded-nodes* 
		     (+ *expanded-nodes* (length successors)))
	       (graph-search (q-insert fringe successors)
			     (cons node closed)
			     successor goalp samep)))
            ))
    ))

;inits a list given a list of lists, each 3 deep
;each number should be distinct, [1,9]
(defun init (x)
  (make-array `(3 3)
	    :initial-contents
	      x))

;more recursion
(defun new-list (arr x y)
  (cond
    ((= y 2) (cons (aref arr x y) nil))
    (t (cons (aref arr x y) (new-list arr x (+ y 1))))))

;creates a list from an array
;useful for making a new array
(defun arr-to-list (arr x y)
  (cond
    ((= x 2) (cons (new-list arr x y) nil))
    (t (cons (new-list arr x y) (arr-to-list arr (+ x 1) y)))))

;writes the boilerplate for you
(defun arr-list (arr)
  (arr-to-list arr 0 0))

;copies an array into a new array, only works for this specific version
(defun copy-3-list (arr)
  (init (arr-list arr)))

;same state test
(defun same (x y)
  (equalp x y))

;sums the similar values in the column of the array
(defun misplaced-recurs (arr compare x y)
  (cond
    ((= y 2)
     (cond
       ((= 9 (aref arr x y)) 0)
       ((= (aref arr x y) (aref compare x y)) 0)
       (t 1)))
    (t
     (+
      (cond
	((= 9 (aref arr x y)) 0)
	((= (aref arr x y) (aref compare x y)) 0)
	(t 1)) (misplaced-recurs arr compare x (+ y 1)))))
  )

;sums the similar values from columns in the array
(defun list-recurs (arr compare x y)
  (cond
    ((= x 2)
     (misplaced-recurs arr compare x y))
    (t
     (+ (misplaced-recurs arr compare x y) (list-recurs arr compare (+ x 1) y))))
  )

;absolute value difference
(defun abs-diff (x y)
  (cond
    ((= x y) 0)
    ((< x y) (- y x))
    (t (- x y)))
  )

;manhattan distance heuristic
(defun manhattan (val x y)
  (cond
    ((= val 1) (+ (abs-diff 0 x) (abs-diff 0 y)))
    ((= val 2) (+ (abs-diff 0 x) (abs-diff 1 y)))
    ((= val 3) (+ (abs-diff 0 x) (abs-diff 2 y)))
    ((= val 4) (+ (abs-diff 1 x) (abs-diff 0 y)))
    ((= val 5) (+ (abs-diff 1 x) (abs-diff 1 y)))
    ((= val 6) (+ (abs-diff 1 x) (abs-diff 2 y)))
    ((= val 7) (+ (abs-diff 2 x) (abs-diff 0 y)))
    ((= val 8) (+ (abs-diff 2 x) (abs-diff 1 y)))
    ((= val 9) 0)
    (t -1))
  )

;fetches the manhattan distance for cols
(defun man-col (arr x y)
  (cond
    ((= x 2) (manhattan (aref arr x y) x y))
    (t (+ (manhattan (aref arr x y) x y) (man-col arr (+ x 1) y))))
  )

;fetches the manhattan distance for rows
(defun man-row (arr x y)
  (cond
    ((= y 2) (man-col arr x y))
    (t (+ (man-col arr x y) (man-row arr x (+ y 1)))))
  )

;fetches the manhattan distance of this array
(defun manhattan-heuristic (arr)
  (man-row arr 0 0)
  )

;if 0,0 and 0,1 are reversed, add 1 to the manhattan.
;otherwise do nothing. in nearly all cases this is manhattan
;but in a few it is not, so it dominates manhattan.
;this is still consistent because manhattan distance doesn't take
;into account movement that must be done for tiles to move around each other
;for tiles that are in the correct positions except reversed and next
;each other, they cannot swap spaces in two moves, but instead must make
;several moves (at least 2) to get to the correct spot for each of them.
;Figured this out with help from Cecilia Schudel and:
;http://web.mit.edu/6.034/wwwbob/EightPuzzle.pdf
(defun tiny-heuristic (arr)
  (cond
    ((and (= 2 (aref arr 0 0)) (= 1 (aref arr 0 1))) 1)
    (t 0))
  )

;fetches the manhattan distance of this array plus a little
;proof that it dominates:
(defun manhattan-plus (arr)
  (+ (manhattan-heuristic arr) (tiny-heuristic arr))
  )

;fetches the manhattan distance of this array
(defun manhattan-plus-node-state (node)
  (manhattan-plus (node-state node))
  )

;count the number of incorrect tiles
(defun misplaced (arr)
  (list-recurs arr (init `((1 2 3) (4 5 6) (7 8 9))) 0 0)
  )

;fetches the manhattan distance of this array
(defun astar-man (node)
  (+ (manhattan-heuristic (node-state node)) (node-path-cost node))
  )

(defun astar-disp (node)
  (+ (misplaced (node-state node)) (node-path-cost node))
  )

(defun astar-plus (node)
  (+ (manhattan-plus (node-state node)) (node-path-cost node))
  )

;note: 9 is the empty square
(defun complete (x)
  (same x (init `((1 2 3) (4 5 6) (7 8 9)))))

;constructs the list of 4 surrounding elements
(defun successor-list (posx posy)
  (list
   (cons posx (- posy 1))
   (cons posx (+ posy 1))
   (cons (- posx 1) posy)
   (cons (+ posx 1) posy)))

;validates a pair of coordinates
(defun invalidp (pair)
  (cond
    ((< (car pair) 0) t)
    ((< (cdr pair) 0) t)
    ((> (car pair) 2) t)
    ((> (cdr pair) 2) t)
    (t nil)))

;swaps two positions in a 2d array
(defun swap (arr emptyx emptyy fullx fully)
  (let ((temp (aref arr emptyx emptyy)))
    (setf (aref arr emptyx emptyy) (aref arr fullx fully))
    (setf (aref arr fullx fully) temp))
  (list
   (cond
     ((> emptyx fullx) "DOWN")
     ((< emptyx fullx) "UP")
     ((> emptyy fully) "RIGHT")
     ((< emptyy fully) "LEFT")
     (t ""))
   arr
   1
   ))

;generators successor from a cons pair
(defun gen-successor (arr posx posy pair)
  (swap (copy-3-list arr) posx posy (car pair) (cdr pair))
  )

;recursively handles the valid elements of the list
(defun proc-successors (arr posx posy lst)
  (cond
    ((null lst) nil)
    (t (cons (gen-successor arr posx posy (car lst))
	     (proc-successors arr posx posy (cdr lst))))))

;cleans the list of successors
(defun clean-successors (lst)
  (remove-if `invalidp lst))

;fetches the list of possible next states
(defun gen-successors (arr posx posy)
  (proc-successors arr posx posy
		   (clean-successors (successor-list posx posy)))
  )

;fetches the list of possible next states
(defun gen-successors-safe (arr)
  (cond
    ((= 9 (aref arr 0 0)) (gen-successors arr 0 0))
    ((= 9 (aref arr 0 1)) (gen-successors arr 0 1))
    ((= 9 (aref arr 0 2)) (gen-successors arr 0 2))
    ((= 9 (aref arr 1 0)) (gen-successors arr 1 0))
    ((= 9 (aref arr 1 1)) (gen-successors arr 1 1))
    ((= 9 (aref arr 1 2)) (gen-successors arr 1 2))
    ((= 9 (aref arr 2 0)) (gen-successors arr 2 0))
    ((= 9 (aref arr 2 1)) (gen-successors arr 2 1))
    (t (gen-successors arr 2 2)))
  )

(defun contains-list (lst val)
  (cond
    ((null lst) nil)
    ((= val (car lst)) t)
    (t (contains-list (cdr lst) val))))

(defun try-add (lst val)
  (cond
    ((contains-list lst val) lst)
    (t (cons val lst)))
  )

(defun random-gen (x lst)
  (cond
    ((= x (list-length lst)) lst)
    (t (random-gen x (try-add lst (+ 1 (random x))))))
  )

(defun random-generate (x)
  (random-gen x nil)
  )

(defun inversions (val lst)
  (cond
    ((null lst) 0)
    ((= val 9) 0)
    ((> val (car lst)) (+ 1 (inversions val (cdr lst))))
    (t (inversions val (cdr lst))))
  )

(defun unsolvable-recurs (lst)
  (cond
    ((null lst) 0)
    (t (+ (inversions (car lst) (cdr lst)) (unsolvable-recurs (cdr lst)))))
  )

;uses solvability solution from
;http://www.cs.bham.ac.uk/~mdr/teaching/modules04/java2/TilesSolvability.html
(defun solvable (lst)
  (evenp (unsolvable-recurs lst))
  )

(defun init-square (lst)
   (cond
     ((null lst) nil)
     (t (cons (list (first lst) (second lst) (third lst)) (init-square (cdddr lst))))))

(defun make-random-eight (x)
  (let ((lst (random-generate x)))
    (cond
      ((solvable lst) (init (init-square lst)))
      (t (make-random-eight x))))
  )

(defun astar-search-man (arr)
  (general-search
   arr
   'gen-successors-safe
   'complete
   :samep 'same
   :enqueue #'enqueue-priority
   :key 'astar-man))

(defun astar-search-disp (arr)
  (general-search
   arr
   'gen-successors-safe
   'complete
   :samep 'same
   :enqueue #'enqueue-priority
   :key 'astar-disp))

(defun astar-search-plus (arr)
  (general-search
   arr
   'gen-successors-safe
   'complete
   :samep 'same
   :enqueue #'enqueue-priority
   :key 'astar-plus))



;checks that the goal has been found
(complete  (make-array `(3 3)
	    :initial-contents
	    `((1 2 3)
	      (4 5 6)
	      (7 8 9))))

;makes a new problem instance
(init `((1 2 3) (4 5 6) (7 8 9)))

;checks whether two states are the same
(same
 (init `((1 2 3) (4 5 6) (7 8 9)))
 (init `((1 2 3) (4 5 6) (7 8 9))))

(swap
 (init `((1 2 3) (4 5 6) (7 8 9)))
 0 0 0 1)

(successor-list 1 1)

(gen-successor
 (init `((1 2 3) (4 5 6) (7 8 9)))
 0 0 (cons 0 1))

(invalidp (cons 0 0))
(invalidp (cons -1 0))
(invalidp (cons 0 3))
(invalidp (cons 2 2))

(clean-successors
	(list (cons 0 0) (cons -1 0) (cons 0 3) (cons 2 2)))

(arr-to-list (init `((1 2 3) (4 5 6) (7 8 9))) 0 0)
(arr-list (init `((1 2 3) (4 5 6) (7 8 9))))

(copy-3-list (init `((1 2 3) (4 5 6) (7 8 9))))

(gen-successors
 (init `((1 2 3) (4 5 6) (7 8 9)))
 1 1)

(gen-successors
 (init `((1 2 3) (4 5 6) (7 8 9)))
 0 1)

(misplaced (init `((1 2 3) (4 6 5) (9 7 8))))
(manhattan-heuristic (init `((1 2 3) (4 6 5) (7 9 8))))
(manhattan-plus (init `((2 1 3) (4 6 5) (7 9 8))))

(general-search
 (init `((2 3 6) (1 9 5) (4 7 8)))
 'gen-successors-safe
 'complete
 :samep 'same
 :enqueue #'enqueue-priority
 :key 'manhattan-plus-node-state)

(general-search
 (init `((2 3 6) (1 9 5) (4 7 8)))
 'gen-successors-safe
 'complete
 :samep 'same
 :enqueue #'enqueue-priority
 :key 'astar-plus)

(astar-search-man
 (init `((2 3 6) (1 9 5) (4 7 8))))

(random-generate 9)
(random-generate 9)
(random-generate 9)
(random-generate 9)
(random-generate 9)
(random-generate 9)
(solvable (random-generate 9))

(let ((x (make-random-eight 9)))
      (astar-search-man x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-disp x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-plus x)
      (princ *expanded-nodes*)
      (princ "    "))

(let ((x (make-random-eight 9)))
      (astar-search-man x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-disp x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-plus x)
      (princ *expanded-nodes*)
      (princ "    "))

(let ((x (make-random-eight 9)))
      (astar-search-man x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-disp x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-plus x)
      (princ *expanded-nodes*)
      (princ "    "))

(let ((x (make-random-eight 9)))
      (astar-search-man x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-disp x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-plus x)
      (princ *expanded-nodes*)
      (princ "    "))

(let ((x (make-random-eight 9)))
      (astar-search-man x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-disp x)
      (princ *expanded-nodes*)
      (princ "    ")
      (astar-search-plus x)
      (princ *expanded-nodes*)
      (princ "    "))

