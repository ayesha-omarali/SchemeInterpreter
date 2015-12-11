; Name Ayesha Omarali
; Login CS61a-fb

;;;;;;;;;;;;
;; Lab 14 ;;
;;;;;;;;;;;;

; Question 2
; Base Case
(fact (interleave () ?lst2 ()))

; YOUR CODE HERE
(fact (interleave (?first . ?rest) ?lst (?first . ?rest2))
	(interleave ?lst ?rest ?rest2))

(query (interleave (1 2 3 4) (5 6 7 8) ?lst))
; expect Success! ; lst: (1 5 2 6 3 7 4 8)

(query (interleave (1) (2 3 4 5 6 7 8 9) ?lst))
; expect Success! ; lst: (1 2)

(query (interleave (1 3 5 7 9) ?evens (1 2 3 4 5 6 7 8 9)))

; expect Success! ; evens: (2 4 6 8)


; Question 3
(fact (last-element (?x) ?x))
(fact (last-element (?a . ?b) ?x)
(last-element ?b ?x))

(query (last-element (a b c) c))
; expect Success!

(query (last-element (3) ?x))
; expect Success! ; x: 3

(query (last-element (1 2 3) ?x))
; expect Success! ; x: 3

(query (last-element (2 ?x) 3))
; expect Success! ; x: 3


; Question 4
(fact (firsts ((?x . ?y)) ?x))

(fact (firsts ((?x . ?rest) . ?y) (?x . ?rest2))
	(firsts ?y ?rest2))


(query (firsts ((1 2 3 4) (2 3 4 5) (1 2 3 4) (1 2 3 2)) ?x))
; expect Success! ; x: (1 2 1 1)

(query (firsts ((2 3 4) (3 4 5) (2 3 4) (2 3 2)) ?y))
; expect Success! ; y: (2 3 2 2)


; Question 5
(fact (rests (?first . ?rest) (?rest)))

(fact (rests ((?first1 . ?rest) . ?rest2) (?rest . ?rest3))
	(rests ?rest2 ?rest3))


(query (rests ((1 2 3 4) (2 3 4 5) (1 2 3 4) (1 2 3 2)) ?x))
; expect Success! ; x: ((2 3 4) (3 4 5) (2 3 4) (2 3 2))

(query (rests ((2 3 4) (3 4 5) (2 3 4) (2 3 2)) ?y))
; expect Success! ; y: ((3 4) (4 5) (3 4) (3 2))
