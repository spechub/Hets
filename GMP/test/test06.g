;;; usage: racer -f test-tbox.racer -q test-queries.racer

(concept-subsumes? 
	(at-most 3 R (or a 
	   (at-most 4 R (or b
		(at-least 5 R (or a b))))))
	(at-most 3 R (or b
		(and a
			(at-least 4 R (or b (not a)))))))

<3>! (a \/ <4>! (b \/ [5] (a\/b)))
<3>! (b \/ a/\ [4](b\/~a))

def: <n>! f = <n-1> f /\ ~<n> f
