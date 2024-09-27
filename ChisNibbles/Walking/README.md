# Walking

Once upon a time, someone asked the following question.

> There are some people (maybe infinitely many) standing in the Euclidean plane, and each has a destination. Their starting points are distinct, and same for their destinations. Is it always possible for the people to simultaneously walk to their destinations without colliding?
> 
> (This just means we want continuous paths which don't intersect each other at any given time; people have radius 0, and there are no speed or smoothness constraints or anything.)

Turns out the answer is yes, and one way to prove it is using a certain homotopy related to the Hilbert curve.
To be precise we can build a homotopy (I'll call it the "Hilbert homotopy") between the unit interval('s standard embedding) and a space-filling curve on the unit square, with the property that, at every $t < 1$, the curve it traces is injective. One construction is to homotope through the intermediate stages of the recursive construction of the Hilbert curve one at a time, and that's what I implement in [``HilbertCurve.lean``](HilbertCurve.lean).
<details>
<summary>Details</summary> <!-- explicitly adding <summary>Details</summary>?? who even does that? -->

1. Without loss of generality we can consider the unit square instead of the plane.
2. Now use the Hilbert homotopy to move all starts and goals into the unit interval, by picking some preimage of each point in the square.
3. Suppose each person is at $(a, 0)$ and wants to get to $(b, 0)$. Have them all walk $(a, 0) \to (a, b) \to (0, b) \to (b, 0)$, taking one second on each arrow.

This argument is due to some CMU students, apparently.

</details>

There is a much more easily formalised proof using transfinite induction, but I wanted to see what the Hilbert homotopy was like to play with. (Turns out, kind of annoying! Now we know.)

The most interesting thing that came out of this from my perspective is the proof strategy for ``aux.homotopy_injective`` (injectivity of the Hilbert homotopy at all $t < 1$), using the theorem ``linearHomotopy_timewise_injective_iff``. This is to show something that you would ordinarily prove by just, drawing a diagram and looking at it. I generally find the puzzle of formalising things like that pretty cool. There's a more "straightforward" proof by a massive dumb case analysis, but at the time I didn't know enough to write the automation for that, so I did it by hand and it sucked.