---- MODULE W4Od19m3p1t3 ----
EXTENDS Naturals

Nodes == {"n1", "n2", "n3"}
NONE == "none"
MAXSEQ == 3
MAXTERM == 2

VARIABLES leader, term, committed, nextseq, view

vars == <<leader, term, committed, nextseq, view>>

TypeOK ==
    ( (leader \in Nodes \cup {NONE})
     /\  (term \in 0..MAXTERM)
     /\  (committed \subseteq 1..MAXSEQ)
     /\  (nextseq \in 1..(MAXSEQ + 1))
     /\  (view \in [Nodes -> 0..MAXSEQ]))

Init ==
    ( (leader = NONE)
     /\  (term = 0)
     /\  (committed = {})
     /\  (nextseq = 1)
     /\  (view = [n \in Nodes |-> 0]))

Elect(n) ==
    ( (leader = NONE)
     /\  (leader' = n)
     /\  (term' = IF term < MAXTERM THEN term + 1 ELSE term)
     /\  (UNCHANGED <<committed, nextseq, view>>))

Commit(n) ==
    ( (leader = n)
     /\  (nextseq <= MAXSEQ)
     /\  (committed' = committed \cup {nextseq})
     /\  (view' = [view EXCEPT ![n] = nextseq])
     /\  (nextseq' = nextseq + 1)
     /\  (UNCHANGED <<leader, term>>))

Replicate(n) ==
    ( (leader # NONE)
     /\  (view[n] < view[leader])
     /\  (view' = [view EXCEPT ![n] = view[leader]])
     /\  (UNCHANGED <<leader, term, committed, nextseq>>))

StepDown ==
    ( (leader # NONE)
     /\  (leader' = NONE)
     /\  (UNCHANGED <<term, committed, nextseq, view>>))

Next ==
    ( (\E n \in Nodes : Elect(n))
     \/  (\E n \in Nodes : Commit(n))
     \/  (\E n \in Nodes : Replicate(n))
     \/  (StepDown))

Spec == Init /\ [][Next]_vars

NoLostUpdate ==
    committed = { s \in 1..MAXSEQ : s < nextseq }

====