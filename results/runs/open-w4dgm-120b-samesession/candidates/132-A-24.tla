---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt
vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in [1..bound -> Values]
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Bump(p) == IF p < bound THEN p + 1 ELSE p

Correct == \A v \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => (cand = v)

Inv == \A i \in 1..(pos - 1) :
         /\ (cnt = 0 => cand \in Values)
         /\ (i < pos => (cnt > 0 => seq[i] = cand))

Init ==
  /\ seq \in [1..bound -> Values]
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Next ==
  \/ \E x \in Values :
       /\ pos <= bound
       /\ IF cnt = 0 THEN cand' = x ELSE cand' = cand
       /\ IF cnt = 0 THEN cnt' = 1 ELSE cnt' = cnt
       /\ pos' = Bump(pos)
       /\ UNCHANGED seq
  \/ \E x \in Values :
       /\ pos <= bound
       /\ IF cnt > 0 /\ seq[pos] = cand THEN cnt' = cnt + 1 /\ cand' = cand
          ELSE IF cnt > 0 /\ seq[pos] # cand THEN cnt' = cnt - 1 /\ cand' = cand
          ELSE cnt' = 1 /\ cand' = seq[pos]
       /\ pos' = Bump(pos)
       /\ UNCHANGED seq
  \/ \E x \in Values :
       /\ pos > bound
       /\ seq' = [seq EXCEPT ![pos] = x]
       /\ UNCHANGED <<pos, cand, cnt>>

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Next)

BoundedSeq == [1..bound -> Values]
====