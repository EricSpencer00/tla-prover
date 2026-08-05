---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

BoundedSeq(T) == UNION { [1 .. n -> T] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt
vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Next ==
  \/ \E x \in Values :
       /\ pos = Len(seq) + 1
       /\ cand' = x
       /\ UNCHANGED <<seq, pos, cnt>>
  \/ \E k \in 1 .. Len(seq) :
       /\ pos = k
       /\ cand' = IF cnt = 0 \/ seq[k] # cand THEN seq[k] ELSE cand
       /\ cnt' = IF cnt = 0 \/ seq[k] # cand THEN 1 ELSE cnt + 1
       /\ pos' = k + 1
       /\ UNCHANGED seq
  \/ \E x \in Values :
       /\ pos = Len(seq) + 1
       /\ seq' = seq \o <<x>>
       /\ UNCHANGED <<pos, cand, cnt>>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Correct ==
  (cnt > 0 /\ \A k \in 1 .. Len(seq) : seq[k] = cand) => cand = Values

Inv ==
  (cnt > 0 /\ \A k \in 1 .. pos - 1 : seq[k] = cand) => cand = Values

ScanComplete == pos = Len(seq) + 1

====