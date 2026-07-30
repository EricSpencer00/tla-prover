---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq replaces Seq from Sequences with a finite version so the
\* model stays in the bounded horizon the .cfg expects: only
\* sequences of length up to the bound appear.
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ count \in 0 .. bound

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

Valid(n) == pos <= n + 1

Next ==
  \E n \in 0 .. bound :
    \/ /\ VALID(n) /\ seq' = seq
       /\ (IF pos > n
            THEN pos' = 1
            ELSE pos' = pos + 1)
       /\ (IF pos > n
            THEN cand' = CHOOSE c \in Values : TRUE
            ELSE cand' = cand)
       /\ IF pos > n
            THEN count' = 0
            ELSE IF count = 0
                 THEN cand' = seq[pos] /\ count' = 1
                 ELSE IF seq[pos] = cand
                      THEN count' = count + 1
                      ELSE count' = count - 1
    \/ /\ seq' \in BoundedSeq(Values) /\ UNCHANGED <<pos, cand, count>>

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

Correct ==
  (cardinality({i \in 1 .. Len(seq) : seq[i] = cand}) > Len(seq) \div 2)
    => (cand = seq[Cardinality({i \in 1 .. Len(seq) : seq[i] = cand})])

Inv ==
  /\ count <= Len(seq)
  /\ count >= 0
  /\ cand \in Values

====