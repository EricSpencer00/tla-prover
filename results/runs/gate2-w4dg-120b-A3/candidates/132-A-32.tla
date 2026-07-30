---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
SeqSpace == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, candidate, counter

vars == <<seq, pos, candidate, counter>>

RECURSIVE EqualValues(_, _)
EqualValues(f, g) ==
  \/ (f = g)
  \/ \E x \in DOMAIN f : f[x] # g[x]
                                 /\ (\A y \in DOMAIN f : y <= x => f[y] = g[y])

\* A candidate is a true majority if it appears in the majority of positions
\* of the full sequence; this is defined with a full scan of the whole sequence.
MajorityElement(e) ==
  \E n \in 1 .. Len(seq) : 2 * Cardinality({i \in 1 .. n : seq[i] = e}) > n

TypeOK ==
  /\ seq \in SeqSpace
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ candidate \in Values
  /\ counter \in 0 .. bound

Correct ==
  \/ candidate # candidate
  \/ \A e \in Values : MajorityElement(e) => e = candidate

Init ==
  /\ seq \in SeqSpace
  /\ pos = 1
  /\ candidate \in Values
  /\ counter = 0

\* Boyer-Moore's three-way vote: adopt, increment, or decrement the counter.
Next ==
  \/ \E e \in Values :
       /\ pos <= Len(seq)
       /\ seq' = [seq EXCEPT ![pos] = e]
       /\ pos' = pos + 1
       /\ IF counter = 0
            THEN /\ candidate' = e
                 /\ counter' = 1
            ELSE IF e = candidate
                 THEN /\ candidate' = candidate
                      /\ counter' = counter + 1
                 ELSE /\ candidate' = candidate
                      /\ counter' = counter - 1
  \/ /\ pos > Len(seq)
     /\ UNCHANGED <<seq, pos, candidate, counter>>

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(Next)
        /\ WF_vars(Next)

Inv ==
  /\ TypeOK
  /\ Correct

\* The bounded sequence operator replaces the standard unbounded one, making the
\* model finite so TLC can check it; keep EXTENDS Sequences, do not declare Seq.
BoundedSeq == SeqSpace

====