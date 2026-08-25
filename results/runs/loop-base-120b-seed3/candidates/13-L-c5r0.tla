---- MODULE MCBakery ----
EXTENDS Naturals, TLC

CONSTANT N
CONSTANT MaxNat

\* Finite replacement for the infinite set of natural numbers
NatOverride == 0..MaxNat

ProcessSet == 1..N

VARIABLES choosing, number

\* ---------- Helper definitions ----------
Max(S) == 
    IF S = {} THEN 0
    ELSE LET m == CHOOSE x \in S : \A y \in S : x >= y IN m

PairLess(p, q) == (p[1] < q[1]) \/ (p[1] = q[1] /\ p[2] < q[2])

InCS(i) == 
    /\ number[i] # 0
    /\ \A j \in ProcessSet : (j # i) => 
          (number[j] = 0 \/ PairLess(<<number[i], i>>, <<number[j], j>>))

\* ---------- Invariants ----------
MutualExclusion == 
    \A i, j \in ProcessSet : i # j => ~ (InCS(i) /\ InCS(j))

TypeOK == 
    /\ choosing \in [ProcessSet -> BOOLEAN]
    /\ number   \in [ProcessSet -> NatOverride]

Inv == TypeOK /\ MutualExclusion

\* ---------- Initial state ----------
Init == 
    /\ choosing = [i \in ProcessSet |-> FALSE]
    /\ number   = [i \in ProcessSet |-> 0]

\* ---------- Actions ----------
ChooseNumber(i) == 
    /\ choosing[i] = FALSE
    /\ number[i] = 0
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED number

AssignNumber(i) == 
    /\ choosing[i] = TRUE
    /\ number' = [number EXCEPT ![i] = 1 + Max({ number[j] : j \in ProcessSet /\ number[j] # 0 })]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED << >>

Wait(i) == 
    /\ number[i] # 0
    /\ \A j \in ProcessSet : (j # i) => 
          (number[j] = 0 \/ PairLess(<<number[i], i>>, <<number[j], j>>))
    /\ UNCHANGED << choosing, number >>

Exit(i) == 
    /\ number[i] # 0
    /\ number' = [number EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

Next == 
    \/ \E i \in ProcessSet : ChooseNumber(i)
    \/ \E i \in ProcessSet : AssignNumber(i)
    \/ \E i \in ProcessSet : Wait(i)
    \/ \E i \in ProcessSet : Exit(i)

\* ---------- Specification ----------
ISpec == Init /\ [][Next]_<<choosing, number>>

====