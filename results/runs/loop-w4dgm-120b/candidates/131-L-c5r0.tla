---- MODULE MajorityProof ----
EXTENDS MajorityMain, FiniteSets

CONSTANTS Value

\* The invariant Inv is the same one from the main specification: it ties
\* the candidate to the count of the element it currently represents.
Inv == candidates \subseteq (({candidates} \cup Value) \times (1..SeqLen)) /\ \
       \A c \in candidates : \A k \in 1..SeqLen : c[2] <= k => c[1] \in
           {Seq[j] : j \in positions(c[1], k)}

TypeOK == candidates \subseteq (Value \X (1..SeqLen))

Spec == Init /\ [][Next]_vars

Init == Init /\ candidates = {}

Next == Next \/ (\E v \in Value : candidates' = candidates \cup
    {<<v, Cardinality({j \in 1..SeqLen : Seq[j] = v})>>})

TypeOKStep == TypeOK

TypeOKInv == TypeOK /\ [][TypeOKStep]_vars

\* The core correctness property: any value appearing in a strict majority
\* of the full sequence must equal the candidate's value.
Correct == candidates # {} =>
    (\E c \in candidates : Cardinality({j \in 1..SeqLen : Seq[j] = c[1]})
        > SeqLen \div 2) => (\E c \in candidates : c[1] = (CHOOSE x \in Value :
            Cardinality({j \in 1..SeqLen : Seq[j] = x}) > SeqLen \div 2))

====