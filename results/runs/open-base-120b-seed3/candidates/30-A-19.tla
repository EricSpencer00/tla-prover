---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ------------------------------------------------------------
\* Types
\* ------------------------------------------------------------
Proc   == 1..N
Value  == Values

Message ==
    [type  : {"p1","p2"},
     sender: Proc,
     value : Value,
     est   : Value]  \* for phase‑2 messages the field  est  is used,
                     \* for phase‑1 messages its value is ignored

\* ------------------------------------------------------------
\* State variables
\* ------------------------------------------------------------
VARIABLES
    loc,   \* [i \in Proc -> {"b1","w1","b2","w2","done","crashed","choosing"}]
    view,  \* [i \in Proc -> [j \in Proc -> Value]]      (local view matrix)
    prop,  \* [i \in Proc -> Value]                     (initial proposal)
    est,   \* [i \in Proc -> Value]                     (estimated value after phase‑1)
    dec,   \* [i \in Proc -> Value]                     (decision value)
    sent,  \* SUBSET Message                           (messages that have been sent)
    rcv    \* [i \in Proc -> SUBSET Message]           (messages received by each process)

\* ------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------
Locs == {"b1","w1","b2","w2","done","crashed","choosing"}

MaxInView(i) ==
    LET vals == { view[i][j] : j \in Proc } \* a finite set of numbers
    IN  IF vals = {Bottom} THEN Bottom
        ELSE Max(vals \ {Bottom})

ReceivedSenders(i) == { m.sender : m \in rcv[i] }

ReceivedEstCount(i, v) == Cardinality({ m \in rcv[i] : m.type = "p2" /\ m.est = v })

Phase1Enough(i) == Cardinality(ReceivedSenders(i)) >= N - T
Phase2Enough(i, v) == ReceivedEstCount(i, v) >= N - T
Phase2All(i) == Cardinality(ReceivedSenders(i)) = N

\* ------------------------------------------------------------
\* Initial state
\* ------------------------------------------------------------
Init ==
    /\ loc = [i \in Proc |-> "b1"]
    /\ view = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Value]               \* each process proposes an arbitrary value
    /\ est = [i \in Proc |-> Bottom]
    /\ dec = [i \in Proc |-> Bottom]
    /\ sent = {}
    /\ rcv = [i \in Proc |-> {}]

\* ------------------------------------------------------------
\* Actions
\* ------------------------------------------------------------

Broadcast1(i) ==
    /\ loc[i] = "b1"
    /\ sent' = sent \cup { [type |-> "p1", sender |-> i,
                           value |-> prop[i], est |-> Bottom] }
    /\ loc' = [loc EXCEPT ![i] = "w1"]
    /\ UNCHANGED << view, prop, est, dec, rcv >>

Receive1(i, m) ==
    /\ loc[i] = "w1"
    /\ m \in sent
    /\ m.type = "p1"
    /\ m.sender \notin ReceivedSenders(i)
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ rcv' = [rcv EXCEPT ![i] = rcv[i] \cup {m}]
    /\ UNCHANGED << loc, prop, est, dec, sent >>

Phase1Complete(i) ==
    /\ loc[i] = "w1"
    /\ Phase1Enough(i)
    /\ est' = [est EXCEPT ![i] = MaxInView(i)]
    /\ loc' = [loc EXCEPT ![i] = "b2"]
    /\ UNCHANGED << view, prop, dec, sent, rcv >>

Broadcast2(i) ==
    /\ loc[i] = "b2"
    /\ sent' = sent \cup { [type |-> "p2", sender |-> i,
                           value |-> prop[i], est |-> est[i]] }
    /\ loc' = [loc EXCEPT ![i] = "w2"]
    /\ UNCHANGED << view, prop, est, dec, rcv >>

Receive2(i, m) ==
    /\ loc[i] = "w2"
    /\ m \in sent
    /\ m.type = "p2"
    /\ m.sender \notin ReceivedSenders(i)
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ rcv' = [rcv EXCEPT ![i] = rcv[i] \cup {m}]
    /\ UNCHANGED << loc, prop, est, dec, sent >>

Phase2Decide(i) ==
    /\ loc[i] = "w2"
    /\ \E v \in Value :
          Phase2Enough(i, v)
    /\ LET v == CHOOSE w \in Value : Phase2Enough(i, w) IN
       /\ dec' = [dec EXCEPT ![i] = v]
       /\ loc' = [loc EXCEPT ![i] = "done"]
    /\ UNCHANGED << view, prop, est, sent, rcv >>

Phase2Choose(i) ==
    /\ loc[i] = "w2"
    /\ Phase2All(i)
    /\ \A v \in Value : ~Phase2Enough(i, v)   \* no value reached the N‑T threshold
    /\ (* deterministic choice: the smallest value appearing in the view *)
       LET candidates == { view[i][j] : j \in Proc /\ view[i][j] # Bottom } IN
       /\ candidates # {}                      \* there is at least one candidate
       /\ let v == Min(candidates) in
          /\ dec' = [dec EXCEPT ![i] = v]
          /\ loc' = [loc EXCEPT ![i] = "done"]
    /\ UNCHANGED << view, prop, est, sent, rcv >>

Crash(i) ==
    /\ loc[i] # "crashed"
    /\ Cardinality({ j \in Proc : loc[j] = "crashed" }) < F
    /\ loc' = [loc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED << view, prop, est, dec, sent, rcv >>

\* ------------------------------------------------------------
\* Next-state relation
\* ------------------------------------------------------------
Next ==
    \/ \E i \in Proc : Broadcast1(i)
    \/ \E i \in Proc, m \in Message : Receive1(i, m)
    \/ \E i \in Proc : Phase1Complete(i)
    \/ \E i \in Proc : Broadcast2(i)
    \/ \E i \in Proc, m \in Message : Receive2(i, m)
    \/ \E i \in Proc : Phase2Decide(i)
    \/ \E i \in Proc : Phase2Choose(i)
    \/ \E i \in Proc : Crash(i)

\* ------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------
Spec == Init /\ [][Next]_<< loc, view, prop, est, dec, sent, rcv >>

\* ------------------------------------------------------------
\* Type correctness invariant
\* ------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> Value]]
    /\ prop \in [Proc -> Value]
    /\ est \in [Proc -> Value]
    /\ dec \in [Proc -> Value]
    /\ sent \subseteq Message
    /\ rcv \in [Proc -> SUBSET Message]

\* ------------------------------------------------------------
\* Safety properties
\* ------------------------------------------------------------
Validity ==
    \A i \in Proc :
        dec[i] # Bottom =>
            /\ dec[i] \in Values
            /\ \E j \in Proc : prop[j] = dec[i]

Agreement ==
    \A i, j \in Proc :
        /\ dec[i] # Bottom
        /\ dec[j] # Bottom
        => dec[i] = dec[j]

====