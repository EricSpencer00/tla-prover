---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1 .. N

MsgType == {"p1", "p2"}

\* Set of all possible messages
Msg == {
        [type |-> t,
         sender |-> s,
         val |-> v,
         est |-> e] :
            t \in MsgType,
            s \in Proc,
            v \in Values \cup {Bottom},
            e \in Values \cup {Bottom}
       }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          prop,             \* proposed value of each process
          view,             \* N x N matrix of observed values
          est,              \* estimated value after phase 1
          dec,              \* decision value
          crashed,          \* set of crashed processes
          sent,             \* set of all messages that have been sent
          recv              \* messages received by each process

vars == << pc, prop, view, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of values that a process i has observed (excluding Bottom)
ObservedVals(i) == { v \in Values : \E j \in Proc : view[i][j] = v }

\* Maximum (respectively minimum) value among a non‑empty set of values.
\* If the set is empty we return Bottom.
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

MinVal(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : x <= y

\* Number of distinct senders from which i has received a message of type t
RecvSenders(i, t) ==
    { s \in Proc :
        \E m \in recv[i] :
            /\ m["type"] = t
            /\ m["sender"] = s }

\* Count of messages of type p2 with a given estimated value v received by i
EstCount(i, v) ==
    Cardinality(
        { m \in recv[i] :
            /\ m["type"] = "p2"
            /\ m["est"] = v })

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "b1"]                     \* broadcast phase‑1
    /\ prop \in [Proc -> Values]                     \* arbitrary proposals
    /\ view = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ est = [i \in Proc |-> Bottom]
    /\ dec = [i \in Proc |-> Bottom]
    /\ crashed = {}                                   \* no crashes yet
    /\ sent = {}                                      \* no messages sent
    /\ recv = [i \in Proc |-> {}]                     \* nothing received

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(i) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ pc[i] = "b1"
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ sent' = sent \cup {
            [type |-> "p1",
             sender |-> i,
             val |-> prop[i],
             est |-> Bottom]
        }
    /\ UNCHANGED << prop, view, est, dec, crashed, recv >>

Receive1(i, m) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ pc[i] = "w1"
    /\ m \in sent
    /\ m["type"] = "p1"
    /\ m["sender"] \notin RecvSenders(i, "p1")
    /\ pc' = pc
    /\ view' = [view EXCEPT ![i][m["sender"]] = m["val"]]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << prop, est, dec, crashed, sent >>

Ready1(i) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ pc[i] = "w1"
    /\ Cardinality(RecvSenders(i, "p1")) >= N - T
    /\ pc' = [pc EXCEPT ![i] = "b2"]
    /\ est' = [est EXCEPT ![i] = MaxVal(ObservedVals(i))]
    /\ UNCHANGED << prop, view, dec, crashed, sent, recv >>

Broadcast2(i) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ pc[i] = "b2"
    /\ pc' = [pc EXCEPT ![i] = "w2"]
    /\ sent' = sent \cup {
            [type |-> "p2",
             sender |-> i,
             val |-> prop[i],
             est |-> est[i]]
        }
    /\ UNCHANGED << prop, view, est, dec, crashed, recv >>

Receive2(i, m) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ pc[i] = "w2"
    /\ m \in sent
    /\ m["type"] = "p2"
    /\ m["sender"] \notin RecvSenders(i, "p2")
    /\ pc' = pc
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << prop, view, est, dec, crashed, sent >>

DecideFromEst(i) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ pc[i] = "w2"
    /\ \E v \in Values : EstCount(i, v) >= N - T
    /\ LET v == CHOOSE w \in Values : EstCount(i, w) >= N - T IN
       /\ dec' = [dec EXCEPT ![i] = v]
       /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, crashed, sent, recv >>

MoveToChoose(i) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ pc[i] = "w2"
    /\ \A j \in Proc : \E m \in recv[i] :
            /\ m["type"] = "p2"
            /\ m["sender"] = j
    /\ \A v \in Values : EstCount(i, v) < N - T
    /\ pc' = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED << prop, view, est, dec, crashed, sent, recv >>

ChooseAndDecide(i) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ pc[i] = "choose"
    /\ ObservedVals(i) # {}
    /\ dec' = [dec EXCEPT ![i] = MinVal(ObservedVals(i))]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << prop, view, est, crashed, sent, recv >>

Crash(i) ==
    /\ i \in Proc
    /\ i \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {i}
    /\ pc' = [pc EXCEPT ![i] = "crash"]
    /\ UNCHANGED << prop, view, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in Proc : Broadcast1(i)
    \/ \E i \in Proc : \E m \in sent : Receive1(i, m)
    \/ \E i \in Proc : Ready1(i)
    \/ \E i \in Proc : Broadcast2(i)
    \/ \E i \in Proc : \E m \in sent : Receive2(i, m)
    \/ \E i \in Proc : DecideFromEst(i)
    \/ \E i \in Proc : MoveToChoose(i)
    \/ \E i \in Proc : ChooseAndDecide(i)
    \/ \E i \in Proc : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"b1","w1","b2","w2","choose","done","crash"}]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A i \in Proc :
        /\ dec[i] # Bottom
        => /\ dec[i] \in Values
           /\ \E j \in Proc : prop[j] = dec[i]

Agreement ==
    \A i, j \in Proc :
        /\ dec[i] # Bottom /\ dec[j] # Bottom
        => dec[i] = dec[j]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====