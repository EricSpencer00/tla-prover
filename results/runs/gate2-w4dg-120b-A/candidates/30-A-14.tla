---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

MessageTypes == {"phase1", "phase2"}
Phases == {"phase1B", "phase1W", "prep", "phase2B", "phase2W",
           "done", "crashed", "choosing"}

RECURSIVE MaxVal(_)
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE LET x == CHOOSE y \in S : TRUE IN IF x > MaxVal(S \ {x}) THEN x ELSE MaxVal(S \ {x})

VARIABLES phase, view, prop, est, decided, crashCount, sentMsgs, recvLog

vars == <<phase, view, prop, est, decided, crashCount, sentMsgs, recvLog>>

TypeOK ==
    /\ phase \in [1..N -> Phases]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashCount \in 0..F
    /\ sentMsgs \subseteq [type: MessageTypes, val: Values, sender: 1..N, est: Values \cup {Bottom}]
    /\ recvLog \in [1..N -> SUBSET 1..N]

Init ==
    /\ phase = [i \in 1..N |-> "phase1B"]
    /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ est = [i \in 1..N |-> Bottom]
    /\ decided = [i \in 1..N |-> Bottom]
    /\ crashCount = 0
    /\ sentMsgs = {}
    /\ recvLog = [i \in 1..N |-> {}]

Bump(a, S) == IF a \in S THEN S ELSE S \cup {a}

Recv(i, m) ==
    /\ phase[i] \in {"phase1W", "phase2W"}
    /\ m.type = IF phase[i] = "phase1W" THEN "phase1" ELSE "phase2"
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ recvLog' = [recvLog EXCEPT ![i] = Bump(m.sender, @)]
    /\ UNCHANGED <<phase, prop, est, decided, crashCount, sentMsgs>>

Broadcast1(i) ==
    /\ phase[i] = "phase1B"
    /\ sentMsgs' = sentMsgs \cup {[type |-> "phase1", val |-> prop[i], sender |-> i, est |-> Bottom]}
    /\ phase' = [phase EXCEPT ![i] = "phase1W"]
    /\ UNCHANGED <<view, prop, est, decided, crashCount, recvLog>>

ComputeEst(i) ==
    /\ phase[i] = "phase1W"
    /\ Cardinality(recvLog[i]) >= N - T
    /\ est' = [est EXCEPT ![i] = MaxVal({view[i][j] : j \in recvLog[i]})]
    /\ phase' = [phase EXCEPT ![i] = "phase2B"]
    /\ UNCHANGED <<view, prop, decided, crashCount, sentMsgs, recvLog>>

Broadcast2(i) ==
    /\ phase[i] = "phase2B"
    /\ sentMsgs' = sentMsgs \cup {[type |-> "phase2", val |-> prop[i], sender |-> i, est |-> est[i]]}
    /\ phase' = [phase EXCEPT ![i] = "phase2W"]
    /\ UNCHANGED <<view, prop, est, decided, crashCount, sentMsgs, recvLog>>

Decide(i, v) ==
    /\ phase[i] = "phase2W"
    /\ Cardinality({m \in recvLog[i] : view[i][m] = v}) >= N - T
    /\ decided' = [decided EXCEPT ![i] = v]
    /\ phase' = [phase EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashCount, sentMsgs, recvLog>>

Choose(i) ==
    /\ phase[i] = "phase2W"
    /\ recvLog[i] = 1..N
    /\ phase' = [phase EXCEPT ![i] = "choosing"]
    /\ UNCHANGED <<view, prop, est, decided, crashCount, sentMsgs, recvLog>>

Settle(i, v) ==
    /\ phase[i] = "choosing"
    /\ v \in {view[i][j] : j \in 1..N}
    /\ decided' = [decided EXCEPT ![i] = v]
    /\ phase' = [phase EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashCount, sentMsgs, recvLog>>

Crash(i) ==
    /\ phase[i] \notin {"crashed", "done"}
    /\ crashCount < F
    /\ phase' = [phase EXCEPT ![i] = "crashed"]
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED <<view, prop, est, decided, sentMsgs, recvLog>>

Next ==
    \/ \E i \in 1..N, m \in sentMsgs : Recv(i, m)
    \/ \E i \in 1..N : Broadcast1(i) \/ ComputeEst(i) \/ Broadcast2(i) \/ Choose(i) \/ Crash(i)
    \/ \E i \in 1..N, v \in Values : Decide(i, v) \/ Settle(i, v)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 1..N, m \in sentMsgs : Recv(i, m))
        /\ WF_vars(\E i \in 1..N : Broadcast1(i))
        /\ WF_vars(\E i \in 1..N : ComputeEst(i))
        /\ WF_vars(\E i \in 1..N : Broadcast2(i))
        /\ WF_vars(\E i \in 1..N : Choose(i))
        /\ WF_vars(\E i \in 1..N : Crash(i))

Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : prop[j] = decided[i]

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination == <>(\A i \in 1..N : phase[i] \in {"done", "crashed"})

C1ConditionalTermination ==
    (Cardinality({i \in 1..N : prop[i] = MaxVal(Range(prop))}) >= F + 1) ~> (\A i \in 1..N : phase[i] \in {"done", "crashed"})
====