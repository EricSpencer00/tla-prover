---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    N,          \* number of processes
    T,          \* maximum tolerated faults
    F,          \* actual crash bound
    Values,     \* finite totally ordered set of proposal values
    Bottom      \* special value not in Values

\* ----------------------------------------------------------------------
\* Enumerations
\* ----------------------------------------------------------------------
MessageTypes == {"phase1", "phase2"}
ProcStates   == {"broadcast1", "wait1", "broadcast2", "wait2",
                "choosing", "done", "crashed"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    loc,            \* [proc -> state]
    proposals,      \* [proc -> value]  initial proposals
    localViews,     \* [proc -> [proc -> value]]  N-by-N matrix
    estimates,      \* [proc -> value]  max of local view after phase1
    decisions,      \* [proc -> value]  decision value or Bottom
    crashCount,     \* number of crashed processes
    sentMsgs,       \* set of messages sent so far
    recvMsgs        \* [proc -> SUBSET Message] messages received by each proc

vars == <<loc, proposals, localViews, estimates,
          decisions, crashCount, sentMsgs, recvMsgs>>

\* ----------------------------------------------------------------------
\* Message record
\* ----------------------------------------------------------------------
Message == [type : MessageTypes,
            sender : 1..N,
            prop : Values,
            est  : Values \cup {Bottom}]   \* est = Bottom for phase1

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in 1..N |-> "broadcast1"]
    /\ proposals \in [p \in 1..N |-> Values]
    /\ localViews = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ estimates = [p \in 1..N |-> Bottom]
    /\ decisions = [p \in 1..N |-> Bottom]
    /\ crashCount = 0
    /\ sentMsgs = {}
    /\ recvMsgs = [p \in 1..N |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ let m == [type |-> "phase1",
                sender |-> p,
                prop   |-> proposals[p],
                est    |-> Bottom] in
       /\ sentMsgs' = sentMsgs \cup {m}
       /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<proposals, localViews, estimates,
                   decisions, crashCount, recvMsgs>>

Receive1(p) ==
    /\ loc[p] = "wait1"
    /\ \E m \in sentMsgs :
          /\ m.type = "phase1"
          /\ m.sender \notin recvFrom(p)   \* not yet received from this sender
          /\ localViews' = [localViews EXCEPT
               ![p][m.sender] = m.prop]
          /\ recvMsgs' = [recvMsgs EXCEPT
               ![p] = recvMsgs[p] \cup {m}]
    /\ UNCHANGED <<loc, proposals, estimates,
                   decisions, crashCount, sentMsgs>>

Wait1To2(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({ m \in recvMsgs[p] : m.type = "phase1" }) >= N - T
    /\ estimates' = [estimates EXCEPT ![p] = Max({ localViews[p][q] : q \in 1..N })]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<proposals, localViews, decisions,
                   crashCount, sentMsgs, recvMsgs>>

Broadcast2(p) ==
    /\ loc[p] = "broadcast2"
    /\ let m == [type |-> "phase2",
                sender |-> p,
                prop   |-> proposals[p],
                est    |-> estimates[p]] in
       /\ sentMsgs' = sentMsgs \cup {m}
       /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<proposals, localViews, estimates,
                   decisions, crashCount, recvMsgs>>

Receive2(p) ==
    /\ loc[p] = "wait2"
    /\ \E m \in sentMsgs :
          /\ m.type = "phase2"
          /\ m.sender \notin recvFrom(p)
          /\ localViews' = [localViews EXCEPT
               ![p][m.sender] = m.prop]
          /\ recvMsgs' = [recvMsgs EXCEPT
               ![p] = recvMsgs[p] \cup {m}]
    /\ UNCHANGED <<loc, proposals, estimates, decisions,
                   crashCount, sentMsgs>>

Decide(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
          Cardinality({ m \in recvMsgs[p] :
                         m.type = "phase2" /\ m.est = v }) >= N - T
    /\ decisions' = [decisions EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<proposals, localViews, estimates,
                   crashCount, sentMsgs, recvMsgs>>

MoveToChoosing(p) ==
    /\ loc[p] = "wait2"
    /\ \A v \in Values :
          Cardinality({ m \in recvMsgs[p] :
                         m.type = "phase2" /\ m.est = v }) < N - T
    /\ \A m \in sentMsgs :
          m.type = "phase2" => m.sender \in recvFrom(p)
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<proposals, localViews, estimates,
                   decisions, crashCount, sentMsgs, recvMsgs>>

Choose(p) ==
    /\ loc[p] = "choosing"
    /\ \E v \in Values :
          \E q \in 1..N :
             localViews[p][q] = v
    /\ decisions' = [decisions EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<proposals, localViews, estimates,
                   crashCount, sentMsgs, recvMsgs>>

Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashCount < F
    /\ crashCount' = crashCount + 1
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<proposals, localViews, estimates,
                   decisions, sentMsgs, recvMsgs>>

Next ==
    \/ \E p \in 1..N : Broadcast1(p)
    \/ \E p \in 1..N : Receive1(p)
    \/ \E p \in 1..N : Wait1To2(p)
    \/ \E p \in 1..N : Broadcast2(p)
    \/ \E p \in 1..N : Receive2(p)
    \/ \E p \in 1..N : Decide(p)
    \/ \E p \in 1..N : MoveToChoosing(p)
    \/ \E p \in 1..N : Choose(p)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Helper for received senders
\* ----------------------------------------------------------------------
recvFrom(p) == { m.sender : m \in recvMsgs[p] }

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [1..N -> ProcStates]
    /\ proposals \in [1..N -> Values]
    /\ localViews \in [1..N -> [1..N -> (Values \cup {Bottom})]]
    /\ estimates \in [1..N -> (Values \cup {Bottom})]
    /\ decisions \in [1..N -> (Values \cup {Bottom})]
    /\ crashCount \in Nat
    /\ sentMsgs \subseteq Message
    /\ recvMsgs \in [1..N -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
    \A p \in 1..N :
        decisions[p] # Bottom => decisions[p] \in Values

Agreement ==
    \A p,q \in 1..N :
        /\ decisions[p] # Bottom
        /\ decisions[q] # Bottom
        => decisions[p] = decisions[q]

\* ----------------------------------------------------------------------
\* Theorem (optional, for documentation)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK /\ []Validity /\ []Agreement

====