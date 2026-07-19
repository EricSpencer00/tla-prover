-------------------------- MODULE W4Od11m5p0t1 --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Jobs, Voters, NoJob, Quorum

VARIABLES
    grant,      \* grant[v] : the job voter v currently backs, or NoJob
    pc          \* pc[j] : "idle" | "seeking" | "printing"

vars == << grant, pc >>

TypeOK ==
    /\ grant \in [Voters -> (Jobs \cup {NoJob})]
    /\ pc \in [Jobs -> {"idle", "seeking", "printing"}]

Init ==
    /\ grant = [v \in Voters |-> NoJob]
    /\ pc = [j \in Jobs |-> "idle"]

Support(j) == {v \in Voters : grant[v] = j}

Request(j) ==
    /\ pc[j] = "idle"
    /\ pc' = [pc EXCEPT ![j] = "seeking"]
    /\ UNCHANGED grant

\* A voter backs a seeking job; grants may be recorded in any order.
GiveVote(v, j) ==
    /\ pc[j] = "seeking"
    /\ grant[v] = NoJob
    /\ grant' = [grant EXCEPT ![v] = j]
    /\ UNCHANGED pc

\* A voter withdraws support from a job that is not yet printing.
Revoke(v) ==
    /\ grant[v] # NoJob
    /\ pc[grant[v]] # "printing"
    /\ grant' = [grant EXCEPT ![v] = NoJob]
    /\ UNCHANGED pc

\* Seize the printer once a quorum backs the job -- no other freeness check.
Enter(j) ==
    /\ pc[j] = "seeking"
    /\ Cardinality(Support(j)) >= Quorum
    /\ pc' = [pc EXCEPT ![j] = "printing"]
    /\ UNCHANGED grant

Finish(j) ==
    /\ pc[j] = "printing"
    /\ pc' = [pc EXCEPT ![j] = "idle"]
    /\ grant' = [v \in Voters |-> IF grant[v] = j THEN NoJob ELSE grant[v]]

Abort(j) ==
    /\ pc[j] = "seeking"
    /\ pc' = [pc EXCEPT ![j] = "idle"]
    /\ grant' = [v \in Voters |-> IF grant[v] = j THEN NoJob ELSE grant[v]]

Next ==
    \/ \E j \in Jobs : Request(j)
    \/ \E v \in Voters, j \in Jobs : GiveVote(v, j)
    \/ \E v \in Voters : Revoke(v)
    \/ \E j \in Jobs : Enter(j)
    \/ \E j \in Jobs : Finish(j)
    \/ \E j \in Jobs : Abort(j)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: quorum intersection ensures a single printer user.
PrinterExclusion ==
    \A j, k \in Jobs : (pc[j] = "printing" /\ pc[k] = "printing") => (j = k)

=============================================================================
