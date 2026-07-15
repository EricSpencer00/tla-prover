---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

\*-----------------------------------------------------------------
\* Constants (as required by the .cfg)
\*-----------------------------------------------------------------
CONSTANT participants
CONSTANT yes, no, undecided, commit, abort, waiting, notsent

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES
    alive,               \* [Proc -> BOOLEAN] : true iff the process is alive
    faulty,              \* [Proc -> BOOLEAN] : true iff the process has crashed
    vote,                \* [Proc -> {yes,no}] : vote cast by participants
    decision,            \* [Proc -> {commit,abort,undecided}] : final decision
    preDec,              \* [Proc -> {commit,abort,undecided}] : pre‑decision stored after receipt
    forward                 \* [Proc -> [Proc -> {"notsent","commit","abort"}]]
    
\*-----------------------------------------------------------------
\* Helper sets
\*-----------------------------------------------------------------
Proc == {"c"} \cup participants   \* all processes (coordinator "c" plus participants)

\*-----------------------------------------------------------------
\* Type invariant (required)
\*-----------------------------------------------------------------
TypeInvNB ==
    /\ alive \in [Proc -> BOOLEAN]
    /\ faulty \in [Proc -> BOOLEAN]
    /\ vote \in [participants -> {yes,no}]
    /\ decision \in [participants -> {commit,abort,undecided}]
    /\ preDec \in [participants -> {commit,abort,undecided}]
    /\ forward \in [participants -> [participants -> {"notsent","commit","abort"}]]
    /\ \A i \in participants : forward[i][i] = "notsent"   \* self‑entries never used

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ alive = [p \in Proc |-> TRUE]
    /\ faulty = [p \in Proc |-> FALSE]
    /\ vote = [p \in participants |-> yes]    \* arbitrary, can be overwritten
    /\ decision = [p \in participants |-> undecided]
    /\ preDec = [p \in participants |-> undecided]
    /\ forward = [i \in participants |-> [j \in participants |-> notsent]]

\*-----------------------------------------------------------------
\* Coordinator actions (inherited from ACP‑SB)
\*-----------------------------------------------------------------
CoordinatorBroadcast ==
    /\ alive["c"] = TRUE
    /\ decision["c"] \in {commit, abort}
    /\ \E d \in {commit, abort} :
        /\ decision["c"] = d
        /\ \A p \in participants :
            /\ alive[p] = TRUE
            /\ preDec' = [preDec EXCEPT ![p] = d]
    /\ UNCHANGED <<alive, faulty, vote, decision, forward>>

CoordinatorDie ==
    /\ alive["c"] = TRUE
    /\ alive' = [alive EXCEPT !["c"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["c"] = TRUE]
    /\ UNCHANGED <<vote, decision, preDec, forward>>

\*-----------------------------------------------------------------
\* Participant actions
\*-----------------------------------------------------------------
ParticipantReceiveFromCoord(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ decision["c"] \in {commit, abort}
    /\ preDec[p] = undecided
    /\ preDec' = [preDec EXCEPT ![p] = decision["c"]]
    /\ UNCHANGED <<alive, faulty, vote, decision, forward>>

ParticipantReceiveFromPeer(p,q) ==
    /\ p,q \in participants
    /\ p # q
    /\ alive[p] = TRUE
    /\ forward[q][p] # "notsent"
    /\ preDec[p] = undecided
    /\ preDec' = [preDec EXCEPT ![p] = 
            IF forward[q][p] = "commit" THEN commit ELSE abort]
    /\ UNCHANGED <<alive, faulty, vote, decision, forward>>

ParticipantForward(p,q) ==
    /\ p,q \in participants
    /\ p # q
    /\ alive[p] = TRUE
    /\ preDec[p] \in {commit, abort}
    /\ forward[p][q] = "notsent"
    /\ forward' = [forward EXCEPT ![p][q] = 
            IF preDec[p] = commit THEN "commit" ELSE "abort"]
    /\ UNCHANGED <<alive, faulty, vote, decision, preDec>>

ParticipantDecide(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ preDec[p] \in {commit, abort}
    /\ \A q \in participants : q # p => forward[p][q] # "notsent"
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = preDec[p]]
    /\ UNCHANGED <<alive, faulty, vote, preDec, forward>>

ParticipantAbortOnTimeout(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ decision[p] = undecided
    /\ faulty["c"] = TRUE
    /\ \A q \in participants : forward[q][p] = "notsent"
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<alive, faulty, vote, preDec, forward>>

ParticipantDie(p) ==
    /\ p \in participants
    /\ alive[p] = TRUE
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, preDec, forward>>

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
    \/ CoordinatorBroadcast
    \/ CoordinatorDie
    \/ \E p \in participants : ParticipantReceiveFromCoord(p)
    \/ \E p,q \in participants : p # q /\ ParticipantReceiveFromPeer(p,q)
    \/ \E p,q \in participants : p # q /\ ParticipantForward(p,q)
    \/ \E p \in participants : ParticipantDecide(p)
    \/ \E p \in participants : ParticipantAbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<alive, faulty, vote, decision, preDec, forward>>

\*-----------------------------------------------------------------
\* Safety invariants (as described)
\*-----------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (decision[p] = commit) => (decision[q] = commit)

CommitValidity ==
    \A p \in participants :
        (decision[p] = commit) => (\A q \in participants : vote[q] = yes)

AbortValidity ==
    \A p \in participants :
        (decision[p] = abort) =>
            \/ \E q \in participants : vote[q] = no
            \/ \E q \in participants : faulty[q] = TRUE
            \/ faulty["c"] = TRUE

Irrevocability ==
    \A p \in participants :
        (decision[p] \in {commit, abort}) => 
            decision[p]' = decision[p]

\*-----------------------------------------------------------------
\* Liveness properties (named for completeness)
\*-----------------------------------------------------------------
Termination ==
    WF_vars(Next)   \* placeholder; TLC will check the liveness from the cfg

\*-----------------------------------------------------------------
\* The only exported identifier required by the .cfg is SpecNB and TypeInvNB.
\*-----------------------------------------------------------------
====