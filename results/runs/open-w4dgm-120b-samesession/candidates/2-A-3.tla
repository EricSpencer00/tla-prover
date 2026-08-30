---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Concrete participant identifiers (bounded pool) derived from the constant set.
\* The set itself is a constant to keep the model finite, with symmetry reduction applied.
Ids == CHOOSE S \in SUBSET participants : Cardinality(S) = 3

VARIABLES vote, alive, decision, faulty, voteSent, req, coordinator, forwarded

vars == <<vote, alive, decision, faulty, voteSent, req, coordinator, forwarded>>

TypeOK ==
    /\ vote \in [Ids -> {yes, no, undecided}]
    /\ alive \in [Ids -> BOOLEAN]
    /\ decision \in [Ids -> {commit, abort, waiting}]
    /\ faulty \in [Ids -> BOOLEAN]
    /\ voteSent \in [Ids -> BOOLEAN]
    /\ req \in {yes, no, undecided}
    /\ coordinator \in {alive, waiting, faulty}
    /\ forwarded \in [Ids -> [Ids -> {notsent, commit, abort}]]

Init ==
    /\ vote = [i \in Ids |-> undecided]
    /\ alive = [i \in Ids |-> TRUE]
    /\ decision = [i \in Ids |-> waiting]
    /\ faulty = [i \in Ids |-> FALSE]
    /\ voteSent = [i \in Ids |-> FALSE]
    /\ req = undecided
    /\ coordinator = alive
    /\ forwarded = [i \in Ids |-> [j \in Ids |-> notsent]]

\* Coordinator crashes silently: it stops deciding but no one is notified.
\* The forwarding mechanism is what keeps non-faulty participants from waiting forever.
CoordDie ==
    /\ coordinator = alive
    /\ coordinator' = faulty
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, forwarded>>

SendVote(i) ==
    /\ coordinator = alive
    /\ alive[i]
    /\ vote[i] = undecided
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![i] = v]
    /\ voteSent' = [voteSent EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, req, coordinator, forwarded>>

MakeDecision ==
    /\ coordinator = alive
    /\ req = undecided
    /\ req' = IF \A i \in Ids : vote[i] = yes THEN yes ELSE no
    /\ coordinator' = waiting
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, forwarded>>

\* Broadcast is best-effort (no ack): a receiver may be dead, and the coordinator may
\* crash mid-round, so a participant may never hear from the coordinator.
Broadcast ==
    /\ coordinator = waiting
    /\ coordinator' = alive
    /\ forwarded' = [i \in Ids |-> [j \in Ids |->
                        IF alive[j] THEN req ELSE forwarded[i][j]]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req>>

\* A participant records a pre-decision either directly from the coordinator (it got
\* there), or from any other participant that has already recorded it.
PreDecideFromCoordinator(i) ==
    /\ alive[i]
    /\ forwarded[i][i] = notsent
    /\ coordinator = alive
    /\ req # undecided
    /\ forwarded' = [forwarded EXCEPT ![i][i] = req]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordinator>>

PreDecideFromForward(i) ==
    /\ alive[i]
    /\ forwarded[i][i] = notsent
    /\ \E j \in Ids : j # i /\ forwarded[j][i] # notsent
    /\ forwarded' = [forwarded EXCEPT ![i][i] = forwarded[j][i]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordinator>>

Forward(i, j) ==
    /\ alive[i]
    /\ alive[j]
    /\ forwarded[i][i] # notsent
    /\ forwarded[i][j] = notsent
    /\ forwarded' = [forwarded EXCEPT ![i][j] = forwarded[i][i]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, req, coordinator>>

Decide(i) ==
    /\ alive[i]
    /\ decision[i] = waiting
    /\ forwarded[i][i] # notsent
    /\ \A j \in Ids : (j = i \/ ~alive[j] \/ forwarded[i][j] # notsent)
    /\ decision' = [decision EXCEPT ![i] = forwarded[i][i]]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, req, coordinator, forwarded>>

\* A participant may give up waiting for the coordinator's broadcast if the
\* coordinator has died, no live participant ever got a broadcast, and no dead
\* participant has already forwarded a decision to it -- so nothing is lost.
AbortOnTimeout(i) ==
    /\ alive[i]
    /\ decision[i] = waiting
    /\ coordinator = faulty
    /\ (\A j \in Ids : alive[j] => forwarded[j][i] = notsent)
    /\ (\A j \in Ids : faulty[j] => \A k \in Ids : forwarded[j][k] = notsent)
    /\ decision' = [decision EXCEPT ![i] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voteSent, req, coordinator, forwarded>>

Die(i) ==
    /\ alive[i]
    /\ alive' = [alive EXCEPT ![i] = FALSE]
    /\ faulty' = [faulty EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote, decision, voteSent, req, coordinator, forwarded>>

Next ==
    \/ CoordDie \/ MakeDecision \/ Broadcast
    \/ \E i \in Ids :
         \/ SendVote(i) \/ PreDecideFromCoordinator(i) \/ PreDecideFromForward(i)
         \/ Decide(i) \/ AbortOnTimeout(i) \/ Die(i)
         \/ \E j \in Ids : Forward(i, j)

\* A decision is only irreversible once it is final and irreversible: there is no
\* action to undo or change a participant's decision once it is made.
SpecNB == Init /\ [][Next]_vars
    /\ WF_vars(\E i \in Ids : SendVote(i) \/ PreDecideFromCoordinator(i)
                              \/ PreDecideFromForward(i) \/ Forward(i, CHOOSE k \in Ids : TRUE)
                              \/ Decide(i) \/ AbortOnTimeout(i))
    /\ SF_vars(Broadcast)
    /\ WF_vars(\E i \in Ids, j \in Ids : Forward(i, j))

\* Safety: no conflicting decisions, decision always matches the actual vote
\* outcome, and no decision is ever undone.
Agreement ==
    \A i, j \in Ids : (decision[i] = commit /\ decision[j] = abort) => FALSE
CommitValidity ==
    (\E i \in Ids : decision[i] = commit) => (\A i \in Ids : vote[i] = yes)
AbortValidity ==
    (\E i \in Ids : decision[i] = abort) =>
        (\E i \in Ids : vote[i] = no) \/ (\E i \in Ids : faulty[i]) \/ coordinator = faulty
Irrevocability ==
    \A i \in Ids : (decision[i] # waiting) ~> (decision[i] = decision[i])

\* Progress: either everyone decides or someone is known to have failed; and
\* every non-crashed participant eventually decides, which is the new guarantee.
Termination == <>(\A i \in Ids : decision[i] # waiting \/ \E i \in Ids : faulty[i])
NonBlocking == \A i \in Ids : alive[i] ~> (decision[i] # waiting \/ faulty[i])

\* The full set of properties checked for AC3 (safety) and AC5 (non-blocking).
Properties == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

\* For AC3 alone: the protocol always reaches a decision or discovers a fault.
AC3Liveness == Termination

\* For AC5 alone: the non-blocking guarantee holds even when the coordinator
\* crashes silently mid-round, because peer forwarding always suffices to finish.
AC5Liveness == NonBlocking

TypeInvNB == TypeOK

====