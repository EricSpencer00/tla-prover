-------------------------- MODULE W4Od17m1p5t5 --------------------------
EXTENDS Naturals, TLC

CONSTANTS Bags

\* Fixed ring of three router nodes.
RNodes == {"r1", "r2", "r3"}
Succ == ("r1" :> "r2" @@ "r2" :> "r3" @@ "r3" :> "r1")

VARIABLES
    token,          \* node currently holding the dispatch token
    state,          \* state[b] : "pending" | "dispatched"
    dispatchCount,  \* dispatchCount[b] : how many times b has been dispatched
    adminBusy       \* TRUE iff the administrator has seized the ring

vars == << token, state, dispatchCount, adminBusy >>

TypeOK ==
    /\ token \in RNodes
    /\ state \in [Bags -> {"pending", "dispatched"}]
    /\ dispatchCount \in [Bags -> 0..2]
    /\ adminBusy \in BOOLEAN

Init ==
    /\ token = "r1"
    /\ state = [b \in Bags |-> "pending"]
    /\ dispatchCount = [b \in Bags |-> 0]
    /\ adminBusy = FALSE

\* Token circulates while the administrator is not in control.
PassToken ==
    /\ ~adminBusy
    /\ token' = Succ[token]
    /\ UNCHANGED << state, dispatchCount, adminBusy >>

\* The token holder finally dispatches a pending bag.
Dispatch(n, b) ==
    /\ ~adminBusy
    /\ token = n
    /\ state[b] = "pending"
    /\ state' = [state EXCEPT ![b] = "dispatched"]
    /\ dispatchCount' = [dispatchCount EXCEPT ![b] = @ + 1]
    /\ UNCHANGED << token, adminBusy >>

\* Admin override: seize the ring.
AdminSeize ==
    /\ ~adminBusy
    /\ adminBusy' = TRUE
    /\ UNCHANGED << token, state, dispatchCount >>

AdminRelease ==
    /\ adminBusy
    /\ adminBusy' = FALSE
    /\ UNCHANGED << token, state, dispatchCount >>

\* While in control the administrator may itself dispatch a pending bag.
AdminDispatch(b) ==
    /\ adminBusy
    /\ state[b] = "pending"
    /\ state' = [state EXCEPT ![b] = "dispatched"]
    /\ dispatchCount' = [dispatchCount EXCEPT ![b] = @ + 1]
    /\ UNCHANGED << token, adminBusy >>

Next ==
    \/ PassToken
    \/ \E n \in RNodes, b \in Bags : Dispatch(n, b)
    \/ AdminSeize
    \/ AdminRelease
    \/ \E b \in Bags : AdminDispatch(b)

Spec == Init /\ [][Next]_vars

\* The irreversible dispatch of each bag happens at most once.
DispatchAtMostOnce == \A b \in Bags : dispatchCount[b] <= 1

=============================================================================
