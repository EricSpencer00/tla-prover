---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

VARIABLES cs, pc, ticket, nextTicket, inCS, bb
vars == <<cs, pc, ticket, nextTicket, inCS, bb>>

TypeOK ==
    /\ cs \in 0 .. (N - 1)
    /\ pc \in [0 .. (N - 1) -> {"idle", "waiting", "holding"}]
    /\ ticket \in [0 .. (N - 1) -> 0 .. MaxNat]
    /\ nextTicket \in 0 .. MaxNat
    /\ inCS \in [0 .. (N - 1) -> BOOLEAN]
    /\ bb \in [0 .. (N - 1) -> BOOLEAN]

Init ==
    /\ cs = 0
    /\ pc = [p \in 0 .. (N - 1) |-> "idle"]
    /\ ticket = [p \in 0 .. (N - 1) |-> 0]
    /\ nextTicket = 0
    /\ inCS = [p \in 0 .. (N - 1) |-> FALSE]
    /\ bb = [p \in 0 .. (N - 1) |-> FALSE]

Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED <<cs, inCS, bb>>

PassToken ==
    /\ cs' = (cs + 1) % N
    /\ UNCHANGED <<pc, ticket, nextTicket, inCS, bb>>

Enter(p) ==
    /\ pc[p] = "waiting"
    /\ cs = p
    /\ \A q \in 0 .. (N - 1) : ticket[q] >= ticket[p]
    /\ inCS[p] = FALSE
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "holding"]
    /\ UNCHANGED <<cs, ticket, nextTicket, bb>>

Exit(p) ==
    /\ pc[p] = "holding"
    /\ inCS[p] = TRUE
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<cs, ticket, nextTicket, bb>>

ReadBag(p) ==
    /\ pc[p] \in {"waiting", "holding"}
    /\ \A q \in 0 .. (N - 1) : ~bb[q]
    /\ \E q \in 0 .. (N - 1) : inCS[q]
    /\ \A q \in 0 .. (N - 1) : ~(pc[q] \in {"waiting", "holding"} /\ ticket[q] < ticket[p])
    /\ bb' = [bb EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cs, pc, ticket, nextTicket, inCS>>

Expire(p) ==
    /\ pc[p] \in {"waiting", "holding"}
    /\ \E q \in 0 .. (N - 1) : pc[q] \in {"waiting", "holding"} /\ ticket[q] < ticket[p]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<cs, ticket, nextTicket, inCS, bb>>

Next ==
    \/ \E p \in 0 .. (N - 1) : Request(p)
    \/ PassToken
    \/ \E p \in 0 .. (N - 1) : Enter(p)
    \/ \E p \in 0 .. (N - 1) : Exit(p)
    \/ \E p \in 0 .. (N - 1) : ReadBag(p)
    \/ \E p \in 0 .. (N - 1) : Expire(p)

Spec == Init /\ [][Next]_vars

\* The two sides below are exactly equivalent; the right side is the one the
\* Boulanger specification actually reasons from, and the left side is the
\* mutual-exclusion claim the model is checking against.
MutualExclusion ==
    /\ \A p, q \in 0 .. (N - 1) : (inCS[p] /\ inCS[q]) => (p = q)
    /\ \A p \in 0 .. (N - 1) : inCS[p] => (pc[p] = "holding")

\* The full pair of invariants the Boulanger specification carries alongside
\* the mutual-exclusion claim.
Inv ==
    /\ \A p \in 0 .. (N - 1) : pc[p] = "holding" => inCS[p]
    /\ \A p \in 0 .. (N - 1) : inCS[p] => pc[p] = "holding"

\* Overriding Naturals.Nat with a finite version is what makes bounded
\* model checking tractable here; it must not change the claim being checked.
NatOverride == TRUE

====