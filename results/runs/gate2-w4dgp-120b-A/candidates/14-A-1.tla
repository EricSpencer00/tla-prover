---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES turn, bstate, want, ticket, maxTicket

vars == <<turn, bstate, want, ticket, maxTicket>>

TypeOK ==
    /\ turn \in 0..N
    /\ bstate \in [1..N -> {"idle", "waiting", "cs"}]
    /\ want \in 0..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ maxTicket \in 0..MaxNat

Init ==
    /\ turn = 0
    /\ bstate = [p \in 1..N |-> "idle"]
    /\ want = 0
    /\ ticket = [p \in 1..N |-> 0]
    /\ maxTicket = 0

Request ==
    /\ \E p \in 1..N :
         /\ bstate[p] = "idle"
         /\ bstate' = [bstate EXCEPT ![p] = "waiting"]
         /\ ticket' = [ticket EXCEPT ![p] = maxTicket]
         /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
    /\ UNCHANGED <<turn, want>>

Dequeue(p) ==
    /\ bstate[p] = "waiting"
    /\ \A q \in 1..N : (q # p => ticket[p] < ticket[q] \/ (ticket[p] = ticket[q] /\ p < q))
    /\ turn' = (turn % N) + 1
    /\ UNCHANGED <<bstate, want, ticket, maxTicket>>

Enter(p) ==
    /\ turn = p
    /\ bstate[p] = "waiting"
    /\ bstate' = [bstate EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<turn, want, ticket, maxTicket>>

Exit(p) ==
    /\ bstate[p] = "cs"
    /\ bstate' = [bstate EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<turn, want, ticket, maxTicket>>

Next == Request \/ \E p \in 1..N : Dequeue(p) \/ Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N : bstate[p] = "cs" => turn = p

Inv ==
    \A p \in 1..N :
        /\ bstate[p] = "cs" => turn = p
        /\ (\E q \in 1..N : bstate[q] = "waiting") => (want = 0 \/ turn \in {p \in 1..N : bstate[p] = "waiting"})
        /\ (\A q \in 1..N : ticket[p] >= ticket[q]) => (bstate[q] # "cs")
        /\ (\A q \in 1..N : ticket[p] >= ticket[q] /\ (ticket[p] = ticket[q] => p <= q)) => (bstate[p] = "cs")
        /\ (bstate[p] # "cs") => (bstate[p] = "idle" <=> ticket[p] = 0)

NatOverride == Nat

====