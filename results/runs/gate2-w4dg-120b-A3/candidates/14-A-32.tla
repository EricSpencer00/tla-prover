---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES role, want, ticket, nextTicket
vars == <<role, want, ticket, nextTicket>>

NoTicket == 0 - 1

TypeOK ==
  /\ role \in [1..N -> {"idle", "trying", "cs"}]
  /\ want \in BOOLEAN
  /\ ticket \in [1..N -> (NoTicket..MaxNat)]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ role = [i \in 1..N |-> "idle"]
  /\ want = FALSE
  /\ ticket = [i \in 1..N |-> NoTicket]
  /\ nextTicket = 0

Want(i) ==
  /\ role[i] = "idle"
  /\ role' = [role EXCEPT ![i] = "trying"]
  /\ want' = TRUE
  /\ UNCHANGED <<ticket, nextTicket>>

Take(i) ==
  /\ role[i] = "trying"
  /\ \A j \in 1..N : role[j] # "cs"
  /\ \A j \in 1..N : ticket[j] # NoTicket => ticket[j] > nextTicket
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)
  /\ role' = [role EXCEPT ![i] = "cs"]
  /\ UNCHANGED want

Exit(i) ==
  /\ role[i] = "cs"
  /\ role' = [role EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = NoTicket]
  /\ UNCHANGED <<want, nextTicket>>

Abandon(i) ==
  /\ role[i] = "trying"
  /\ role' = [role EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<want, ticket, nextTicket>>

Next ==
  \/ \E i \in 1..N : Want(i)
  \/ \E i \in 1..N : Take(i)
  \/ \E i \in 1..N : Exit(i)
  \/ \E i \in 1..N : Abandon(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (role[i] = "cs" /\ role[j] = "cs") => i = j

Inv ==
  /\ (\A i \in 1..N : role[i] = "cs" => ticket[i] = nextTicket - 1)
  /\ (nextTicket >= 1 => \A i \in 1..N : role[i] = "cs" => ticket[i] = nextTicket - 1)
  /\ (\A i \in 1..N : role[i] = "trying" => ticket[i] = NoTicket)

StateBound == \A i \in 1..N : ticket[i] # MaxNat

NatOverride == Nat

====