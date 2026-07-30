---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES phase, ticket, serving, wants

vars == <<phase, ticket, serving, wants>>

NoneP == 99
MaxT == MaxNat - 1

Phases == {"idle", "waiting", "holding"}

TypeOK ==
  /\ phase \in [1..N -> Phases]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ serving \in 0..N
  /\ wants \in SUBSET (1..N)

Init ==
  /\ phase = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ serving = 0
  /\ wants = {}

Request(p) ==
  /\ phase[p] = "idle"
  /\ phase' = [phase EXCEPT ![p] = "waiting"]
  /\ wants' = wants \cup {p}
  /\ UNCHANGED <<ticket, serving>>

Assign(p) ==
  /\ p \in wants
  /\ phase[p] = "waiting"
  /\ \A q \in 1..N : ticket[q] < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = CHOOSE t \in 0..MaxNat :
                               \A q \in 1..N : (phase[q] = "holding") => (ticket[q] # t)
                               /\ \A r \in 1..N : (phase[r] = "waiting" /\ r # p) => (ticket[r] < t)]
  /\ UNCHANGED <<phase, serving, wants>>

Enter(p) ==
  /\ phase[p] = "waiting"
  /\ serving = 0
  /\ serving' = p
  /\ phase' = [phase EXCEPT ![p] = "holding"]
  /\ wants' = wants \ {p}
  /\ UNCHANGED ticket

Exit(p) ==
  /\ phase[p] = "holding"
  /\ serving = p
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ serving' = 0
  /\ UNCHANGED <<ticket, wants>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Assign(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : Assign(p))
  /\ WF_vars(\E p \in 1..N : Enter(p))
  /\ WF_vars(\E p \in 1..N : Exit(p))

MutualExclusion ==
  \A p \in 1..N : phase[p] = "holding" => serving = p

Inv ==
  /\ \A p \in 1..N : phase[p] = "holding" => serving = p
  /\ \A p \in 1..N : phase[p] = "waiting" => ticket[p] < MaxNat

NatOverride == Nat

====