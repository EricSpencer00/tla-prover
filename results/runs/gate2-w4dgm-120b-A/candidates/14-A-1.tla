---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES coarse, fine, ticket, maxUsed, slow

States == {"idle", "tryingCoarse", "tryingFine", "critical"}
NoTicket == MaxNat

TypeOK ==
  /\ coarse \in States
  /\ fine \in [1..N -> States]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxUsed \in 0..MaxNat
  /\ slow \in [1..N -> BOOLEAN]

Init ==
  /\ coarse = "idle"
  /\ fine = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ maxUsed = 0
  /\ slow = [i \in 1..N |-> FALSE]

EnterCoarse(i) ==
  /\ coarse = "idle"
  /\ fine[i] = "idle"
  /\ ~slow[i]
  /\ coarse' = "tryingCoarse"
  /\ fine' = [fine EXCEPT ![i] = "tryingFine"]
  /\ ticket' = [ticket EXCEPT ![i] = IF maxUsed < MaxNat THEN maxUsed + 1 ELSE 0]
  /\ maxUsed' = IF maxUsed < MaxNat THEN maxUsed + 1 ELSE maxUsed
  /\ UNCHANGED slow

EnterFine(i) ==
  /\ coarse = "tryingCoarse"
  /\ \A j \in 1..N : fine[j] # "tryingFine" \/ j = i
  /\ coarse' = "critical"
  /\ fine' = [fine EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<ticket, maxUsed, slow>>

Leave(i) ==
  /\ fine[i] = "critical"
  /\ coarse' = "idle"
  /\ fine' = [fine EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = NoTicket]
  /\ UNCHANGED <<maxUsed, slow>>

ToggleSlow(i) ==
  /\ slow' = [slow EXCEPT ![i] = ~slow[i]]
  /\ UNCHANGED <<coarse, fine, ticket, maxUsed>>

Next ==
  \/ \E i \in 1..N : EnterCoarse(i)
  \/ \E i \in 1..N : EnterFine(i)
  \/ \E i \in 1..N : Leave(i)
  \/ \E i \in 1..N : ToggleSlow(i)

Spec == Init /\ [][Next]_<<coarse, fine, ticket, maxUsed, slow>>

MutualExclusion ==
  \A i \in 1..N : fine[i] = "critical" => coarse = "critical"

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in 1..N : fine[i] # "idle" => (coarse = "tryingCoarse" \/ coarse = "critical")

TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====