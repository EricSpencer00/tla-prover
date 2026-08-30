---- MODULE MCBakery ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

\* Same as the Bakery specification; NAT is overridden below to be a finite range
\* rather than an unbounded set, so the model is checkable.
VARIABLES inCS, line, want, ticket, nextTicket, crashed

vars == <<inCS, line, want, ticket, nextTicket, crashed>>

TypeOK ==
  /\ inCS \in 0..N
  /\ line \in Seq(Naturals)
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ crashed \in 0..N

\* SAFETY PROPERTY (inherited): at most one process is in the critical section.
MutualExclusion == inCS <= 1

\* Full inductive invariant, inheriting the safety properties of the Bakery spec.
\* The ticket-number bound is part of the invariant, which is what keeps the
\* number of reachable states finite under the overridden NAT.
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ nextTicket <= MaxNat
  /\ \A p \in 1..N : want[p] => \E i \in 1..Len(line) : line[i] = p
  /\ \A i \in 1..Len(line) : \A j \in 1..Len(line) :
        (line[i] = line[j]) => (i = j)

NextNat(n) == IF n < MaxNat THEN n + 1 ELSE n

Init ==
  /\ inCS = 0
  /\ line = <<>>
  /\ want = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ crashed = 0

Request(p) ==
  /\ p # crashed
  /\ want[p] = FALSE
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = NextNat(nextTicket)
  /\ UNCHANGED <<inCS, line, crashed>>

Enqueue(p) ==
  /\ p # crashed
  /\ want[p] = TRUE
  /\ \A i \in 1..Len(line) : line[i] # p
  /\ line' = Append(line, p)
  /\ UNCHANGED <<inCS, want, ticket, nextTicket, crashed>>

Enter(p) ==
  /\ p # crashed
  /\ \E i \in 1..Len(line) : line[i] = p
  /\ inCS = 0
  /\ inCS' = 1
  /\ line' = SelectSeq(line, LAMBDA x : x # p)
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket, crashed>>

Exit(p) ==
  /\ p # crashed
  /\ inCS = 1
  /\ inCS' = inCS - 1
  /\ UNCHANGED <<line, want, ticket, nextTicket, crashed>>

\* The twist: a process may crash silently, keeping its critical section and
\* ticket number, which is what tests the invariant against a stuck-but-consistent
\* holder. At most one process crashes, and only while not already crashed.
Crash(p) ==
  /\ crashed = 0
  /\ p # crashed
  /\ crashed' = p
  /\ UNCHANGED <<inCS, line, want, ticket, nextTicket>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enqueue(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)
  \/ \E p \in 1..N : Crash(p)

\* Model checking starts from any type-correct state satisfying the invariant,
\* not just from the initial state, so the invariant must hold inductively.
ISpec == Init /\ [][Next]_vars /\ WF_vars(\E p \in 1..N : Enter(p))
          /\ WF_vars(\E p \in 1..N : Exit(p))

\* The .cfg file that drives TLC replaces NAT with NatOverride here; because the
\* override replaces Nat globally, this definition must be present but must not
\* itself declare or redefine Nat.
NatOverride == 0..MaxNat

====