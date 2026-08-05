---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

\* River crossing puzzle: missionaries and cannibals cross by boat.  A bank
\* is safe when missionaries are outnumbered by cannibals only if there are
\* no missionaries there at all.
CONSTANTS Missionaries, Cannibals
Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boat, bankOf

TypeOK ==
  /\ boat \in Banks
  /\ bankOf \in [People -> Banks]

Init ==
  /\ boat = "east"
  /\ bankOf = [p \in People |-> "east"]

\* A crossing moves a group of size 1 or 2 across the river, and is allowed
\* only when both banks are safe afterwards.
Cross(m, g) ==
  /\ g \subseteq {p \in People : bankOf[p] = m}
  /\ Cardinality(g) \in 1..2
  /\ LET newBank == [bankOf EXCEPT ![q \in g] = IF m = "east" THEN "west" ELSE "east"]
     IN /\ \A o \in People :
           bankOf[o] = m => Cardinality({x \in g : x = o}) <= 1
        /\ \A o \in People :
           (newBank[o] # "east" => Cardinality({x \in People : newBank[x] = "east"}) = 0)
              \/ Cardinality({x \in People : newBank[x] = "east"}) >= Cardinality({x \in People : bankOf[x] = "east"})
        /\ \A o \in People :
           (newBank[o] # "west" => Cardinality({x \in People : newBank[x] = "west"}) = 0)
              \/ Cardinality({x \in People : newBank[x] = "west"}) >= Cardinality({x \in People : bankOf[x] = "west"})
        /\ bankOf' = newBank
  /\ boat' = IF m = "east" THEN "west" ELSE "east"

Next ==
  \/ \E g \in SUBSET People : Cross("east", g)
  \/ \E g \in SUBSET People : Cross("west", g)

Solution == \A bank \in Banks :
  ~(\A p \in People : bankOf[p] = bank) /\ Cardinality({p \in People : bankOf[p] = bank}) >= Cardinality(People) / 2

====