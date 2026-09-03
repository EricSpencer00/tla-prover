---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS N1, I1, R1, NoNode

Node == N1
initiator == I1
R == R1

ASSUME NoNode \notin Node
ASSUME initiator \in Node

VARIABLES parent, seen, heard, crashed
vars == <<parent, seen, heard, crashed>>

RECURSIVE SeenSet(_)
SeenSet(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN heard[x] \cup SeenSet(S \ {x})

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ seen \subseteq Node
  /\ heard \subseteq Node
  /\ crashed \subseteq Node

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ seen = {}
  /\ heard = {}
  /\ crashed = {}

SendEcho ==
  /\ initiator \notin seen
  /\ seen' = seen \cup {initiator}
  /\ heard' = heard \cup {initiator}
  /\ parent' = [parent EXCEPT ![initiator] = initiator]
  /\ UNCHANGED crashed

RelayEcho ==
  /\ \E m \in Node, n \in Node :
       /\ m \notin seen
       /\ n \in seen
       /\ m \in R
       /\ m \notin crashed
       /\ parent' = [parent EXCEPT ![m] = n]
       /\ seen' = seen \cup {m}
       /\ heard' = heard \cup {m}
  /\ crashed' = crashed

Crash ==
  /\ \E m \in Node :
       /\ m \in R
       /\ m \notin crashed
       /\ crashed' = crashed \cup {m}
  /\ UNCHANGED <<parent, seen, heard>>

Recover ==
  /\ \E m \in Node :
       /\ m \in crashed
       /\ crashed' = crashed \ {m}
  /\ UNCHANGED <<parent, seen, heard>>

Done ==
  /\ seen = Node
  /\ UNCHANGED vars

Next == SendEcho \/ RelayEcho \/ Crash \/ Recover \/ Done

InitSpec == Init
NextSpec == Next

AncestorProperties ==
  /\ (initiator \in seen) /\ (parent[initiator] = initiator)
  /\ \A n \in Node : n \in seen => (initiator \in SeenSet({n}))
  /\ \A a, b \in Node : (a \in seen /\ b \in seen /\ a # b) => (b \notin SeenSet({a}))

TestSpec == Init /\ [][Next]_vars
====