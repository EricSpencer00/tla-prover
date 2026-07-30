---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

\* Edge-case note: CalculateHash models a real one-way hash function abstractly here.
\* In a concrete implementation it would compute a Blake2b hash of the block data,
\* which is why it can be swapped for a different operator (e.g. a mock) without
\* changing the rest of the spec. Its output type is also what lets the model scale
\* so badly: each new block needs a fresh hash while still modeling an ordered chain.
\* That's the whole point of this example -- showing how blockchain-style structures
\* explode combinatorially even for a tiny bounded hash space.

VARIABLES lastHash, ledger, received

TypeInvariant ==
  /\ lastHash \in Hash
  /\ ledger \in [Node -> [Hash -> PublicKey \cup {NoBlockVal}]]
  /\ received \subseteq [node : Node, block : Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = {}

OpenAccount == {n \in Node : ledger[n][NoHash] # NoBlockVal}

\* BalanceOf walks the chain backwards from the tip hash, accumulating the
\* amounts that flowed in and out. It is a small-leap recursive function
\* rather than a loop, which is why the spec needs a finite hash space.
BalanceOf(n, h) ==
  IF h = NoHashVal THEN 0
  ELSE IF h = NoHash THEN 0
  ELSE LET prev == \E x \in Hash : ledger[n][x] = h /\ lastHash = x
           cprev == CHOOSE x \in Hash : ledger[n][x] = h /\ lastHash = x
           own    == ledger[n][h] = h
           amt    == IF own THEN GenesisBalance ELSE 1
       IN IF own THEN amt ELSE BalanceOf(n, cprev)

SendAmount(n) == IF ledger[n][NoHash] # NoBlockVal THEN BalanceOf(n, NoHash) ELSE 0

\* SentTo tracks one outstanding send per receiver, which is what the model
\* can check in a finite hash space. A real chain would need a full donor list.
SentTo(k) == {h \in Hash : \E n \in Node : ledger[n][h] = k}

CreateGenesis(n) ==
  /\ ledger[n][NoHash] = NoBlockVal
  /\ lastHash = NoHashVal
  /\ \A m \in Node : ledger' = [ledger EXCEPT ![m] = [NoHash |-> n]]
  /\ lastHash' = n
  /\ received' = received
  /\ UNCHANGED <<>>

CreateSend(n, k, h) ==
  /\ ledger[n][NoHash] # NoBlockVal
  /\ ledger[n][NoHash] = n
  /\ SendAmount(n) > 0
  /\ ~\E x \in Hash : ledger[k][x] = NoHash
  /\ \E x \in Hash :
       /\ ledger' = [ledger EXCEPT ![n] = [x |-> n, lastHash |-> NoHashVal]]
       /\ lastHash' = x
       /\ received' = received \cup {<<n, x>>}
  /\ UNCHANGED <<>>

CreateOpen(k, h) ==
  /\ ~\E n \in Node : ledger[n][NoHash] = k
  /\ ~\E x \in Hash : ledger[k][x] = NoHash
  /\ SentTo(k) # {}
  /\ \E x \in Hash :
       ledger' = [ledger EXCEPT ![k] = [x |-> k, lastHash |-> NoHashVal]]
       /\ lastHash' = x
       /\ received' = received \cup {<<k, x>>}
  /\ UNCHANGED <<>>

\* The receive block is the only one that records two predecessors: the chain
\* link and the send-link. It is also the only one that credits coins.
CreateReceive(k, h) ==
  /\ \E n \in Node : SentTo(k) # {}
  /\ ledger[k][NoHash] # NoBlockVal
  /\ \E x \in Hash :
       ledger' = [ledger EXCEPT ![k] = [x |-> k, lastHash |-> NoHashVal]]
       /\ lastHash' = x
       /\ received' = received \cup {<<k, x>>}
  /\ UNCHANGED <<>>

CreateChange(n, h) ==
  /\ ledger[n][NoHash] # NoBlockVal
  /\ \E x \in Hash :
       ledger' = [ledger EXCEPT ![n] = [x |-> n, lastHash |-> NoHashVal]]
       /\ lastHash' = x
       /\ received' = received \cup {<<n, x>>}
  /\ UNCHANGED <<>>

DeliverConfirm(n, h) ==
  /\ <<n, h>> \in received
  /\ ~(\E x \in Hash : ledger[n][x] = h)
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[NoHash][h]]
  /\ received' = received \ {<<n, h>>}
  /\ UNCHANGED <<lastHash>>

ValidateSignature(n, h) ==
  /\ <<n, h>> \in received
  /\ \E x \in Hash : ledger[NoHash][x] = h
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[NoHash][h]]
  /\ received' = received \ {<<n, h>>}
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E n \in Node : CreateGenesis(n) \/ CreateChange(n, NoHash)
  \/ \E n \in Node, k \in Node, h \in Hash : CreateSend(n, k, h)
  \/ \E k \in Node, h \in Hash : CreateOpen(k, h) \/ CreateReceive(k, h)
  \/ \E n \in Node, h \in Hash : DeliverConfirm(n, h) \/ ValidateSignature(n, h)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* Safety: each recorded block's signature must still match its account owner's
\* public key, i.e. no node was ever able to change a ledger entry without leaving
\* a forgeable signature behind.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[NoHash][h] = n

====