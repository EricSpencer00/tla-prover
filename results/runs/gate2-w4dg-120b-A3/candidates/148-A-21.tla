---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey,
  Node, GenesisBalance, NoBlockVal, CalculateHash,
  NoHash, NoBlock

\* The hash calculation is an abstract constant operator; the model checker
\* substitutes a finite version, giving the checker a bounded state space.
CalculateHashImpl == CalculateHash

VARIABLES
  LastHash, Ledger, Received

vars == <<LastHash, Ledger, Received>>

Block == [prev: Hash, pKey: PublicKey, kind: {"genesis", "send", "open", "receive", "change"}, to: PublicKey, amt: 1..GenesisBalance]

BlocksWritten == {Ledger[n][h] : n \in Node, h \in Hash} \ {NoBlockVal}

TypeInvariant ==
  /\ LastHash \in {NoHashVal} \cup Hash
  /\ Ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ Received \in [Node -> SUBSET Hash]

\* Each node owns exactly one private key (and its public key).
OwnerOfPublicKey(p) == CHOOSE n \in Node : p \in PublicKey[ n ]

SignedBy(k) == OwnerOfPublicKey(k) \in Node

BalanceOf(node, h) ==
  IF h = NoHash THEN 0
  ELSE LET b == Ledger[node][h] IN
    IF b.kind = "genesis" THEN GenesisBalance
    ELSE IF b.kind = "send" THEN BalanceOf(node, h) - b.amt
    ELSE IF b.kind = "open" THEN b.amt
    ELSE IF b.kind = "receive" THEN BalanceOf(node, b.prev) + b.amt
    ELSE IF b.kind = "change" THEN BalanceOf(node, h)
    ELSE BalanceOf(node, b.prev)

SumBalance ==
  LET f[S \in SUBSET Node] ==
        IF S = {} THEN 0
        ELSE LET n == CHOOSE x \in S : TRUE IN BalanceOf(n, LastHash) + f[S \ {n}]
  IN f[Node]

Init ==
  /\ LastHash = NoHashVal
  /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ Received = [n \in Node |-> {}]

CreateGenesisBlock(node) ==
  /\ LastHash = NoHashVal
  /\ node \in Node
  /\ SignedBy(PublicKey[node])
  /\ LET h == CalculateHashImpl([prev |-> NoHash, pKey |-> PublicKey[node], kind |-> "genesis", to |-> PublicKey[node], amt |-> GenesisBalance], NoHash) IN
       /\ LastHash' = h
       /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [prev |-> NoHash, pKey |-> PublicKey[node], kind |-> "genesis", to |-> PublicKey[node], amt |-> GenesisBalance]]]
       /\ Received' = [n \in Node |-> {h}]
  /\ UNCHANGED <<\E>>

CreateSendBlock(node, pKey, amt) ==
  /\ node \in Node
  /\ LastHash # NoHashVal
  /\ SignedBy(pKey)
  /\ amt \in 1..GenesisBalance
  /\ BalanceOf(node, LastHash) >= amt
  /\ LET h == CalculateHashImpl([prev |-> LastHash, pKey |-> pKey, kind |-> "send", to |-> PublicKey[node], amt |-> amt], LastHash) IN
       /\ LastHash' = h
       /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [prev |-> LastHash, pKey |-> pKey, kind |-> "send", to |-> PublicKey[node], amt |-> amt]]]
       /\ Received' = [n \in Node |-> Received[n] \cup {h}]
  /\ UNCHANGED <<\E>>

CreateOpenBlock(node, pKey) ==
  /\ node \in Node
  /\ LastHash # NoHashVal
  /\ SignedBy(pKey)
  /\ LET h == CalculateHashImpl([prev |-> NoHash, pKey |-> pKey, kind |-> "open", to |-> PublicKey[node], amt |-> 0], NoHash) IN
       (\A m \in Node : h \notin Received[m])
  /\ LastHash' = h
  /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [prev |-> NoHash, pKey |-> pKey, kind |-> "open", to |-> PublicKey[node], amt |-> 0]]]
  /\ Received' = [n \in Node |-> Received[n] \cup {h}]
  /\ UNCHANGED <<\E>>

CreateReceiveBlock(node, pKey, amt) ==
  /\ node \in Node
  /\ LastHash # NoHashVal
  /\ SignedBy(pKey)
  /\ amt \in 1..GenesisBalance
  /\ LET h == CalculateHashImpl([prev |-> LastHash, pKey |-> pKey, kind |-> "receive", to |-> PublicKey[node], amt |-> amt], LastHash) IN
       /\ LastHash' = h
       /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [prev |-> LastHash, pKey |-> pKey, kind |-> "receive", to |-> PublicKey[node], amt |-> amt]]]
       /\ Received' = [n \in Node |-> Received[n] \cup {h}]
  /\ UNCHANGED <<\E>>

CreateChangeBlock(node, pKey) ==
  /\ node \in Node
  /\ LastHash # NoHashVal
  /\ SignedBy(pKey)
  /\ LET h == CalculateHashImpl([prev |-> LastHash, pKey |-> pKey, kind |-> "change", to |-> PublicKey[node], amt |-> 0], LastHash) IN
       /\ LastHash' = h
       /\ Ledger' = [n \in Node |-> [Ledger[n] EXCEPT ![h] = [prev |-> LastHash, pKey |-> pKey, kind |-> "change", to |-> PublicKey[node], amt |-> 0]]]
       /\ Received' = [n \in Node |-> Received[n] \cup {h}]
  /\ UNCHANGED <<\E>>

ValidateBlock(n, h) ==
  /\ h \in Received[n]
  /\ Ledger[n][h].pKey = OwnerOfPublicKey(Ledger[n][h].pKey)
  /\ IF Ledger[n][h].prev = NoHash THEN TRUE ELSE Ledger[n][Ledger[n][h].prev] # NoBlockVal
  /\ IF Ledger[n][h].kind = "send" THEN BalanceOf(n, LastHash) >= Ledger[n][h].amt ELSE TRUE
  /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
  /\ UNCHANGED <<LastHash, Ledger>>

Next ==
  \/ \E n \in Node, k \in PublicKey : CreateGenesisBlock(n)
  \/ \E n \in Node, k \in PublicKey, amt \in 1..GenesisBalance : CreateSendBlock(n, k, amt)
  \/ \E n \in Node, k \in PublicKey : CreateOpenBlock(n, k)
  \/ \E n \in Node, k \in PublicKey, amt \in 1..GenesisBalance : CreateReceiveBlock(n, k, amt)
  \/ \E n \in Node, k \in PublicKey : CreateChangeBlock(n, k)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  /\ TypeInvariant
  /\ \A n \in Node, h \in Hash : Ledger[n][h] # NoBlockVal => Ledger[n][h].pKey = OwnerOfPublicKey(Ledger[n][h].pKey)
====