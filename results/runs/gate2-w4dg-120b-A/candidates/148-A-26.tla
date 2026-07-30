---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME GenesisBalance \in Nat

Blocks == Hash \cup {NoBlock}
Msgs == {NoHash} \cup Hash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

HashOf(b) == b[1]
PrevHashOf(b) == b[2]
OwnerOf(b) == b[3]
SignedBy(b) == b[4]
AmtOf(b) == b[5]
KindOf(b) == b[6]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Msgs -> Blocks]]
  /\ received \in [Node -> SUBSET Msgs]

\* Balance is computed by walking the account chain in reverse, so a node can
\* both earn and spend from the same chain.
RECURSIVE Balance(_)
Balance(n) ==
  IF lastHash = NoHash
  THEN 0
  ELSE IF OwnerOf(ledger[n][lastHash]) = n
       THEN IF KindOf(ledger[n][lastHash]) = "receive"
            THEN AmtOf(ledger[n][lastHash]) + Balance(PrevHashOf(ledger[n][lastHash]))
            ELSE Balance(PrevHashOf(ledger[n][lastHash]))
       ELSE Balance(PrevHashOf(ledger[n][lastHash]))

\* A block is currently in flight to a node if it is in that node's received
\* set, or has already been written into that node's local ledger copy.
InFlight(n) == {m \in Msgs : m \in received[n] \/ ledger[n][m] # NoBlockVal}

NextHash ==
  IF lastHash = NoHash THEN NoHashVal ELSE CalculateHash(<<lastHash>>, NoHashVal)

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [m \in Msgs |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* A valid signature is the public key derived from the block's owner.
ValidSignature(n, b) ==
  /\ SignedBy(b) \in PublicKey
  /\ \E p \in PrivateKey : SignedBy(b) = \E p2 \in PrivateKey : (p2 = p) /\ OwnerOf(b) \in {p2}
  /\ SignedBy(b) = OwnerOf(b)

\* The genesis block is created and written into every node's ledger at once.
CreateGenesis ==
  /\ lastHash = NoHash
  /\ \E p \in PrivateKey :
       /\ \A n \in Node : ledger' = [ledger EXCEPT ![n] = [NoHashVal |-> <<NoHashVal, NoHashVal, OwnerOf(NoHashVal), p, GenesisBalance, "genesis">]]
  /\ lastHash' = NoHashVal
  /\ received' = [n \in Node |-> {}]

CreateSend(n) ==
  /\ lastHash # NoHash
  /\ \E p \in PrivateKey :
       /\ OwnerOf(b) = n
       /\ SignedBy(b) = OwnerOf(b)
       /\ KindOf(b) = "send"
       /\ ledger[n][lastHash] # NoBlockVal
       /\ Balance(n) >= AmtOf(b)
  /\ lastHash' = NextHash
  /\ ledger' = [ledger EXCEPT ![n2] = [m \in Msgs |-> IF m = NextHash THEN <<HashOf(b), lastHash, OwnerOf(b), SignedBy(b), AmtOf(b), KindOf(b)>> ELSE ledger[n2][m]]]
  /\ received' = [n2 \in Node |-> received[n2] \cup {NextHash}]

CreateOpen(n) ==
  /\ lastHash # NoHash
  /\ \E b \in Blocks :
       /\ KindOf(b) = "send"
       /\ OwnerOf(b) # n
       /\ OwnerOf(b) \notin {ledger[n][m][3] : m \in InFlight(n)}
  /\ lastHash' = NextHash
  /\ ledger' = [ledger EXCEPT ![n2][NextHash] = <<HashOf(b), lastHash, n, SignedBy(b), 0, "open">>]
  /\ received' = [received EXCEPT ![n2] = received[n2] \cup {NextHash}]

CreateReceive(n) ==
  /\ lastHash # NoHash
  /\ \E b \in Blocks :
       /\ KindOf(b) = "send"
       /\ OwnerOf(b) # n
       /\ OwnerOf(b) \in {ledger[n][m][3] : m \in InFlight(n)}
  /\ lastHash' = NextHash
  /\ ledger' = [ledger EXCEPT ![n2][NextHash] = <<HashOf(b), lastHash, n, SignedBy(b), AmtOf(b), "receive">>]
  /\ received' = [received EXCEPT ![n2] = received[n2] \cup {NextHash}]

CreateChangeRep(n) ==
  /\ lastHash # NoHash
  /\ \E p \in PrivateKey :
       /\ OwnerOf(b) = n
       /\ SignedBy(b) = OwnerOf(b)
       /\ KindOf(b) = "change"
  /\ lastHash' = NextHash
  /\ ledger' = [ledger EXCEPT ![n2][NextHash] = <<HashOf(b), lastHash, OwnerOf(b), SignedBy(b), 0, "change">>]
  /\ received' = [received EXCEPT ![n2] = received[n2] \cup {NextHash}]

\* A block is validated against the local copy before it is written.
Validate(n, m) ==
  /\ m \in received[n]
  /\ ledger[n][PrevHashOf(ledger[n][m])]
  /\ ValidSignature(n, ledger[n][m])
  /\ ledger' = [ledger EXCEPT ![n][m] = ledger[n][m]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {m}]
  /\ UNCHANGED lastHash

Next ==
  \/ CreateGenesis \/ CreateChangeRep(Node) \/ Validate(Node, NextHash)
  \/ \E n \in Node : CreateSend(n) \/ CreateOpen(n) \/ CreateReceive(n)

Spec == Init /\ [][Next]_vars

\* Every block in every replicated ledger copy carries a signature that matches
\* the public key of the account that owns the chain it sits on.
SafetyInvariant ==
  \A n \in Node : \A m \in Msgs : ledger[n][m] # NoBlockVal => ValidSignature(n, ledger[n][m])

====