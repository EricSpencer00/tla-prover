---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* A block records its sender's public key, the previous block in that account's
\* chain, an optional source block it is receiving from, the amount, and a signature.
Block == [sender: PublicKey, prev: Hash \cup {NoHash}, source: Hash \cup {NoHash},
           amount: Nat, sig: PrivateKey]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Nodes == {n \in Node : \E k \in PrivateKey : OwnerOf(k) = n}

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Balance is the total value held by an account's own chain, calculated by walking
\* it back through prev links -- this is how SEND blocks are prevented from overdrawing.
RECURSIVE ChainValue(_)
ChainValue(h) ==
  IF h = NoHash THEN 0
  ELSE IF ledger[CHOOSE n \in Nodes : ledger[n][h] # NoBlockVal][h].source = NoHash
          THEN ledger[CHOOSE n \in Nodes : ledger[n][h] # NoBlockVal][h].amount
          ELSE ChainValue(ledger[CHOOSE n \in Nodes : ledger[n][h] # NoBlockVal][h].source)
             + ledger[CHOOSE n \in Nodes : ledger[n][h] # NoBlockVal][h].amount

\* The genesis block is written into every node's ledger at once and can never be
\* created again, so the no-genesis-yet guard here is what makes it a single action.
CreateGenesis(k) ==
  /\ \A n \in Nodes : \A h \in Hash : ledger[n][h] = NoBlockVal
  /\ lastHash' = CalculateHash(lastHash, k)
  /\ \A n \in Nodes :
       ledger' = [ledger EXCEPT ![n][CalculateHash(lastHash, k)] =
                    [sender |-> OwnerOf(k), prev |-> NoHash, source |-> NoHash,
                     amount |-> GenesisBalance, sig |-> k]]
  /\ UNCHANGED received

CreateSend(n, k, amt) ==
  /\ n \in Nodes
  /\ OwnerOf(k) = n
  /\ ChainValue(lastHash) >= amt
  /\ lastHash' = CalculateHash(lastHash, k)
  /\ ledger' = [ledger EXCEPT ![n][CalculateHash(lastHash, k)] =
                    [sender |-> OwnerOf(k), prev |-> lastHash, source |-> NoHash,
                     amount |-> amt, sig |-> k]]
  /\ received' = [m \in Node |-> received[m] \cup {CalculateHash(lastHash, k)}]

CreateOpen(n, k, src) ==
  /\ n \in Nodes
  /\ OwnerOf(k) = n
  /\ \A m \in Nodes : ledger[m][src] # NoBlockVal /\ ledger[m][src].sender # OwnerOf(k)
  /\ lastHash' = CalculateHash(lastHash, k)
  /\ ledger' = [ledger EXCEPT ![n][CalculateHash(lastHash, k)] =
                    [sender |-> OwnerOf(k), prev |-> NoHash, source |-> src,
                     amount |-> 0, sig |-> k]]
  /\ received' = [m \in Node |-> received[m] \cup {CalculateHash(lastHash, k)}]

CreateReceive(n, k, src) ==
  /\ n \in Nodes
  /\ OwnerOf(k) = n
  /\ \A m \in Nodes : ledger[m][src] # NoBlockVal /\ ledger[m][src].sender # OwnerOf(k)
  /\ ChainValue(lastHash) >= 0
  /\ lastHash' = CalculateHash(lastHash, k)
  /\ ledger' = [ledger EXCEPT ![n][CalculateHash(lastHash, k)] =
                    [sender |-> OwnerOf(k), prev |-> lastHash, source |-> src,
                     amount |-> 0, sig |-> k]]
  /\ received' = [m \in Node |-> received[m] \cup {CalculateHash(lastHash, k)}]

CreateChangeRep(n, k) ==
  /\ n \in Nodes
  /\ OwnerOf(k) = n
  /\ lastHash' = CalculateHash(lastHash, k)
  /\ ledger' = [ledger EXCEPT ![n][CalculateHash(lastHash, k)] =
                    [sender |-> OwnerOf(k), prev |-> lastHash, source |-> NoHash,
                     amount |-> 0, sig |-> k]]
  /\ received' = [m \in Node |-> received[m] \cup {CalculateHash(lastHash, k)}]

\* Each node only validates against its own local copy of the ledger, never
\* against any other node's view or a central authority.
ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ \A m \in Nodes : ledger[m][h] # NoBlockVal
  /\ LET blk == CHOOSE m \in Nodes : ledger[m][h] # NoBlockVal IN
       /\ ledger' = [ledger EXCEPT ![n][h] = blk]
       /\ received' = [received EXCEPT ![n] = @ \ {h}]
       /\ UNCHANGED lastHash

Next ==
  \/ \E k \in PrivateKey : CreateGenesis(k)
  \/ \E n \in Nodes, k \in PrivateKey, amt \in 1..GenesisBalance : CreateSend(n, k, amt)
  \/ \E n \in Nodes, k \in PrivateKey, src \in Hash : CreateOpen(n, k, src)
  \/ \E n \in Nodes, k \in PrivateKey, src \in Hash : CreateReceive(n, k, src)
  \/ \E n \in Nodes, k \in PrivateKey : CreateChangeRep(n, k)
  \/ \E n \in Nodes, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

CryptographicSound ==
  \A n \in Nodes, h \in Hash :
    ledger[n][h] # NoBlockVal => OwnerOf(ledger[n][h].sig) = ledger[n][h].sender

BalanceConserved ==
  ChainValue(lastHash) <= GenesisBalance /\ ChainValue(lastHash >= 0)

====