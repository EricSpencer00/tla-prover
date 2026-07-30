---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin Hash
ASSUME NoHash \notin Hash

OwnedBy == [n \in Node |-> CHOOSE k \in PrivateKey : n \in NoHash[k]]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

BlockType == {"genesis", "send", "open", "receive", "change"}
BlockAttributes == [type: BlockType, owner: PublicKey, prev: Hash \cup {NoHash}, target: PublicKey \cup {NoHash}, amt: 0 .. GenesisBalance, sig: PrivateKey]
BlockAtHash == [h \in Hash |-> BlockAttributes \cup {NoBlockVal}]
ChainAtNode == [n \in Node |-> BlockAttributes \cup {NoBlockVal}]
LedgerAtNode == [h \in Hash |-> ChainAtNode \cup {NoBlockVal}]
ReceivedAtNode == [n \in Node |-> SUBSET Hash]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in LedgerAtNode
  /\ received \in ReceivedAtNode

\* A node's balance is the sum of all amounts sent to its account chain.
Balance(n, h) ==
  IF h = NoHash
  THEN 0
  ELSE
    LET blk == ledger[n][h]
    IN IF blk = NoBlockVal
       THEN 0
       ELSE IF blk.target = OwnedBy[n]
            THEN Balance(n, blk.prev) + blk.amt
            ELSE Balance(n, blk.prev)

Available(n) == Balance(n, lastHash)

\* Ed25519-style signatures: a block may only reside in a node's ledger if the
\* signature sits on the private key that owns that account's chain.
SignatureValid(n, h) ==
  \/ ledger[n][h] = NoBlockVal
  \/ ledger[n][h].sig \in NoHash[OwnedBy[n]]

\* Every received block must resolve to a valid signature upon acceptance.
SignedChain ==
  \A n \in Node, h \in Hash : SignatureValid(n, h)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E k \in PrivateKey :
       /\ lastHash' = CalculateHash([type |-> "genesis", owner |-> NoHash[k], prev |-> NoHash, target |-> NoHash, amt |-> GenesisBalance, sig |-> k])
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [type |-> "genesis", owner |-> NoHash[k], prev |-> NoHash, target |-> NoHash, amt |-> GenesisBalance, sig |-> k]]]
  /\ received' = [n \in Node |-> received[n]]
  /\ UNCHANGED <<Hash>>

CreateSendBlock(n) ==
  /\ lastHash \in Hash
  /\ \E k \in PrivateKey :
       \E t \in Node :
         /\ k \in NoHash[n]
         /\ t # n
         /\ \E amt \in 1 .. Available(n) :
              /\ lastHash' = CalculateHash([type |-> "send", owner |-> NoHash[k], prev |-> lastHash, target |-> t, amt |-> amt, sig |-> k])
              /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "send", owner |-> NoHash[k], prev |-> lastHash, target |-> t, amt |-> amt, sig |-> k]]]
              /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]
  /\ UNCHANGED NoHash

CreateOpenBlock(n) ==
  /\ \E k \in PrivateKey :
       \E h \in Hash :
         /\ k \in NoHash[n]
         /\ ledger[n][h] # NoBlockVal
         /\ ledger[n][h].type = "send"
         /\ ledger[n][h].target = n
         /\ ledger[n][h].prev = NoHash
         /\ lastHash' = CalculateHash([type |-> "open", owner |-> NoHash[k], prev |-> NoHash, target |-> n, amt |-> ledger[n][h].amt, sig |-> k])
         /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "open", owner |-> NoHash[k], prev |-> NoHash, target |-> n, amt |-> ledger[n][h].amt, sig |-> k]]]
         /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]
  /\ UNCHANGED NoHash

CreateReceiveBlock(n) ==
  /\ \E k \in PrivateKey :
       \E h \in Hash :
         /\ k \in NoHash[n]
         /\ ledger[n][h] # NoBlockVal
         /\ ledger[n][h].type = "send"
         /\ ledger[n][h].target = n
         /\ ledger[n][h].prev \notin {NoHash, NoHashVal}
         /\ lastHash' = CalculateHash([type |-> "receive", owner |-> NoHash[k], prev |-> NoHash, target |-> n, amt |-> ledger[n][h].amt, sig |-> k])
         /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "receive", owner |-> NoHash[k], prev |-> NoHash, target |-> n, amt |-> ledger[n][h].amt, sig |-> k]]]
         /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]
  /\ UNCHANGED NoHash

CreateChangeRepresentativeBlock(n) ==
  /\ \E k \in PrivateKey :
       /\ k \in NoHash[n]
       /\ lastHash' = CalculateHash([type |-> "change", owner |-> NoHash[k], prev |-> lastHash, target |-> NoHash, amt |-> 0, sig |-> k])
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "change", owner |-> NoHash[k], prev |-> lastHash, target |-> NoHash, amt |-> 0, sig |-> k]]]
       /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]
  /\ UNCHANGED NoHash

ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ SignatureValid(n, h)
  /\ ledger' = [ledger EXCEPT ![n][h] = NoBlockVal]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ CreateGenesisBlock
  \/ \E n \in Node : CreateSendBlock(n) \/ CreateOpenBlock(n) \/ CreateReceiveBlock(n) \/ CreateChangeRepresentativeBlock(n)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK
SafetyInvariant == SignedChain
====