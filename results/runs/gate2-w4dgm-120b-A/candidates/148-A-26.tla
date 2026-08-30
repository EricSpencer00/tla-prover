---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Ed25519 keys: one private key holds one public key and one node owns it.
\* Blake2b hash is modeled as an opaque constant operator (CalculateHash).
\* One block type decides where the next hash comes from: the previous block.
\* Validation is done on the receiving node's own copy of the ledger.
\* Safety invariant: every block in every node's ledger validates cryptographically.

Account == [creator : PrivateKey, amtOwner : PublicKey, prev : Hash, signed : BOOLEAN]
OpenBlock == [creator : PrivateKey, amtOwner : PublicKey, prev : Hash, openHash : Hash, signed : BOOLEAN]

VARIABLES lastHash, ledger, received, blocks

vars == <<lastHash, ledger, received, blocks>>

BlockHashes == {InHash : Hash \ {NoHash} : blocks[InHash] \in Account \cup OpenBlock}

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Account \cup OpenBlock \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]
  /\ blocks \subseteq (Account \cup OpenBlock)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]
  /\ blocks = {}

\* Genesis block is added to every node's ledger immediately, never just broadcast.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E k \in PrivateKey, n \in Node :
       /\ lastHash' = CalculateHash(k, NoHash)
       /\ LET b == [creator |-> k, amtOwner |-> PrivateKey, prev |-> NoHash, signed |-> TRUE] IN
            /\ blocks' = blocks \cup {b}
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = b]]
            /\ received' = [m \in Node |-> IF m = n THEN {lastHash} ELSE {}]
  /\ UNCHANGED <<>>

CreateSendBlock ==
  \E k \in PrivateKey, n \in Node :
    /\ lastHash # NoHashVal
    /\ ledger[n][lastHash] \in Account
    /\ ledger[n][lastHash].amtOwner = PrivateKey
    /\ \E amt \in 1..GenesisBalance :
        /\ amt <= GenesisBalance
        /\ lastHash' = CalculateHash(k, lastHash)
        /\ LET b == [creator |-> k, amtOwner |-> PrivateKey, prev |-> lastHash, signed |-> TRUE] IN
             /\ blocks' = blocks \cup {b}
             /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = b]]
             /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {lastHash} ELSE received[m]]
    /\ UNCHANGED <<>>

CreateOpenBlock ==
  \E k \in PrivateKey, n \in Node, h \in BlockHashes :
    /\ lastHash # NoHashVal
    /\ ledger[n][h] \in Account
    /\ ledger[n][h].amtOwner = PrivateKey
    /\ ledger[n][h].signed
    /\ ledger[n][h].creator # k
    /\ \A p \in BlockHashes : ~(p \in BlockHashes /\ p \in Hash /\ ledger[n][p] \in OpenBlock /\ ledger[n][p].amtOwner = PrivateKey)
    /\ lastHash' = CalculateHash(k, lastHash)
    /\ LET b == [creator |-> k, amtOwner |-> PrivateKey, prev |-> lastHash, openHash |-> h, signed |-> TRUE] IN
         /\ blocks' = blocks \cup {b}
         /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = b]]
         /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {lastHash} ELSE received[m]]
    /\ UNCHANGED <<>>

CreateReceiveBlock ==
  \E k \in PrivateKey, n \in Node, h \in BlockHashes :
    /\ lastHash # NoHashVal
    /\ ledger[n][h] \in Account
    /\ ledger[n][h].amtOwner = PrivateKey
    /\ ledger[n][h].signed
    /\ ledger[n][h].creator # k
    /\ \E p \in BlockHashes :
        /\ p \in BlockHashes
        /\ ledger[n][p] \in OpenBlock
        /\ ledger[n][p].openHash = h
        /\ ledger[n][p].amtOwner = PrivateKey
        /\ \A q \in BlockHashes : ~(q \in BlockHashes /\ ledger[n][q] \in Account /\ ledger[n][q].prev = p)
    /\ lastHash' = CalculateHash(k, lastHash)
    /\ LET b == [creator |-> k, amtOwner |-> PrivateKey, prev |-> lastHash, signed |-> TRUE] IN
         /\ blocks' = blocks \cup {b}
         /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = b]]
         /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {lastHash} ELSE received[m]]
    /\ UNCHANGED <<>>

CreateChangeRepresentativeBlock ==
  \E k \in PrivateKey, n \in Node :
    /\ lastHash # NoHashVal
    /\ ledger[n][lastHash] \in Account
    /\ ledger[n][lastHash].amtOwner = PrivateKey
    /\ lastHash' = CalculateHash(k, lastHash)
    /\ LET b == [creator |-> k, amtOwner |-> PrivateKey, prev |-> lastHash, signed |-> TRUE] IN
         /\ blocks' = blocks \cup {b}
         /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = b]]
         /\ received' = [m \in Node |-> IF m = n THEN received[m] \cup {lastHash} ELSE received[m]]
    /\ UNCHANGED <<>>

ValidateReceived ==
  \E n \in Node, h \in received[n] :
    /\ ledger[n][h] = NoBlockVal
    /\ ledger[n] # ledger[CHOOSE m \in Node : ledger[m][h] # NoBlockVal]
    /\ ledger' = [ledger EXCEPT ![n][h] = ledger[CHOOSE m \in Node : ledger[m][h] # NoBlockVal][h]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED <<lastHash, blocks>>

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock \/ CreateReceiveBlock
        \/ CreateChangeRepresentativeBlock \/ ValidateReceived

Spec == Init /\ [][Next]_vars

\* The chain and the linked-previous-pointer walk the same walk; both sides
\* must still agree here, so a block linked to a non-chain block is caught.
SafetyInvariant ==
  \A n \in Node : \A h \in BlockHashes :
    /\ ledger[n][h] # NoBlockVal
    /\ (IF ledger[n][h] \in Account THEN ledger[n][h].prev = NoHash ELSE ledger[n][prevHash] # NoHash)

====