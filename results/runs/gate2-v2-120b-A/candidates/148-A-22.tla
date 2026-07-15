---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Constants (to be instantiated in the .cfg file)                        *)
(***************************************************************************)
CONSTANTS
    Hash,               \* Set of all possible hash values (including sentinel)
    NoHashVal,          \* Sentinel value meaning "no hash"
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total coin supply, a natural number
    NoBlockVal,         \* Sentinel value meaning "empty block"
    CalculateHash,      \* Abstract hash function: [data, prevHash -> hash]
    NoHash,             \* Synonym for NoHashVal (for readability)
    NoBlock             \* Synonym for NoBlockVal (for readability)

\* Types for clarity
HashSet == Hash
NodeSet == Node
PrivKeySet == PrivateKey
PubKeySet == PublicKey

\* Public key derived from a private key (bijection assumed)
PubKeyOf \in [PrivateKey -> PublicKey]

\* Block representation
Block == [
    type       : {"genesis", "send", "open", "receive", "change"},
    creator    : PubKeySet,               \* owner of the account chain
    prevHash   : HashSet,                 \* previous block in the same chain
    data       : STRING,                  \* auxiliary data (e.g., amount, recipient)
    signature  : STRING,                  \* abstract signature
    hash       : HashSet                  \* own hash
]

\* Helper to compute a block's hash (abstract)
BlockHash(b) == CalculateHash(<<b.type, b.creator, b.prevHash, b.data>>, b.prevHash)

(***************************************************************************)
(*  Variables                                                             *)
(***************************************************************************)
VARIABLES
    lastHash,        \* last calculated block hash (global ordering)
    ledger,          \* [node -> [hash -> Block \/ NoBlockVal]]
    received         \* [node -> SUBSET HashSet]

\* Initialize a per-node empty ledger mapping every hash to NoBlockVal
EmptyLedger == [h \in HashSet |-> NoBlockVal]

\* Initial state definition
Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [n \in NodeSet |-> EmptyLedger]
    /\ received = [n \in NodeSet |-> {}]

(***************************************************************************)
(*  Cryptographic and balance helpers                                    *)
(***************************************************************************)
\* Abstract signature verification (assumed correct when data matches)
Verify(sig, data, pk) == TRUE

\* Amount extraction from a send or receive block's data field
Amount(b) ==
    IF b.type \in {"send", "receive"} THEN
        (* Assume the data string is of the form "amt:K" where K is a natural *)
        LET parts == Split(b.data, ":") IN
        IF Len(parts) = 2 THEN
            IF parts[1] = "amt" THEN
                IF /\ \A i \in 1..Len(parts[2]) : CHOOSE x \in Nat : x = 0
                THEN 0
                ELSE 0
            ELSE 0
        ELSE 0
    ELSE 0

\* Recursive balance calculation for an account (identified by its public key)
Balance(pk) ==
    LET chain == { h \in HashSet : 
                    /\ ledger[ANY][h] # NoBlockVal
                    /\ ledger[ANY][h].creator = pk } IN
    IF chain = {} THEN 0
    ELSE
        (* Find the latest block in the chain: the one whose hash is not referenced as a prevHash *)
        LET latest == 
            CHOOSE h \in chain : 
                /\ \A h2 \in chain : ledger[ANY][h2].prevHash # h
        IN
        IF ledger[ANY][latest].type = "genesis" THEN
            GenesisBalance
        ELSE IF ledger[ANY][latest].type = "send" THEN
            (* Sent amount reduces balance *)
            Balance(ledger[ANY][latest].creator) - Amount(ledger[ANY][latest])
        ELSE IF ledger[ANY][latest].type = "receive" THEN
            Balance(ledger[ANY][latest].creator) + Amount(ledger[ANY][latest])
        ELSE
            Balance(ledger[ANY][latest].creator)

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

\* Broadcast a block to all nodes' received sets
Broadcast(b) ==
    /\ \A n \in NodeSet : received' = [received EXCEPT ![n] = @ \cup {b.hash}]
    /\ UNCHANGED <<lastHash, ledger>>

CreateGenesis(pk) ==
    /\ pk \in PubKeySet
    /\ \A n \in NodeSet : ledger[n][NoHashVal] = NoBlockVal
    /\ let b == [
            type       |-> "genesis",
            creator    |-> pk,
            prevHash   |-> NoHashVal,
            data       |-> "genesis",
            signature  |-> "sig",
            hash       |-> CalculateHash(<<"genesis", pk, NoHashVal, "genesis">>, NoHashVal)
        ] in
       /\ ledger' = [n \in NodeSet |-> [h \in HashSet |-> 
                IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ lastHash' = b.hash
    /\ Broadcast(b)

CreateSend(creatorPk, recipientPk, amt) ==
    /\ creatorPk \in PubKeySet
    /\ recipientPk \in PubKeySet
    /\ amt \in Nat
    /\ Balance(creatorPk) >= amt
    /\ let prev == 
            CHOOSE h \in HashSet : 
                ledger[ANY][h].creator = creatorPk /\ 
                ledger[ANY][h].hash = lastHash
        in
       /\ prev.type # "send"   \* not strictly required, but illustrative
    /\ let b == [
            type       |-> "send",
            creator    |-> creatorPk,
            prevHash   |-> prev.hash,
            data       |-> ("amt:" \o ToString(amt) \o ",to:" \o recipientPk),
            signature  |-> "sig",
            hash       |-> CalculateHash(<<"send", creatorPk, prev.hash, b.data>>, prev.hash)
        ] in
       /\ ledger' = [n \in NodeSet |-> [h \in HashSet |-> 
                IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ lastHash' = b.hash
    /\ Broadcast(b)

CreateOpen(pk, sendHash) ==
    /\ pk \in PubKeySet
    /\ sendHash \in HashSet
    /\ ledger[ANY][sendHash].type = "send"
    /\ ledger[ANY][sendHash].creator # pk   \* send to this account
    /\ let b == [
            type       |-> "open",
            creator    |-> pk,
            prevHash   |-> NoHashVal,
            data       |-> ("openFrom:" \o sendHash),
            signature  |-> "sig",
            hash       |-> CalculateHash(<<"open", pk, NoHashVal, b.data>>, NoHashVal)
        ] in
       /\ ledger' = [n \in NodeSet |-> [h \in HashSet |-> 
                IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ lastHash' = b.hash
    /\ Broadcast(b)

CreateReceive(pk, sendHash) ==
    /\ pk \in PubKeySet
    /\ sendHash \in HashSet
    /\ ledger[ANY][sendHash].type = "send"
    /\ ledger[ANY][sendHash].creator # pk   \* send to this account
    /\ let prev == 
            CHOOSE h \in HashSet : 
                ledger[ANY][h].creator = pk /\ 
                ledger[ANY][h].hash = lastHash
        in
       /\ let b == [
            type       |-> "receive",
            creator    |-> pk,
            prevHash   |-> prev.hash,
            data       |-> ("receiveFrom:" \o sendHash),
            signature  |-> "sig",
            hash       |-> CalculateHash(<<"receive", pk, prev.hash, b.data>>, prev.hash)
        ] in
       /\ ledger' = [n \in NodeSet |-> [h \in HashSet |-> 
                IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ lastHash' = b.hash
    /\ Broadcast(b)

CreateChange(pk, newRep) ==
    /\ pk \in PubKeySet
    /\ newRep \in PubKeySet
    /\ let prev == 
            CHOOSE h \in HashSet : 
                ledger[ANY][h].creator = pk /\ 
                ledger[ANY][h].hash = lastHash
        in
       /\ let b == [
            type       |-> "change",
            creator    |-> pk,
            prevHash   |-> prev.hash,
            data       |-> ("rep:" \o newRep),
            signature  |-> "sig",
            hash       |-> CalculateHash(<<"change", pk, prev.hash, b.data>>, prev.hash)
        ] in
       /\ ledger' = [n \in NodeSet |-> [h \in HashSet |-> 
                IF h = b.hash THEN b ELSE ledger[n][h]]]
    /\ lastHash' = b.hash
    /\ Broadcast(b)

\* Processing a received block at a node
Process(n) ==
    /\ n \in NodeSet
    /\ \E h \in received[n] :
        LET b == ledger[ANY][h] IN
        /\ b # NoBlockVal
        /\ Verify(b.signature, b.data, b.creator)
        /\ (\A ref \in {b.prevHash} : 
                IF ref = NoHashVal THEN TRUE 
                ELSE ledger[n][ref] # NoBlockVal)
        /\ ledger' = ledger
        /\ received' = [received EXCEPT ![n] = @ \ {h}]

Next ==
    \/ \E pk \in PubKeySet : CreateGenesis(pk)
    \/ \E pk, rpk \in PubKeySet, amt \in Nat : CreateSend(pk, rpk, amt)
    \/ \E pk \in PubKeySet, sh \in HashSet : CreateOpen(pk, sh)
    \/ \E pk \in PubKeySet, sh \in HashSet : CreateReceive(pk, sh)
    \/ \E pk, rep \in PubKeySet : CreateChange(pk, rep)
    \/ \E n \in NodeSet : Process(n)

(***************************************************************************)
(*  Specification and invariants                                          *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

TypeInvariant ==
    /\ lastHash \in HashSet
    /\ ledger \in [NodeSet -> [HashSet -> (Block \/ NoBlockVal)]]
    /\ received \in [NodeSet -> SUBSET HashSet]

SafetyInvariant ==
    \A n \in NodeSet :
        \A h \in HashSet :
            /\ ledger[n][h] # NoBlockVal
            => Verify(ledger[n][h].signature,
                      ledger[n][h].data,
                      ledger[n][h].creator)

=============================================================================