---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,               \* Set of all possible block hashes
    NoHashVal,          \* Sentinel value for "no hash"
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total supply of coins (a natural number)
    NoBlockVal,         \* Sentinel value for "no block"
    CalculateHash,      \* Abstract hash operator (will be overridden)
    NoHash,             \* Alias for NoHashVal
    NoBlock             \* Alias for NoBlockVal

\* ----------------------------------------------------------------------
\* Derived constants and simple operators
\* ----------------------------------------------------------------------
NoHash == NoHashVal
NoBlock == NoBlockVal

\* Mapping from a private key to its public key (assumed total and injective)
PrivateToPublic \in [PrivateKey -> PublicKey]

\* Mapping from a node to the private key it owns
OwnedKey \in [Node -> PrivateKey]

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Block == [type       : {"genesis","send","open","receive","change"},
          prev       : Hash,
          src        : PublicKey,
          dest       : PublicKey,
          amount     : Nat,
          pubKey     : PublicKey,
          rep        : PublicKey,
          signature  : STRING]

Sig == STRING   \* abstract type for signatures

\* ----------------------------------------------------------------------
\* Abstract cryptographic primitives
\* ----------------------------------------------------------------------
Sign(b, pk) == <<b, pk>>               \* placeholder for a signature
VerifySignature(b) ==
    \E priv \in PrivateKey :
        /\ PrivateToPublic[priv] = b.pubKey
        /\ b.signature = Sign(b, priv)

\* ----------------------------------------------------------------------
\* Hash calculation (will be overridden by the cfg file)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,    \* the most recent block hash (global ordering)
    ledger,      \* [Node -> [Hash -> Block]]  replicated ledger
    received     \* [Node -> SUBSET Hash]      blocks known but not yet processed

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Helper to pick a fresh hash
\* ----------------------------------------------------------------------
FreshHash(hset) ==
    CHOOSE h \in Hash :
        /\ h # NoHash
        /\ \A n \in Node : ledger[n][h] = NoBlock
        /\ h \notin hset

\* ----------------------------------------------------------------------
\* Block constructors
\* ----------------------------------------------------------------------
GenesisBlock(node) ==
    LET pk == PrivateToPublic[OwnedKey[node]] IN
    [type       |-> "genesis",
     prev       |-> NoHash,
     src        |-> pk,
     dest       |-> pk,
     amount     |-> GenesisBalance,
     pubKey     |-> pk,
     rep        |-> pk,
     signature  |-> Sign(<<"genesis", pk, GenesisBalance>>, OwnedKey[node])]

SendBlock(node, amt, dstPk, prevH) ==
    LET pk == PrivateToPublic[OwnedKey[node]] IN
    [type       |-> "send",
     prev       |-> prevH,
     src        |-> pk,
     dest       |-> dstPk,
     amount     |-> amt,
     pubKey     |-> pk,
     rep        |-> pk,
     signature  |-> Sign(<<"send", pk, dstPk, amt, prevH>>, OwnedKey[node])]

OpenBlock(node, srcSendHash, srcPk, prevH) ==
    LET pk == PrivateToPublic[OwnedKey[node]] IN
    [type       |-> "open",
     prev       |-> prevH,
     src        |-> srcPk,
     dest       |-> pk,
     amount     |-> 0,
     pubKey     |-> pk,
     rep        |-> pk,
     signature  |-> Sign(<<"open", srcPk, pk, srcSendHash>>, OwnedKey[node])]

ReceiveBlock(node, sendHash, srcPk, prevH) ==
    LET pk == PrivateToPublic[OwnedKey[node]] IN
    [type       |-> "receive",
     prev       |-> prevH,
     src        |-> srcPk,
     dest       |-> pk,
     amount     |-> 0,
     pubKey     |-> pk,
     rep        |-> pk,
     signature  |-> Sign(<<"receive", srcPk, pk, sendHash>>, OwnedKey[node])]

ChangeRepBlock(node, newRepPk, prevH) ==
    LET pk == PrivateToPublic[OwnedKey[node]] IN
    [type       |-> "change",
     prev       |-> prevH,
     src        |-> pk,
     dest       |-> pk,
     amount     |-> 0,
     pubKey     |-> pk,
     rep        |-> newRepPk,
     signature  |-> Sign(<<"change", pk, newRepPk, prevH>>, OwnedKey[node])]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
        LET b == GenesisBlock(n) IN
        LET nh == FreshHash({}) IN
        /\ lastHash' = nh
        /\ ledger' = [m \in Node |-> [h \in Hash |-> IF h = nh THEN b ELSE ledger[m][h]]]
        /\ received' = [m \in Node |-> received[m] \cup {nh}]
        /\ UNCHANGED <<>>

CreateSend ==
    /\ lastHash # NoHash
    /\ \E n \in Node, amt \in Nat, dst \in PublicKey :
        /\ amt <= GenesisBalance    \* (simplified balance check)
        LET prevH == lastHash IN
        LET b == SendBlock(n, amt, dst, prevH) IN
        LET nh == FreshHash({lastHash}) IN
        /\ lastHash' = nh
        /\ ledger' = [m \in Node |-> [h \in Hash |-> IF h = nh THEN b ELSE ledger[m][h]]]
        /\ received' = [m \in Node |-> received[m] \cup {nh}]
        /\ UNCHANGED <<>>

CreateOpen ==
    /\ lastHash # NoHash
    /\ \E n \in Node, srcSend \in Hash, srcPk \in PublicKey :
        LET prevH == lastHash IN
        LET b == OpenBlock(n, srcSend, srcPk, prevH) IN
        LET nh == FreshHash({lastHash}) IN
        /\ lastHash' = nh
        /\ ledger' = [m \in Node |-> [h \in Hash |-> IF h = nh THEN b ELSE ledger[m][h]]]
        /\ received' = [m \in Node |-> received[m] \cup {nh}]
        /\ UNCHANGED <<>>

CreateReceive ==
    /\ lastHash # NoHash
    /\ \E n \in Node, sendH \in Hash, srcPk \in PublicKey :
        LET prevH == lastHash IN
        LET b == ReceiveBlock(n, sendH, srcPk, prevH) IN
        LET nh == FreshHash({lastHash}) IN
        /\ lastHash' = nh
        /\ ledger' = [m \in Node |-> [h \in Hash |-> IF h = nh THEN b ELSE ledger[m][h]]]
        /\ received' = [m \in Node |-> received[m] \cup {nh}]
        /\ UNCHANGED <<>>

CreateChange ==
    /\ lastHash # NoHash
    /\ \E n \in Node, newRep \in PublicKey :
        LET prevH == lastHash IN
        LET b == ChangeRepBlock(n, newRep, prevH) IN
        LET nh == FreshHash({lastHash}) IN
        /\ lastHash' = nh
        /\ ledger' = [m \in Node |-> [h \in Hash |-> IF h = nh THEN b ELSE ledger[m][h]]]
        /\ received' = [m \in Node |-> received[m] \cup {nh}]
        /\ UNCHANGED <<>>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            /\ ledger[n][h] # NoBlock
            => VerifySignature(ledger[n][h])

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

====