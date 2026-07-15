---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,               \* the set of all possible block hashes
    NoHashVal,          \* a distinguished sentinel hash meaning "no hash"
    PrivateKey,         \* the set of all private keys
    PublicKey,          \* the set of all public keys
    Node,               \* the set of all network nodes
    GenesisBalance,     \* the total amount of coins at genesis (a Nat)
    NoBlockVal,         \* a sentinel value meaning "no block"
    CalculateHash,      \* an abstract operator: (data, prevHash) -> Hash
    NoHash,             \* synonym for NoHashVal (for readability)
    NoBlock             \* synonym for NoBlockVal (for readability)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

Block == [type          : BlockType,
          hash          : Hash,
          prevHash      : Hash,
          account       : PublicKey,
          amount        : Nat,
          recipient     : PublicKey,
          sourceHash    : Hash,
          representative: PublicKey,
          signature     : PublicKey]   \* signature is the public key that signed

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,           \* the most recent block hash known globally
    ledger,             \* [node -> [hash -> Block]]
    received            \* [node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all block hashes that may appear (including the sentinel)
AllHashes == Hash \cup {NoHashVal}

\* The set of all possible blocks (including the sentinel)
AllBlocks == {NoBlockVal} \cup
            { [type          |-> t,
               hash          |-> h,
               prevHash      |-> ph,
               account       |-> a,
               amount        |-> am,
               recipient     |-> r,
               sourceHash    |-> sh,
               representative|-> rep,
               signature     |-> sig]
               : t \in BlockType,
                 h \in Hash,
                 ph \in AllHashes,
                 a \in PublicKey,
                 am \in Nat,
                 r \in PublicKey,
                 sh \in AllHashes,
                 rep \in PublicKey,
                 sig \in PublicKey ] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in AllHashes |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Cryptographic primitives (abstract)
\* ----------------------------------------------------------------------
\* Sign a block: the signature field must equal the public key that owns
\* the account chain.
Sign(b) == b \* (the signature is already a field; we only check equality)

\* Verify a signature: true iff the signature field equals the public key
\* that is expected for the block's account.
VerifySignature(b) ==
    b.signature = b.account

\* ----------------------------------------------------------------------
\* Balance computation (recursive walk of the account chain)
\* ----------------------------------------------------------------------
Balance(node, acc) ==
    LET
        Chain == [h \in Hash |-> ledger[node][h]]
        Rec(b) ==
            IF b = NoBlockVal THEN 0
            ELSE
                CASE b.type = "Genesis"   -> b.amount
                     [] b.type = "Send"    -> -b.amount + Rec(Chain[b.prevHash])
                     [] b.type = "Open"    -> Rec(Chain[b.sourceHash])
                     [] b.type = "Receive" -> b.amount + Rec(Chain[b.prevHash])
                     [] b.type = "ChangeRep" -> Rec(Chain[b.prevHash])
                     [] OTHER              -> 0
    IN
        IF acc \in PublicKey THEN
            IF \E h \in Hash : Chain[h].account = acc /\ Chain[h].type = "Genesis"
            THEN
                LET g == CHOOSE h \in Hash :
                            Chain[h].account = acc /\ Chain[h].type = "Genesis"
                IN Rec(Chain[g])
            ELSE 0
        ELSE 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ \E n \in Node :
        /\ \E pk \in PublicKey :
            /\ \E sk \in PrivateKey :
                /\ sk \in { sk2 \in PrivateKey : sk2 \in Node } \* each node owns a private key
                /\ \A n2 \in Node : ledger[n2][NoHashVal] = NoBlockVal
                /\ lastHash = NoHashVal
                /\ LET gBlock ==
                        [type          |-> "Genesis",
                         hash          |-> h,
                         prevHash      |-> NoHashVal,
                         account       |-> pk,
                         amount        |-> GenesisBalance,
                         recipient     |-> pk,
                         sourceHash    |-> NoHashVal,
                         representative|-> pk,
                         signature     |-> pk]
                   IN
                       /\ h \in Hash
                       /\ gBlock.signature = pk
                       /\ \A n2 \in Node : ledger' = [ledger EXCEPT ![n2][h] = gBlock]
                       /\ lastHash' = h
                       /\ received' = [received EXCEPT ![n] = {}]
    /\ UNCHANGED <<>>

CreateSend(node, amount, recipient) ==
    /\ node \in Node
    /\ amount \in Nat
    /\ recipient \in PublicKey
    /\ Balance(node, ledger[node][lastHash].account) >= amount
    /\ LET prevBlock == ledger[node][lastHash] IN
       LET sBlock ==
            [type          |-> "Send",
             hash          |-> h,
             prevHash      |-> lastHash,
             account       |-> ledger[node][lastHash].account,
             amount        |-> amount,
             recipient     |-> recipient,
             sourceHash    |-> NoHashVal,
             representative|-> ledger[node][lastHash].representative,
             signature     |-> ledger[node][lastHash].account]
       IN
          /\ h \in Hash
          /\ ledger' = [ledger EXCEPT ![node][h] = sBlock]
          /\ lastHash' = h
          /\ received' = [received EXCEPT ![node] = received[node] \cup {h}]
    /\ UNCHANGED <<>>

CreateOpen(node, sourceHash) ==
    /\ node \in Node
    /\ sourceHash \in Hash
    /\ \E b \in AllBlocks :
          b = ledger[node][sourceHash] /\ b.type = "Send" /\ b.recipient = ledger[node][lastHash].account
    /\ LET oBlock ==
            [type          |-> "Open",
             hash          |-> h,
             prevHash      |-> NoHashVal,
             account       |-> ledger[node][sourceHash].recipient,
             amount        |-> ledger[node][sourceHash].amount,
             recipient     |-> ledger[node][sourceHash].recipient,
             sourceHash    |-> sourceHash,
             representative|-> ledger[node][sourceHash].recipient,
             signature     |-> ledger[node][sourceHash].recipient]
       IN
          /\ h \in Hash
          /\ ledger' = [ledger EXCEPT ![node][h] = oBlock]
          /\ lastHash' = h
          /\ received' = [received EXCEPT ![node] = received[node] \cup {h}]
    /\ UNCHANGED <<>>

CreateReceive(node, sourceHash) ==
    /\ node \in Node
    /\ sourceHash \in Hash
    /\ \E b \in AllBlocks :
          b = ledger[node][sourceHash] /\ b.type = "Send" /\ b.recipient = ledger[node][lastHash].account
    /\ LET rBlock ==
            [type          |-> "Receive",
             hash          |-> h,
             prevHash      |-> lastHash,
             account       |-> ledger[node][lastHash].account,
             amount        |-> 0,
             recipient     |-> ledger[node][lastHash].account,
             sourceHash    |-> sourceHash,
             representative|-> ledger[node][lastHash].representative,
             signature     |-> ledger[node][lastHash].account]
       IN
          /\ h \in Hash
          /\ ledger' = [ledger EXCEPT ![node][h] = rBlock]
          /\ lastHash' = h
          /\ received' = [received EXCEPT ![node] = received[node] \cup {h}]
    /\ UNCHANGED <<>>

CreateChangeRep(node, newRep) ==
    /\ node \in Node
    /\ newRep \in PublicKey
    /\ LET prevBlock == ledger[node][lastHash] IN
       LET cBlock ==
            [type          |-> "ChangeRep",
             hash          |-> h,
             prevHash      |-> lastHash,
             account       |-> prevBlock.account,
             amount        |-> 0,
             recipient     |-> prevBlock.account,
             sourceHash    |-> NoHashVal,
             representative|-> newRep,
             signature     |-> prevBlock.account]
       IN
          /\ h \in Hash
          /\ ledger' = [ledger EXCEPT ![node][h] = cBlock]
          /\ lastHash' = h
          /\ received' = [received EXCEPT ![node] = received[node] \cup {h}]
    /\ UNCHANGED <<>>

ProcessReceived(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET b == ledger[node][h] IN
        /\ b # NoBlockVal
        /\ VerifySignature(b)
        /\ (b.type = "Send" => b.amount <= Balance(node, b.account))
        /\ (b.type = "Open" => b.sourceHash \in Hash /\ ledger[node][b.sourceHash].type = "Send")
        /\ (b.type = "Receive" => b.sourceHash \in Hash /\ ledger[node][b.sourceHash].type = "Send")
        /\ ledger' = ledger
        /\ received' = [received EXCEPT ![node] = received[node] \ {h}]
    /\ UNCHANGED <<>>

Next ==
    \/ \E n \in Node, pk \in PublicKey, sk \in PrivateKey :
          CreateGenesis
    \/ \E n \in Node, amt \in Nat, rcpt \in PublicKey :
          CreateSend(n, amt, rcpt)
    \/ \E n \in Node, src \in Hash :
          CreateOpen(n, src)
    \/ \E n \in Node, src \in Hash :
          CreateReceive(n, src)
    \/ \E n \in Node, newRep \in PublicKey :
          CreateChangeRep(n, newRep)
    \/ \E n \in Node :
          ProcessReceived(n)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in AllHashes
    /\ ledger \in [Node -> [Hash -> AllBlocks]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            b = NoBlockVal \/ VerifySignature(b)

\* ----------------------------------------------------------------------
\* THEOREMS (optional, but keep the names required by the cfg)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

====