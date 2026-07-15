---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,          \* Universe of block hashes
    NoHashVal,     \* Sentinel hash value meaning "no previous block"
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total supply of coins
    NoBlockVal,    \* Sentinel for the empty block
    CalculateHash, \* Abstract hash function: CalculateHash(prevHash, data) \in Hash
    NoHash,        \* Alias for NoHashVal (required by cfg)
    NoBlock        \* Alias for NoBlockVal (required by cfg)

\*--------------------------------------------------------------------
\* Data structures
\*--------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

Block == [
    type        : BlockType,
    hash        : Hash,
    prev        : Hash,
    source      : PublicKey,
    destination : PublicKey,
    amount      : Nat,
    signature   : PrivateKey
]

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES
    lastHash,          \* The hash of the most recent block created
    ledger,            \* [node \in Node |-> [h \in Hash |-> NoBlockVal]]
    received           \* [node \in Node |-> SUBSET Hash]

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
\* The set of all possible blocks (used only for typing)
AllBlocks == { b \in Block : b.hash \in Hash }

\* Mapping from a private key to its public key (bijection for simplicity)
Pub(priv) == 
    CHOOSE pub \in PublicKey : pub = priv

\* Balance of an account (public key) as derived from its chain
Balance(account, l) ==
    LET chain == 
        { h \in Hash : 
            \A node \in Node : 
                ledger[node][h] # NoBlockVal /\ 
                ledger[node][h].source = account }
    IN
        IF chain = {} THEN 0 ELSE
        \* Find the most recent block in the chain (by following prev links)
        LET latest == 
            CHOOSE h \in chain :
                \A other \in chain : ledger[Node][other].prev # h
        IN
            CASE
                ledger[Node][latest].type = "Genesis"   -> GenesisBalance
                ledger[Node][latest].type = "Send"      -> Balance(account, l) - ledger[Node][latest].amount
                ledger[Node][latest].type = "Receive"  -> Balance(account, l) + ledger[Node][latest].amount
                OTHER                                   -> Balance(account, l)

\*--------------------------------------------------------------------
\* Type checking
\*--------------------------------------------------------------------
TypeOK ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ \A n \in Node :
        \A h \in Hash :
            (ledger[n][h] # NoBlockVal) => ledger[n][h] \in Block

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\*--------------------------------------------------------------------
\* Signature checking (abstract)
\*--------------------------------------------------------------------
ValidSig(b) ==
    b.signature = Pub(b.source)

\*--------------------------------------------------------------------
\* Block creation actions
\*--------------------------------------------------------------------
Genesis ==
    /\ \E priv \in PrivateKey :
        LET pub == Pub(priv) IN
        /\ lastHash = NoHashVal
        /\ \A n \in Node :
            ledger[n][hash] = [
                type        |-> "Genesis",
                hash        |-> hash,
                prev        |-> NoHashVal,
                source      |-> pub,
                destination |-> pub,
                amount      |-> GenesisBalance,
                signature   |-> priv
            ]
        /\ lastHash' = hash
        /\ received' = [n \in Node |-> {}]
  \* hash is freshly calculated
    /\ hash \in Hash \ {NoHashVal}
    /\ hash = CalculateHash(NoHashVal, "Genesis" \o "0" \o pub \o pub \o GenesisBalance)
    /\ UNCHANGED << >>

Send(sndNode, priv, dstPub, amt) ==
    /\ sndNode \in Node
    /\ priv \in PrivateKey
    /\ Pub(priv) = srcPub
    /\ srcPub \in PublicKey
    /\ dstPub \in PublicKey
    /\ amt \in Nat
    /\ Balance(srcPub, ledger) >= amt
    /\ \E prevHash \in Hash :
        ledger[sndNode][prevHash] # NoBlockVal /\
        ledger[sndNode][prevHash].source = srcPub /\
        ledger[sndNode][prevHash].type # "Send"
    /\ hash \in Hash \ {NoHashVal}
    /\ hash = CalculateHash(prevHash, "Send" \o srcPub \o dstPub \o amt)
    /\ \A n \in Node :
        ledger[n][hash] = [
            type        |-> "Send",
            hash        |-> hash,
            prev        |-> prevHash,
            source      |-> srcPub,
            destination |-> dstPub,
            amount      |-> amt,
            signature   |-> priv
        ]
    /\ lastHash' = hash
    /\ received' = [n \in Node |-> received[n] \cup {hash}]
    /\ UNCHANGED << >>

Open(node, priv, sendHash) ==
    /\ node \in Node
    /\ priv \in PrivateKey
    /\ Pub(priv) = myPub
    /\ sendHash \in Hash
    /\ \E b \in Block :
        b = ledger[node][sendHash] /\ b.type = "Send" /\ b.destination = myPub
    /\ hash \in Hash \ {NoHashVal}
    /\ hash = CalculateHash(sendHash, "Open" \o myPub)
    /\ \A n \in Node :
        ledger[n][hash] = [
            type        |-> "Open",
            hash        |-> hash,
            prev        |-> sendHash,
            source      |-> myPub,
            destination |-> myPub,
            amount      |-> 0,
            signature   |-> priv
        ]
    /\ lastHash' = hash
    /\ received' = [n \in Node |-> received[n] \cup {hash}]
    /\ UNCHANGED << >>

Receive(node, priv, sendHash, prevHash) ==
    /\ node \in Node
    /\ priv \in PrivateKey
    /\ Pub(priv) = myPub
    /\ sendHash \in Hash
    /\ prevHash \in Hash
    /\ \E s \in Block :
        s = ledger[node][sendHash] /\ s.type = "Send" /\ s.destination = myPub
    /\ \E p \in Block :
        p = ledger[node][prevHash] /\ p.type \in {"Open", "Receive", "Change"} /\ p.source = myPub
    /\ hash \in Hash \ {NoHashVal}
    /\ hash = CalculateHash(prevHash, "Receive" \o myPub \o sendHash)
    /\ \A n \in Node :
        ledger[n][hash] = [
            type        |-> "Receive",
            hash        |-> hash,
            prev        |-> prevHash,
            source      |-> myPub,
            destination |-> myPub,
            amount      |-> ledger[node][sendHash].amount,
            signature   |-> priv
        ]
    /\ lastHash' = hash
    /\ received' = [n \in Node |-> received[n] \cup {hash}]
    /\ UNCHANGED << >>

Change(node, priv, prevHash) ==
    /\ node \in Node
    /\ priv \in PrivateKey
    /\ Pub(priv) = myPub
    /\ prevHash \in Hash
    /\ \E p \in Block :
        p = ledger[node][prevHash] /\ p.source = myPub
    /\ hash \in Hash \ {NoHashVal}
    /\ hash = CalculateHash(prevHash, "Change" \o myPub)
    /\ \A n \in Node :
        ledger[n][hash] = [
            type        |-> "Change",
            hash        |-> hash,
            prev        |-> prevHash,
            source      |-> myPub,
            destination |-> myPub,
            amount      |-> 0,
            signature   |-> priv
        ]
    /\ lastHash' = hash
    /\ received' = [n \in Node |-> received[n] \cup {hash}]
    /\ UNCHANGED << >>

\*--------------------------------------------------------------------
\* Processing of received blocks
\*--------------------------------------------------------------------
Process(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET b == ledger[node][h] IN
        /\ b # NoBlockVal
        /\ ValidSig(b)
        /\ (b.type = "Send" => 
                /\ b.prev \in Hash
                /\ ledger[node][b.prev] # NoBlockVal
                /\ Balance(b.source, ledger) >= b.amount)
        /\ (b.type = "Open" => 
                /\ b.prev \in Hash
                /\ ledger[node][b.prev].type = "Send"
                /\ ledger[node][b.prev].destination = b.source)
        /\ (b.type = "Receive" => 
                /\ b.prev \in Hash
                /\ ledger[node][b.prev] # NoBlockVal
                /\ ledger[node][b.prev].source = b.source
                /\ b.destination = b.source
                /\ ledger[node][b.prev].type # "Receive")
        /\ ledger[node][h] = b
        /\ received' = [n \in Node |-> IF n = node THEN received[n] \ {h} ELSE received[n]]
        /\ UNCHANGED <<lastHash, ledger>>

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
    \/ \E priv \in PrivateKey : Genesis
    \/ \E sndNode \in Node, priv \in PrivateKey, dstPub \in PublicKey, amt \in Nat : 
        Send(sndNode, priv, dstPub, amt)
    \/ \E node \in Node, priv \in PrivateKey, sendHash \in Hash :
        Open(node, priv, sendHash)
    \/ \E node \in Node, priv \in PrivateKey, sendHash \in Hash, prevHash \in Hash :
        Receive(node, priv, sendHash, prevHash)
    \/ \E node \in Node, priv \in PrivateKey, prevHash \in Hash :
        Change(node, priv, prevHash)
    \/ \E node \in Node : Process(node)

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeInvariant == TypeOK

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            /\ ledger[n][h] # NoBlockVal => ValidSig(ledger[n][h])
            /\ ledger[n][h].type = "Send" => ledger[n][h].amount <= Balance(ledger[n][h].source, ledger)

\*--------------------------------------------------------------------
\* THEOREMS (optional, but included for completeness)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

====