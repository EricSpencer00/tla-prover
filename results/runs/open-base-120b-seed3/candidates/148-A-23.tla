---- MODULE Nano ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Hash, NoHashVal,               \* set of possible hash values, sentinel for “no hash”
    PrivateKey, PublicKey,         \* key spaces
    Node,                          \* set of network nodes
    GenesisBalance,                \* total supply at genesis
    NoBlockVal,                    \* sentinel for “no block”
    CalculateHash,                 \* abstract hash operator (overridden by cfg)
    NoHash, NoBlock                \* additional sentinels

\* ----------------------------------------------------------------------
\* Abstract mappings and cryptographic primitives (to be instantiated in .cfg)
\* ----------------------------------------------------------------------
PubOfPriv \in [PrivateKey -> PublicKey]
NodeKey   \in [Node -> PrivateKey]           \* each node owns a private key
Sign      \in [PrivateKey \X STRING -> Sig] \* signing operation
VerifySig \in [PublicKey \X STRING \X Sig -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Concrete hash implementation used by the model checker (overridden)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Block definition and sentinels
\* ----------------------------------------------------------------------
Block ==
    [type    : {"genesis","send","open","receive","change"},
     prev    : Hash,
     acc     : PublicKey,      \* account that owns the chain
     dest    : PublicKey,      \* destination (or new representative)
     amount  : Nat,
     sig     : Sig]

NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Helper abstract predicates (used in action pre‑conditions)
\* ----------------------------------------------------------------------
BlockValid(b) ==
    VerifySig(b.acc, ToString(b), b.sig)

ChainTip(pub, l) ==
    CHOOSE h \in Hash :
        /\ l[ANY][h] # NoBlock
        /\ l[ANY][h].acc = pub
        /\ \A h2 \in Hash :
               (l[ANY][h2] # NoBlock /\ l[ANY][h2].acc = pub /\ l[ANY][h2].prev = h) => FALSE

Balance(pub, l) ==
    CHOOSE b \in Nat : TRUE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
GenesisAction ==
    /\ lastHash = NoHashVal
    /\ \E n \in Node :
        LET priv == NodeKey[n]
            pub  == PubOfPriv[priv]
            b    == [type   |-> "genesis",
                    prev   |-> NoHash,
                    acc    |-> pub,
                    dest   |-> pub,
                    amount |-> GenesisBalance,
                    sig    |-> Sign[priv, "genesis"]]
            h    == CalculateHashImpl(b, NoHash)
        IN
            /\ lastHash' = h
            /\ ledger' = [m \in Node |-> ledger[m] \oplus [h |-> b]]
            /\ received' = [m \in Node |-> {}]
            /\ UNCHANGED <<>>

SendAction ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node :
        LET priv == NodeKey[n]
            pub  == PubOfPriv[priv]
            tip  == ChainTip(pub, ledger[n])
            amt  \in Nat
            destPub \in PublicKey
        IN
            /\ amt > 0
            /\ Balance(pub, ledger[n]) >= amt
            /\ b == [type   |-> "send",
                    prev   |-> tip,
                    acc    |-> pub,
                    dest   |-> destPub,
                    amount |-> amt,
                    sig    |-> Sign[priv, "send"]]
            /\ h == CalculateHashImpl(b, tip)
            /\ lastHash' = h
            /\ ledger' = [m \in Node |-> ledger[m] \oplus [h |-> b]]
            /\ received' = [m \in Node |-> received[m] \cup {h}]
            /\ UNCHANGED <<>>

OpenAction ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, sendHash \in Hash :
        LET priv == NodeKey[n]
            pub  == PubOfPriv[priv]
            sendBlock == CHOOSE m \in Node : ledger[m][sendHash] # NoBlock
        IN
            /\ sendBlock.type = "send"
            /\ sendBlock.dest = pub
            /\ b == [type   |-> "open",
                    prev   |-> NoHash,
                    acc    |-> pub,
                    dest   |-> pub,
                    amount |-> sendBlock.amount,
                    sig    |-> Sign[priv, "open"]]
            /\ h == CalculateHashImpl(b, NoHash)
            /\ lastHash' = h
            /\ ledger' = [m \in Node |-> ledger[m] \oplus [h |-> b]]
            /\ received' = [m \in Node |-> received[m] \cup {h}]
            /\ UNCHANGED <<>>

ReceiveAction ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, sendHash \in Hash :
        LET priv == NodeKey[n]
            pub  == PubOfPriv[priv]
            tip  == ChainTip(pub, ledger[n])
            sendBlock == CHOOSE m \in Node : ledger[m][sendHash] # NoBlock
        IN
            /\ sendBlock.type = "send"
            /\ sendBlock.dest = pub
            /\ b == [type   |-> "receive",
                    prev   |-> tip,
                    acc    |-> pub,
                    dest   |-> pub,
                    amount |-> sendBlock.amount,
                    sig    |-> Sign[priv, "receive"]]
            /\ h == CalculateHashImpl(b, tip)
            /\ lastHash' = h
            /\ ledger' = [m \in Node |-> ledger[m] \oplus [h |-> b]]
            /\ received' = [m \in Node |-> received[m] \cup {h}]
            /\ UNCHANGED <<>>

ChangeAction ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, newRep \in PublicKey :
        LET priv == NodeKey[n]
            pub  == PubOfPriv[priv]
            tip  == ChainTip(pub, ledger[n])
            b == [type   |-> "change",
                  prev   |-> tip,
                  acc    |-> pub,
                  dest   |-> newRep,
                  amount |-> 0,
                  sig    |-> Sign[priv, "change"]]
            h == CalculateHashImpl(b, tip)
        IN
            /\ lastHash' = h
            /\ ledger' = [m \in Node |-> ledger[m] \oplus [h |-> b]]
            /\ received' = [m \in Node |-> received[m] \cup {h}]
            /\ UNCHANGED <<>>

ProcessAction ==
    /\ \E n \in Node, h \in received[n] :
        LET b == ledger[n][h]
        IN
            /\ b # NoBlock
            /\ BlockValid(b)
            /\ received' = [m \in Node |
                              IF m = n THEN received[m] \ {h}
                              ELSE received[m]]
            /\ UNCHANGED <<lastHash, ledger>>

Next ==
    \/ GenesisAction
    \/ SendAction
    \/ OpenAction
    \/ ReceiveAction
    \/ ChangeAction
    \/ ProcessAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHashVal}
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node : \A h \in Hash :
        IF ledger[n][h] # NoBlock THEN BlockValid(ledger[n][h]) ELSE TRUE

====