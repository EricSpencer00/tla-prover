---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,               \* universe of block hashes
    NoHashVal,          \* sentinel hash meaning "no hash"
    PrivateKey,         \* set of private keys
    PublicKey,          \* set of public keys
    Node,               \* set of network nodes
    GenesisBalance,     \* total coin supply (a natural number)
    NoBlockVal,         \* sentinel for "no block"
    CalculateHash,      \* abstract hash function: [data, prevHash -> Hash]
    NoHash,             \* synonym for NoHashVal (for readability)
    NoBlock             \* synonym for NoBlockVal

\* ----------------------------------------------------------------------
\* Types for readability
\* ----------------------------------------------------------------------
BlockType == {"genesis", "send", "open", "receive", "change"}

\* ----------------------------------------------------------------------
\* Record representing a block (some fields are only meaningful for certain types)
\* ----------------------------------------------------------------------
Block == [
    type          : BlockType,
    creator       : PublicKey,
    prevHash      : Hash,
    target        : PublicKey,   \* for send/open/receive (the account that receives)
    amount        : Nat,
    changedRep    : PublicKey,   \* for change blocks (new representative)
    signature     : PRIVATE_KEY
]

\* ----------------------------------------------------------------------
\* Function to retrieve the public key that owns a given private key
\* (provided externally via the cfg file as a function PrivateToPublic)
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,               \* the most recent block hash known to the system
    ledger,                 \* [node \in Node -> [h \in Hash -> Block UNION {NoBlockVal}]]
    received                \* [node \in Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
IsGenesis(b) == b.type = "genesis"
IsSend(b)    == b.type = "send"
IsOpen(b)    == b.type = "open"
IsReceive(b) == b.type = "receive"
IsChange(b)  == b.type = "change"

\* ----------------------------------------------------------------------
\* Balance computation (recursive walk of the account chain)
\* For simplicity we assume that a missing block contributes 0.
\* ----------------------------------------------------------------------
Balance(node) ==
    LET h == lastHash IN
    BalanceFromHash(node, h)

BalanceFromHash(node, h) ==
    IF h = NoHashVal THEN 0
    ELSE
        LET b == ledger[node][h] IN
        IF b = NoBlockVal THEN 0
        ELSE
            CASE b.type = "genesis"   -> b.amount
               [] b.type = "send"    -> BalanceFromHash(node, b.prevHash) - b.amount
               [] b.type = "receive"-> BalanceFromHash(node, b.prevHash) + b.amount
               [] b.type = "open"    -> b.amount
               [] b.type = "change"  -> BalanceFromHash(node, b.prevHash)
               [] OTHER              -> BalanceFromHash(node, b.prevHash)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Action: CreateGenesis (only once)
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E pk \in PublicKey :
        LET b == [
                type      |-> "genesis",
                creator   |-> pk,
                prevHash  |-> NoHashVal,
                target    |-> pk,
                amount    |-> GenesisBalance,
                changedRep|-> pk,
                signature |-> ( \E sk \in PrivateKey : /\ PrivateToPublic[sk] = pk /\ sk)   \* placeholder: any matching private key
            ] IN
        /\ b.signature \in PrivateKey
        /\ \A n \in Node : ledger[n][CalculateHash([b], NoHashVal)] = b
        /\ lastHash' = CalculateHash([b], NoHashVal)
        /\ UNCHANGED <<ledger, received>>

\* ----------------------------------------------------------------------
\* Action: CreateSend
\* ----------------------------------------------------------------------
CreateSend ==
    \E sender \in Node :
        \E pk \in PublicKey :
            /\ PrivateToPublic[ PrivateKeyOfNode[sender] ] = pk
            /\ Balance(sender) >= 1    \* assume sending at least 1 unit
            /\ \E recipient \in PublicKey :
                LET b == [
                        type      |-> "send",
                        creator   |-> pk,
                        prevHash  |-> lastHash,
                        target    |-> recipient,
                        amount    |-> 1,
                        changedRep|-> pk,
                        signature |-> PrivateKeyOfNode[sender]
                    ] IN
                /\ b.signature = PrivateKeyOfNode[sender]
                /\ lastHash' = CalculateHash([b], lastHash)
                /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![lastHash'] = b]
                /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]
                /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: CreateOpen
\* ----------------------------------------------------------------------
CreateOpen ==
    \E node \in Node :
        \E openPk \in PublicKey :
            /\ PrivateToPublic[ PrivateKeyOfNode[node] ] = openPk
            /\ \E sendHash \in received[node] :
                LET sb == ledger[node][sendHash] IN
                /\ IsSend(sb)
                /\ sb.target = openPk
                LET b == [
                        type      |-> "open",
                        creator   |-> openPk,
                        prevHash  |-> NoHashVal,
                        target    |-> openPk,
                        amount    |-> sb.amount,
                        changedRep|-> openPk,
                        signature |-> PrivateKeyOfNode[node]
                    ] IN
                /\ b.signature = PrivateKeyOfNode[node]
                /\ lastHash' = CalculateHash([b], NoHashVal)
                /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![lastHash'] = b]
                /\ received' = [n \in Node |-> received[n] \ {sendHash}]
                /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: CreateReceive
\* ----------------------------------------------------------------------
CreateReceive ==
    \E node \in Node :
        \E recvPk \in PublicKey :
            /\ PrivateToPublic[ PrivateKeyOfNode[node] ] = recvPk
            /\ \E sendHash \in received[node] :
                LET sb == ledger[node][sendHash] IN
                /\ IsSend(sb)
                /\ sb.target = recvPk
                LET b == [
                        type      |-> "receive",
                        creator   |-> recvPk,
                        prevHash  |-> lastHash,
                        target    |-> recvPk,
                        amount    |-> sb.amount,
                        changedRep|-> recvPk,
                        signature |-> PrivateKeyOfNode[node]
                    ] IN
                /\ b.signature = PrivateKeyOfNode[node]
                /\ lastHash' = CalculateHash([b], lastHash)
                /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![lastHash'] = b]
                /\ received' = [n \in Node |-> received[n] \ {sendHash}]
                /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: CreateChangeRepresentative
\* ----------------------------------------------------------------------
CreateChange ==
    \E node \in Node :
        \E pk \in PublicKey :
            /\ PrivateToPublic[ PrivateKeyOfNode[node] ] = pk
            LET b == [
                    type      |-> "change",
                    creator   |-> pk,
                    prevHash  |-> lastHash,
                    target    |-> pk,
                    amount    |-> 0,
                    changedRep|-> pk,
                    signature |-> PrivateKeyOfNode[node]
                ] IN
            /\ b.signature = PrivateKeyOfNode[node]
            /\ lastHash' = CalculateHash([b], lastHash)
            /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![lastHash'] = b]
            /\ UNCHANGED <<received>>

\* ----------------------------------------------------------------------
\* Action: ProcessReceived (generic validation and addition)
\* ----------------------------------------------------------------------
ProcessReceived ==
    \E node \in Node :
        \E h \in received[node] :
            LET b == ledger[node][h] IN
            /\ b # NoBlockVal
            /\ b.signature \in PrivateKey
            /\ PrivateToPublic[ b.signature ] = b.creator
            /\ (b.prevHash = NoHashVal \/ ledger[node][b.prevHash] # NoBlockVal)
            /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![h] = b]
            /\ received' = [n \in Node |-> IF n = node THEN received[n] \ {h} ELSE received[n]]
            /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures variables stay within declared domains)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block UNION {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic validity of every stored block)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node : \A h \in Hash :
        LET b == ledger[n][h] IN
        IF b = NoBlockVal THEN TRUE
        ELSE b.signature \in PrivateKey /\ PrivateToPublic[b.signature] = b.creator

\* ----------------------------------------------------------------------
\* (Optional) balance invariant – not required by the .cfg but useful
\* ----------------------------------------------------------------------
BalanceInvariant ==
    \A n \in Node : Balance(n) >= 0 /\ Balance(n) <= GenesisBalance

=============================================================================