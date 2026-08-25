---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,            \* Set of all possible block hashes
    NoHashVal,       \* Sentinel hash value indicating no previous block
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total supply of coins at genesis (a Nat)
    NoBlockVal,      \* Sentinel value representing the absence of a block
    CalculateHash,   \* Abstract hash operator (will be overridden)
    NoHash,          \* Distinct element not in Hash (optional)
    NoBlock          \* Distinct element not in Block (optional)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Block == [
    type          : {"genesis", "send", "open", "receive", "change"},
    prev          : Hash,
    account       : PublicKey,
    recipient     : PublicKey,
    amount        : Nat,
    source        : Hash,
    representative: PublicKey,
    signature     : STRING
]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHashVal)
    ledger,     \* [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    received    \* [Node -> SUBSET Block]  (blocks waiting to be validated)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A concrete (finite) implementation of the abstract hash operator.
\* The .cfg file will substitute CalculateHash with this definition.
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* Signature verification (abstract, but deterministic for model checking)
IsValidSignature(b) ==
    b.signature = ("sig_" \o b.account)

\* The set of all blocks currently stored in a node's ledger
LedgerBlocks(n) ==
    { b \in Block : \E h \in Hash : ledger[n][h] = b }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Block creation actions (broadcast to all nodes)
\* ----------------------------------------------------------------------
CreateBlock(node, b) ==
    LET newHash == CalculateHashImpl(b, lastHash) IN
    /\ newHash \in Hash
    /\ lastHash' = newHash
    /\ ledger' = [n \in Node |-> ledger[n] @@ [newHash |-> b]]
    /\ received' = [n \in Node |-> received[n] \cup {b}]
    /\ UNCHANGED << >>

\* Genesis block creation (can happen only once)
GenesisCreate ==
    \E n \in Node :
        /\ lastHash = NoHashVal
        /\ \E pk \in PublicKey :
            \E sk \in PrivateKey :
                /\ (* assume a mapping from private to public exists *)
                   TRUE
                /\ LET b == [
                        type           |-> "genesis",
                        prev           |-> NoHashVal,
                        account        |-> pk,
                        recipient      |-> NoHash,
                        amount         |-> GenesisBalance,
                        source         |-> NoHash,
                        representative|-> NoHash,
                        signature      |-> ("sig_" \o pk)
                    ] IN
                   CreateBlock(n, b)

\* Send block creation
SendCreate ==
    \E n \in Node :
        \E pk \in PublicKey :
            \E rec \in PublicKey :
                \E amt \in Nat :
                    /\ amt > 0
                    /\ LET b == [
                            type           |-> "send",
                            prev           |-> lastHash,
                            account        |-> pk,
                            recipient      |-> rec,
                            amount         |-> amt,
                            source         |-> NoHash,
                            representative|-> NoHash,
                            signature      |-> ("sig_" \o pk)
                        ] IN
                       CreateBlock(n, b)

\* Open block creation (first block of a new account)
OpenCreate ==
    \E n \in Node :
        \E pk \in PublicKey :
            \E src \in Hash :
                /\ src \in Hash
                /\ LET b == [
                        type           |-> "open",
                        prev           |-> NoHash,
                        account        |-> pk,
                        recipient      |-> NoHash,
                        amount         |-> 0,
                        source         |-> src,
                        representative|-> NoHash,
                        signature      |-> ("sig_" \o pk)
                    ] IN
                       CreateBlock(n, b)

\* Receive block creation
ReceiveCreate ==
    \E n \in Node :
        \E pk \in PublicKey :
            \E src \in Hash :
                \E amt \in Nat :
                    /\ amt > 0
                    /\ LET b == [
                            type           |-> "receive",
                            prev           |-> lastHash,
                            account        |-> pk,
                            recipient      |-> NoHash,
                            amount         |-> amt,
                            source         |-> src,
                            representative|-> NoHash,
                            signature      |-> ("sig_" \o pk)
                        ] IN
                       CreateBlock(n, b)

\* Change representative block creation
ChangeCreate ==
    \E n \in Node :
        \E pk \in PublicKey :
            \E rep \in PublicKey :
                LET b == [
                        type           |-> "change",
                        prev           |-> lastHash,
                        account        |-> pk,
                        recipient      |-> NoHash,
                        amount         |-> 0,
                        source         |-> NoHash,
                        representative|-> rep,
                        signature      |-> ("sig_" \o pk)
                    ] IN
                CreateBlock(n, b)

\* ----------------------------------------------------------------------
\* Processing (validation) of a received block by a node
\* ----------------------------------------------------------------------
ProcessBlock(node) ==
    \E b \in received[node] :
        /\ IsValidSignature(b)
        /\ (* basic structural checks, e.g., referenced hashes exist *)
           (b.prev = NoHashVal) \/ (\E h \in Hash : ledger[node][h] # NoBlockVal)
        /\ ledger' = [n \in Node |-> 
                        IF n = node 
                        THEN ledger[n] @@ [lastHash |-> b] 
                        ELSE ledger[n]]
        /\ received' = [n \in Node |-> 
                        IF n = node 
                        THEN received[n] \ {b} 
                        ELSE received[n]]
        /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ GenesisCreate
    \/ SendCreate
    \/ OpenCreate
    \/ ReceiveCreate
    \/ ChangeCreate
    \/ \E n \in Node : ProcessBlock(n)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Block]

\* ----------------------------------------------------------------------
\* Safety invariant (all stored blocks have a valid signature)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            (ledger[n][h] # NoBlockVal) => IsValidSignature(ledger[n][h])

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====