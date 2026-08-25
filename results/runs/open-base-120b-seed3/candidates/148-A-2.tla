---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* -------------------------------------------------
\* CONSTANTS (to be instantiated in the .cfg file)
\* -------------------------------------------------
CONSTANTS
    Hash,               \* set of all possible block hashes
    NoHashVal,          \* sentinel value meaning “no previous hash”
    PrivateKey,         \* set of private keys
    PublicKey,          \* set of public keys
    Node,               \* set of network nodes
    GenesisBalance,     \* total supply of coins (a Nat)
    NoBlockVal,         \* sentinel value meaning “no block”
    CalculateHash,      \* abstract hash operator (will be overridden)
    NoHash,             \* synonym for NoHashVal
    NoBlock,            \* synonym for NoBlockVal
    PrivateToPublic,    \* mapping PrivateKey -> PublicKey
    NodeToPrivKey       \* mapping Node -> PrivateKey

\* -------------------------------------------------
\* DERIVED CONSTANTS / SYMMETRIC DEFINITIONS
\* -------------------------------------------------
NoHash == NoHashVal
NoBlock == NoBlockVal

\* -------------------------------------------------
\* UNINTERPRETED OPERATORS (cryptographic primitives)
\* -------------------------------------------------
Sign(priv, data) == 
    CHOOSE s \in STRING : TRUE    \* abstract signature

VerifySignature(pub, data, sig) == 
    CHOOSE b \in BOOLEAN : TRUE   \* abstract verification

\* -------------------------------------------------
\* BLOCK RECORD TYPE
\* -------------------------------------------------
Block ==
    [ type         : {"genesis", "send", "receive", "open", "change"},
      prev         : Hash \/ {NoHash},
      account      : PublicKey,
      amount       : Nat,
      recipient    : PublicKey \/ {NoHash},
      source       : Hash \/ {NoHash},
      rep          : PublicKey \/ {NoHash},
      signature    : STRING ]

\* -------------------------------------------------
\* ABSTRACT HASH FUNCTION (overridden by CalculateHashImpl)
\* -------------------------------------------------
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* -------------------------------------------------
\* State Variables
\* -------------------------------------------------
VARIABLES
    LastHash,   \* the most recent block hash (or NoHashVal initially)
    Ledger,     \* [Hash -> Block \/ {NoBlockVal}]
    Received,   \* [Node -> SUBSET Hash]  (blocks awaiting validation)
    BlockInfo   \* [Hash -> Block \/ {NoBlockVal}]  (stores block data once created)

\* -------------------------------------------------
\* Helper Functions
\* -------------------------------------------------
AccountOfNode(n) == PrivateToPublic[NodeToPrivKey[n]]

\* For the purpose of this specification we treat the balance
\* of every account as non‑negative and never exceeding GenesisBalance.
\* A precise recursive balance function is omitted for brevity.
Balance(pk) == 
    IF \E n \in Node : AccountOfNode(n) = pk
    THEN GenesisBalance
    ELSE 0

ValidSignature(b) == VerifySignature(b.account, b, b.signature)

\* -------------------------------------------------
\* Initialization
\* -------------------------------------------------
Init ==
    /\ LastHash = NoHashVal
    /\ Ledger = [h \in Hash |-> NoBlockVal]
    /\ Received = [n \in Node |-> {}]
    /\ BlockInfo = [h \in Hash |-> NoBlockVal]

\* -------------------------------------------------
\* Genesis Block Creation (may occur only once)
\* -------------------------------------------------
Genesis ==
    /\ LastHash = NoHashVal                \* no block has been created yet
    /\ \E n \in Node :
        LET pk      == AccountOfNode(n)
            bData   == << "genesis", NoHashVal, pk, GenesisBalance >>
            newBlk  == [ type      |-> "genesis",
                         prev      |-> NoHashVal,
                         account   |-> pk,
                         amount    |-> GenesisBalance,
                         recipient |-> NoHash,
                         source    |-> NoHash,
                         rep       |-> NoHash,
                         signature |-> Sign(NodeToPrivKey[n], bData) ]
            newHash == CalculateHash(bData, LastHash)
        IN
            /\ newBlk.signature = Sign(NodeToPrivKey[n], bData)   \* signature definition
            /\ LastHash' = newHash
            /\ BlockInfo' = [h \in Hash |-> IF h = newHash THEN newBlk ELSE BlockInfo[h]]
            /\ Ledger' = [h \in Hash |-> IF h = newHash THEN newBlk ELSE Ledger[h]]
            /\ Received' = [m \in Node |-> Received[m] \cup {newHash}]
            /\ UNCHANGED << >>   \* no other variables change

\* -------------------------------------------------
\* Processing a Received Block (validation and ledger update)
\* -------------------------------------------------
Process ==
    /\ \E n \in Node :
        /\ \E h \in Received[n] :
            LET b == BlockInfo[h]
            IN
                /\ b # NoBlockVal
                /\ ValidSignature(b)               \* cryptographic check
                /\ Ledger' = [l \in Hash |-> IF l = h THEN b ELSE Ledger[l]]
                /\ Received' = [m \in Node |-> IF m = n THEN Received[m] \setminus {h} ELSE Received[m]]
                /\ UNCHANGED << LastHash, BlockInfo >>

\* -------------------------------------------------
\* NEXT (all possible actions)
\* -------------------------------------------------
Next == 
    \/ Genesis
    \/ Process

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, BlockInfo>>

\* -------------------------------------------------
\* INVARIANTS
\* -------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \/ {NoHashVal}
    /\ Ledger \in [Hash -> (Block \/ {NoBlockVal})]
    /\ Received \in [Node -> SUBSET Hash]
    /\ BlockInfo \in [Hash -> (Block \/ {NoBlockVal})]

SafetyInvariant ==
    \A h \in Hash :
        IF Ledger[h] = NoBlockVal
        THEN TRUE
        ELSE ValidSignature(Ledger[h])

\* -------------------------------------------------
\* THEOREMS (to be checked by TLC)
\* -------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

\* -------------------------------------------------
\* IMPLEMENTATION OF CalculateHashImpl (finite version for model checking)
\* -------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE   \* nondeterministic hash value within the finite set Hash

====