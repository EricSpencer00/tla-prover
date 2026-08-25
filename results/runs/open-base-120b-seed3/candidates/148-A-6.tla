---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(*  CONSTANTS (provided by the model configuration)                       *)
(***************************************************************************)
CONSTANTS
    Hash,            \* set of all possible block hashes
    NoHashVal,       \* sentinel value meaning “no hash”
    PrivateKey,      \* set of private keys
    PublicKey,       \* set of public keys
    Node,            \* set of network nodes
    GenesisBalance,  \* total supply of coins (a natural number)
    NoBlockVal,      \* sentinel value meaning “no block”
    CalculateHash,   \* abstract hash operator (will be overridden)
    NoHash,          \* another sentinel for “no hash” (may coincide with NoHashVal)
    NoBlock          \* another sentinel for “no block” (may coincide with NoBlockVal)

(***************************************************************************)
(*  Additional constants that are useful for the specification             *)
(***************************************************************************)
CONSTANT
    PrivToPub \in [PrivateKey -> PublicKey],
    NodePriv  \in [Node -> PrivateKey]

(***************************************************************************)
(*  Types ----------------------------------------------------------------- *)
(***************************************************************************)
Block ==
    [type    : {"Genesis", "Send", "Open", "Receive", "Change"},
     prev    : Hash \cup {NoHashVal},
     acct    : PublicKey,
     sig     : STRING,
     amount  : Nat,
     dest    : PublicKey,
     src     : Hash,
     rep     : PublicKey]

BlockOrNoBlock == Block \cup {NoBlockVal}

VARIABLES
    lastHash,          \* the hash of the most recently created block (or NoHashVal)
    ledger,            \* [Node -> [Hash -> BlockOrNoBlock]]
    received           \* [Node -> SUBSET Hash]  (blocks awaiting validation)

(***************************************************************************)
(*  Abstract cryptographic primitives                                      *)
(***************************************************************************)
Sign(priv, data) == "signature"               \* abstract placeholder
VerifySignature(pub, data, sig) == TRUE      \* abstract placeholder

(***************************************************************************)
(*  Helper operators -------------------------------------------------------)
(***************************************************************************)
NodePub(n) == PrivToPub[NodePriv[n]]

IsValidSignature(b) ==
    VerifySignature(b.acct, b, b.sig)

ValidateBlock(b) == IsValidSignature(b)        \* additional checks omitted

BlockData(h) == CHOOSE b \in Block : TRUE     \* abstract lookup from hash to block

(***************************************************************************)
(*  Hash calculation (finite‑model friendly version)                      *)
(***************************************************************************)
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

(***************************************************************************)
(*  Initial state ----------------------------------------------------------)
(***************************************************************************)
Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

(***************************************************************************)
(*  Action: create the genesis block (once)                               *)
(***************************************************************************)
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E n \in Node :
        LET pk  == NodePub(n) IN
        LET blk == [type   |-> "Genesis",
                    prev   |-> NoHashVal,
                    acct   |-> pk,
                    sig    |-> Sign(NodePriv[n], <<>>),
                    amount |-> GenesisBalance,
                    dest   |-> NoHashVal,
                    src    |-> NoHashVal,
                    rep    |-> NoHashVal] IN
        LET h == CalculateHashImpl(blk, NoHashVal) IN
        /\ lastHash' = h
        /\ ledger'   = [n2 \in Node |-> [ledger[n2] EXCEPT ![h] = blk]]
        /\ received' = received
        /\ UNCHANGED << >>

(***************************************************************************)
(*  Action: process a received block on a node                            *)
(***************************************************************************)
ProcessReceived ==
    \/ \E n \in Node, h \in received[n] :
        LET blk == BlockData(h) IN
        /\ ValidateBlock(blk)
        /\ ledger'   = [n2 \in Node |-> IF n2 = n
                                  THEN [ledger[n2] EXCEPT ![h] = blk]
                                  ELSE ledger[n2]]
        /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
        /\ UNCHANGED lastHash

(***************************************************************************)
(*  Next-state relation ----------------------------------------------------)
(***************************************************************************)
Next ==
    \/ CreateGenesis
    \/ ProcessReceived

(***************************************************************************)
(*  Specification ----------------------------------------------------------)
(***************************************************************************)
Spec ==
    Init /\ [][Next]_<<lastHash, ledger, received>>

(***************************************************************************)
(*  Invariants -------------------------------------------------------------)
(***************************************************************************)
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> BlockOrNoBlock]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlockVal
            THEN IsValidSignature(ledger[n][h])
            ELSE TRUE

(***************************************************************************)
(*  Exported names ---------------------------------------------------------)
(***************************************************************************)
THEOREM SpecImpliesTypeInvariant == Spec => []TypeInvariant
THEOREM SpecImpliesSafetyInvariant == Spec => []SafetyInvariant

====