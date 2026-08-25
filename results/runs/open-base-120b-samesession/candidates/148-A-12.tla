---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* -----------------------------------------------------------------
\* CONSTANTS (to be supplied by the model checker configuration)
\* -----------------------------------------------------------------
CONSTANTS
    Hash,               \* the set of all possible block hashes
    NoHashVal,          \* a distinguished value representing “no hash”
    PrivateKey,         \* the set of private keys
    PublicKey,          \* the set of public keys
    Node,               \* the set of network nodes
    GenesisBalance,     \* total amount of coins at genesis (a Nat)
    NoBlockVal,         \* a distinguished value representing “no block”
    CalculateHash,      \* abstract hash calculation operator (overridden)
    NoHash,             \* sentinel used for the previous‑hash field
    NoBlock             \* sentinel used for empty block slots

\* -----------------------------------------------------------------
\* STATE VARIABLES
\* -----------------------------------------------------------------
VARIABLES
    lastHash,   \* the most recent block hash (or NoHash)
    ledger,     \* [node -> [hash -> (Block \cup {NoBlock})]]
    received    \* [node -> SUBSET Hash]  (blocks pending validation)

\* -----------------------------------------------------------------
\* BLOCK RECORD DEFINITION
\* -----------------------------------------------------------------
Block ==
    [ type          : {"genesis", "send", "open", "receive", "change"},
      account       : PublicKey,
      prev          : Hash \cup {NoHash},
      amount        : Nat,
      recipient     : PublicKey,
      representative: PublicKey,
      sig           : STRING ]

\* -----------------------------------------------------------------
\* HELPER DEFINITIONS
\* -----------------------------------------------------------------
ValidSignature(b) ==
    (* Abstract placeholder – we assume signatures are always valid. *)
    TRUE

\* -----------------------------------------------------------------
\* INITIAL STATE
\* -----------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger   = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]

\* -----------------------------------------------------------------
\* ACTION: CREATE GENESIS BLOCK
\* -----------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E pk \in PublicKey :
        \E sk \in PrivateKey :
            LET hNew == CHOOSE h \in Hash : TRUE
                b    == [ type          |-> "genesis",
                         account       |-> pk,
                         prev          |-> NoHash,
                         amount        |-> GenesisBalance,
                         recipient     |-> pk,
                         representative|-> pk,
                         sig           |-> "sig" ]
            IN
            /\ lastHash' = hNew
            /\ ledger'   = [ n \in Node |-> [ h \in Hash |-> IF h = hNew THEN b ELSE ledger[n][h] ] ]
            /\ received' = [ n \in Node |-> {} ]
    /\ UNCHANGED << >>

\* -----------------------------------------------------------------
\* ACTION: CREATE A GENERIC BLOCK (send, open, receive, change)
\* -----------------------------------------------------------------
CreateBlock ==
    /\ \E nCreator \in Node :
        \E b \in Block :
            LET hNew == CHOOSE h \in Hash : TRUE
            IN
            /\ lastHash' = hNew
            /\ ledger'   = [ n \in Node |-> [ h \in Hash |-> IF h = hNew THEN b ELSE ledger[n][h] ] ]
            /\ received' = [ n \in Node |-> IF n # nCreator THEN received[n] \cup {hNew} ELSE received[n] ]
    /\ UNCHANGED << >>

\* -----------------------------------------------------------------
\* ACTION: PROCESS A RECEIVED BLOCK
\* -----------------------------------------------------------------
ProcessReceived ==
    /\ \E n \in Node :
        /\ received[n] # {}
        /\ \E h \in received[n] :
            /\ received' = [ m \in Node |-> IF m = n THEN received[m] \ {h} ELSE received[m] ]
            /\ UNCHANGED << lastHash, ledger >>
    /\ UNCHANGED << >>

\* -----------------------------------------------------------------
\* NEXT STATE RELATION
\* -----------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateBlock
    \/ ProcessReceived

\* -----------------------------------------------------------------
\* SPECIFICATION
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<< lastHash, ledger, received >>

\* -----------------------------------------------------------------
\* INVARIANTS
\* -----------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger   \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            (b = NoBlock) \/ ValidSignature(b)

\* -----------------------------------------------------------------
\* ABSTRACT HASH CALCULATION IMPLEMENTATION (to be substituted)
\* -----------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* -----------------------------------------------------------------
\* THE END
\* -----------------------------------------------------------------
====