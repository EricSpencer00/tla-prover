---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,          \* Set of possible block hashes
    NoHashVal,     \* Sentinel value for "no hash"
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total coins created in the genesis block
    NoBlockVal,    \* Sentinel value for "no block"
    CalculateHash, \* Abstract hash calculation operator (to be overridden)
    NoHash,        \* Another sentinel for hash (alias of NoHashVal)
    NoBlock        \* Another sentinel for block (alias of NoBlockVal)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

Block == [type    : BlockType,
          prev    : Hash \/ {NoHashVal},
          acct    : PublicKey,
          amount  : Nat,
          dest    : PublicKey \/ {NoBlock},
          sig     : PublicKey,
          hash    : Hash]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,     \* the most recent block hash (or NoHashVal)
    ledger,       \* [Node -> [Hash -> Block \/ {NoBlockVal}]]
    received,     \* [Node -> SUBSET Hash]
    blockStore    \* [Hash -> Block \/ {NoBlockVal}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A block is considered present if it is not the sentinel value.
IsBlock(b) == b # NoBlockVal

\* Simplified signature validation: a block's signature must equal the
\* account's public key (i.e., we treat the signature as the public key).
ValidSig(b) == b.sig = b.acct

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ blockStore = [h \in Hash |-> NoBlockVal]
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Block creation actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHashVal               \* can happen only once
    /\ \E h \in Hash :
         /\ h # NoHashVal
         /\ Let b == [type   |-> "Genesis",
                      prev   |-> NoHashVal,
                      acct   |-> AnyPublic,
                      amount |-> GenesisBalance,
                      dest   |-> NoBlock,
                      sig    |-> AnyPublic,
                      hash   |-> h] 
            In
                /\ blockStore' = [blockStore EXCEPT ![h] = b]
                /\ lastHash'   = h
                /\ ledger'     = [n \in Node |-> [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n][h2]]]
                /\ received'   = received
                /\ UNCHANGED << >>

\* Helper to pick an arbitrary public key (used for genesis creator)
AnyPublic == CHOOSE pk \in PublicKey : TRUE

CreateSend ==
    /\ \E creator \in Node :
       \E acct \in PublicKey :
          \E prev \in Hash :
             /\ IsBlock(blockStore[prev])
             /\ blockStore[prev].acct = acct
             /\ \E amount \in Nat :
                \E dest \in PublicKey :
                   \E h \in Hash :
                      /\ h # NoHashVal
                      /\ Let b == [type   |-> "Send",
                                   prev   |-> prev,
                                   acct   |-> acct,
                                   amount |-> amount,
                                   dest   |-> dest,
                                   sig    |-> acct,
                                   hash   |-> h] 
                         In
                            /\ blockStore' = [blockStore EXCEPT ![h] = b]
                            /\ lastHash'   = h
                            /\ ledger'     = ledger
                            /\ received'   = [n \in Node |-> received[n] \cup {h}]
                            /\ UNCHANGED lastHash

CreateOpen ==
    /\ \E recipient \in Node :
       \E acct \in PublicKey :
          \E sendHash \in Hash :
             /\ blockStore[sendHash].type = "Send"
             /\ blockStore[sendHash].dest = acct
             /\ \E h \in Hash :
                /\ h # NoHashVal
                /\ Let b == [type   |-> "Open",
                             prev   |-> NoHashVal,
                             acct   |-> acct,
                             amount |-> blockStore[sendHash].amount,
                             dest   |-> NoBlock,
                             sig    |-> acct,
                             hash   |-> h]
                   In
                      /\ blockStore' = [blockStore EXCEPT ![h] = b]
                      /\ lastHash'   = h
                      /\ ledger'     = ledger
                      /\ received'   = [n \in Node |-> received[n] \cup {h}]
                      /\ UNCHANGED lastHash

CreateReceive ==
    /\ \E receiver \in Node :
       \E acct \in PublicKey :
          \E prev \in Hash :
             /\ IsBlock(blockStore[prev])
             /\ blockStore[prev].acct = acct
             /\ \E sendHash \in Hash :
                /\ blockStore[sendHash].type = "Send"
                /\ blockStore[sendHash].dest = acct
                /\ \E h \in Hash :
                   /\ h # NoHashVal
                   /\ Let b == [type   |-> "Receive",
                                prev   |-> prev,
                                acct   |-> acct,
                                amount |-> blockStore[sendHash].amount,
                                dest   |-> NoBlock,
                                sig    |-> acct,
                                hash   |-> h]
                      In
                         /\ blockStore' = [blockStore EXCEPT ![h] = b]
                         /\ lastHash'   = h
                         /\ ledger'     = ledger
                         /\ received'   = [n \in Node |-> received[n] \cup {h}]
                         /\ UNCHANGED lastHash

CreateChange ==
    /\ \E changer \in Node :
       \E acct \in PublicKey :
          \E prev \in Hash :
             /\ IsBlock(blockStore[prev])
             /\ blockStore[prev].acct = acct
             /\ \E h \in Hash :
                /\ h # NoHashVal
                /\ Let b == [type   |-> "Change",
                             prev   |-> prev,
                             acct   |-> acct,
                             amount |-> 0,
                             dest   |-> NoBlock,
                             sig    |-> acct,
                             hash   |-> h]
                   In
                      /\ blockStore' = [blockStore EXCEPT ![h] = b]
                      /\ lastHash'   = h
                      /\ ledger'     = ledger
                      /\ received'   = [n \in Node |-> received[n] \cup {h}]
                      /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* Block processing (validation) action
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node :
       \E h \in received[n] :
          /\ IsBlock(blockStore[h])      \* block data must exist
          /\ ValidSig(blockStore[h])     \* signature must be valid
          /\ ledger' = [ledger EXCEPT ![n][h] = blockStore[h]]
          /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
          /\ UNCHANGED << lastHash, blockStore >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, blockStore>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHashVal}
    /\ blockStore \in [Hash -> (Block \/ {NoBlockVal})]
    /\ ledger \in [Node -> [Hash -> (Block \/ {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]
    /\ \A n \in Node: \A h \in Hash:
          (ledger[n][h] # NoBlockVal) => blockStore[h] = ledger[n][h]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic invariant)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node: \A h \in Hash:
        (ledger[n][h] # NoBlockVal) => ValidSig(ledger[n][h])

\* ----------------------------------------------------------------------
\* Abstract hash calculation implementation (to be substituted)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prevHash) ==
    CHOOSE h \in Hash : TRUE

=============================================================================