---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* CONSTANTS (to be instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,               \* Set of all possible block hashes
    NoHashVal,          \* Sentinel value meaning "no hash"
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total supply of coins (a natural number)
    NoBlockVal,         \* Sentinel value meaning "no block"
    CalculateHash,      \* Abstract hash operator (will be overridden)
    NoHash,             \* Alias for NoHashVal (required by the cfg)
    NoBlock,            \* Alias for NoBlockVal (required by the cfg)
    PrivateKeyToPublic, \* Mapping from private keys to public keys
    NodeToPriv          \* Mapping from nodes to owned private keys

\* ----------------------------------------------------------------------
\* ASSUMPTIONS about the supplied mappings
\* ----------------------------------------------------------------------
ASSUME PrivateKeyToPublic \in [PrivateKey -> PublicKey]
ASSUME NodeToPriv \in [Node -> PrivateKey]

\* ----------------------------------------------------------------------
\* DEFINITIONS for the aliases
\* ----------------------------------------------------------------------
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHashVal)
    ledger,     \* ledger[node][hash] = block stored at node under hash (or NoBlockVal)
    received    \* received[node] = set of hashes pending validation at node

\* ----------------------------------------------------------------------
\* BLOCK RECORD DEFINITION
\* ----------------------------------------------------------------------
Block ==
    [ kind      : {"genesis", "send", "open", "receive", "change"},
      prev      : Hash,
      acct      : PublicKey,
      amount    : Nat,
      dest      : PublicKey,
      src       : Hash,
      rep       : PublicKey,
      sig       : STRING,
      hash      : Hash ]

\* ----------------------------------------------------------------------
\* HELPERS
\* ----------------------------------------------------------------------
\* Extract the data that is signed (everything except the signature and hash)
BlockData(b) ==
    [ kind  |-> b.kind,
      prev  |-> b.prev,
      acct  |-> b.acct,
      amount|-> b.amount,
      dest  |-> b.dest,
      src   |-> b.src,
      rep   |-> b.rep ]

\* Choose a private key that corresponds to a given public key
PrivOfPub(pub) ==
    CHOOSE priv \in PrivateKey : PrivateKeyToPublic[priv] = pub

\* Simple (abstract) signature function
Sign(priv, data) ==
    << priv, data >>   \* represented as a tuple; the exact shape is irrelevant

\* Predicate that a block’s signature is valid
ValidSignature(b) ==
    LET priv == PrivOfPub(b.acct) IN
    b.sig = Sign(priv, BlockData(b))

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [ n \in Node |-> [ h \in Hash |-> NoBlockVal ] ]
    /\ received = [ n \in Node |-> {} ]

\* ----------------------------------------------------------------------
\* ACTION: CREATE GENESIS BLOCK
\* ----------------------------------------------------------------------
GenesisAction ==
    /\ lastHash = NoHashVal
    /\ \E n \in Node :
        LET priv == NodeToPriv[n]
            pub  == PrivateKeyToPublic[priv]
            b    == [ kind   |-> "genesis",
                     prev   |-> NoHash,
                     acct   |-> pub,
                     amount |-> GenesisBalance,
                     dest   |-> NoHash,
                     src    |-> NoHash,
                     rep    |-> NoHash,
                     sig    |-> Sign(priv,
                                    [ kind   |-> "genesis",
                                      prev   |-> NoHash,
                                      acct   |-> pub,
                                      amount |-> GenesisBalance,
                                      dest   |-> NoHash,
                                      src    |-> NoHash,
                                      rep    |-> NoHash ]),
                     hash   |-> CalculateHash(
                                 [ kind   |-> "genesis",
                                   prev   |-> NoHash,
                                   acct   |-> pub,
                                   amount |-> GenesisBalance,
                                   dest   |-> NoHash,
                                   src    |-> NoHash,
                                   rep    |-> NoHash ],
                                 NoHash) ]
        IN /\ lastHash' = b.hash
           /\ ledger'   = [ node \in Node |-> 
                             [ h \in Hash |-> IF h = b.hash THEN b ELSE ledger[node][h] ] ]
           /\ received' = [ node \in Node |-> {} ]
           /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: CREATE SEND BLOCK
\* ----------------------------------------------------------------------
SendAction ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, amt \in Nat, dst \in PublicKey :
         /\ amt <= GenesisBalance   \* (conservative bound for the model)
         LET priv == NodeToPriv[n]
             pub  == PrivateKeyToPublic[priv]
             b    == [ kind   |-> "send",
                      prev   |-> lastHash,
                      acct   |-> pub,
                      amount |-> amt,
                      dest   |-> dst,
                      src    |-> NoHash,
                      rep    |-> NoHash,
                      sig    |-> Sign(priv,
                                     [ kind   |-> "send",
                                       prev   |-> lastHash,
                                       acct   |-> pub,
                                       amount |-> amt,
                                       dest   |-> dst,
                                       src    |-> NoHash,
                                       rep    |-> NoHash ]),
                      hash   |-> CalculateHash(
                                  [ kind   |-> "send",
                                    prev   |-> lastHash,
                                    acct   |-> pub,
                                    amount |-> amt,
                                    dest   |-> dst,
                                    src    |-> NoHash,
                                    rep    |-> NoHash ],
                                  lastHash) ]
         IN /\ lastHash' = b.hash
            /\ ledger'   = [ node \in Node |-> 
                              [ h \in Hash |-> IF h = b.hash THEN b ELSE ledger[node][h] ] ]
            /\ received' = [ node \in Node |-> received[node] \cup {b.hash} ]
            /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: CREATE OPEN BLOCK
\* ----------------------------------------------------------------------
OpenAction ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, srcHash \in Hash :
        LET priv == NodeToPriv[n]
            pub  == PrivateKeyToPublic[priv]
            b    == [ kind   |-> "open",
                     prev   |-> NoHash,
                     acct   |-> pub,
                     amount |-> 0,
                     dest   |-> NoHash,
                     src    |-> srcHash,
                     rep    |-> NoHash,
                     sig    |-> Sign(priv,
                                    [ kind   |-> "open",
                                      prev   |-> NoHash,
                                      acct   |-> pub,
                                      amount |-> 0,
                                      dest   |-> NoHash,
                                      src    |-> srcHash,
                                      rep    |-> NoHash ]),
                     hash   |-> CalculateHash(
                                 [ kind   |-> "open",
                                   prev   |-> NoHash,
                                   acct   |-> pub,
                                   amount |-> 0,
                                   dest   |-> NoHash,
                                   src    |-> srcHash,
                                   rep    |-> NoHash ],
                                 NoHash) ]
        IN /\ lastHash' = b.hash
           /\ ledger'   = [ node \in Node |-> 
                             [ h \in Hash |-> IF h = b.hash THEN b ELSE ledger[node][h] ] ]
           /\ received' = [ node \in Node |-> received[node] \cup {b.hash} ]
           /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: CREATE RECEIVE BLOCK
\* ----------------------------------------------------------------------
ReceiveAction ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, srcHash \in Hash :
        LET priv == NodeToPriv[n]
            pub  == PrivateKeyToPublic[priv]
            b    == [ kind   |-> "receive",
                     prev   |-> lastHash,
                     acct   |-> pub,
                     amount |-> 0,
                     dest   |-> NoHash,
                     src    |-> srcHash,
                     rep    |-> NoHash,
                     sig    |-> Sign(priv,
                                    [ kind   |-> "receive",
                                      prev   |-> lastHash,
                                      acct   |-> pub,
                                      amount |-> 0,
                                      dest   |-> NoHash,
                                      src    |-> srcHash,
                                      rep    |-> NoHash ]),
                     hash   |-> CalculateHash(
                                 [ kind   |-> "receive",
                                   prev   |-> lastHash,
                                   acct   |-> pub,
                                   amount |-> 0,
                                   dest   |-> NoHash,
                                   src    |-> srcHash,
                                   rep    |-> NoHash ],
                                 lastHash) ]
        IN /\ lastHash' = b.hash
           /\ ledger'   = [ node \in Node |-> 
                             [ h \in Hash |-> IF h = b.hash THEN b ELSE ledger[node][h] ] ]
           /\ received' = [ node \in Node |-> received[node] \cup {b.hash} ]
           /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: CREATE CHANGE REPRESENTATIVE BLOCK
\* ----------------------------------------------------------------------
ChangeRepAction ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, newRep \in PublicKey :
        LET priv == NodeToPriv[n]
            pub  == PrivateKeyToPublic[priv]
            b    == [ kind   |-> "change",
                     prev   |-> lastHash,
                     acct   |-> pub,
                     amount |-> 0,
                     dest   |-> NoHash,
                     src    |-> NoHash,
                     rep    |-> newRep,
                     sig    |-> Sign(priv,
                                    [ kind   |-> "change",
                                      prev   |-> lastHash,
                                      acct   |-> pub,
                                      amount |-> 0,
                                      dest   |-> NoHash,
                                      src    |-> NoHash,
                                      rep    |-> newRep ]),
                     hash   |-> CalculateHash(
                                 [ kind   |-> "change",
                                   prev   |-> lastHash,
                                   acct   |-> pub,
                                   amount |-> 0,
                                   dest   |-> NoHash,
                                   src    |-> NoHash,
                                   rep    |-> newRep ],
                                 lastHash) ]
        IN /\ lastHash' = b.hash
           /\ ledger'   = [ node \in Node |-> 
                             [ h \in Hash |-> IF h = b.hash THEN b ELSE ledger[node][h] ] ]
           /\ received' = [ node \in Node |-> received[node] \cup {b.hash} ]
           /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: PROCESS A RECEIVED BLOCK (validation)
\* ----------------------------------------------------------------------
ProcessAction ==
    /\ \E n \in Node, h \in received[n] :
        LET b == ledger[n][h] IN
        /\ b # NoBlockVal
        /\ ValidSignature(b)               \* cryptographic check
        /\ received' = [ node \in Node |-> 
                         IF node = n THEN received[node] \ {h}
                         ELSE received[node] ]
        /\ UNCHANGED << lastHash, ledger >>

\* ----------------------------------------------------------------------
\* COMBINED NEXT ACTION
\* ----------------------------------------------------------------------
Next ==
    \/ GenesisAction
    \/ SendAction
    \/ OpenAction
    \/ ReceiveAction
    \/ ChangeRepAction
    \/ ProcessAction

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ (lastHash = NoHashVal) \/ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* SAFETY INVARIANT (cryptographic signatures are always valid)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            (b # NoBlockVal) => ValidSignature(b)

\* ----------------------------------------------------------------------
\* CONCRETE IMPLEMENTATION OF CalculateHash (used when the .cfg overrides)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    (* A very simple deterministic hash for model checking purposes *)
    CHOOSE h \in Hash : TRUE

============================================================================