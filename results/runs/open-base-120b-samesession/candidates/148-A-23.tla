---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,            \* Universe of hash values
    NoHashVal,       \* Sentinel value meaning “no hash yet”
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Initial total coin supply (Nat)
    NoBlockVal,      \* Sentinel value meaning “no block stored”
    CalculateHash,   \* Abstract hash operator (overridden by CalculateHashImpl)
    NoHash,          \* Alias for NoHashVal (required by .cfg)
    NoBlock          \* Alias for NoBlockVal (required by .cfg)

\* ----------------------------------------------------------------------
\* ALIASES / HELPERS
\* ----------------------------------------------------------------------
NoHash == NoHashVal
NoBlock == NoBlockVal

\* Mapping from a private key to its public key (uninterpreted constant)
CONSTANT PrivToPub \* : [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* BLOCK REPRESENTATION
\* ----------------------------------------------------------------------
Block == [
    type    : {"genesis", "send", "open", "receive", "change"},
    hash    : Hash,
    prev    : Hash,
    account : PublicKey,      \* owner of the chain this block belongs to
    amount  : Nat,
    dest    : PublicKey,      \* used by send blocks
    src     : Hash,           \* used by open/receive blocks (the referenced send)
    sig     : STRING          \* abstract signature
]

\* Abstract signature check – in the model we simply accept any signature
SignatureValid(b) == TRUE

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* the most recent calculated block hash (or NoHashVal)
    ledger,     \* [node \in Node |-> [h \in Hash |-> Block \cup {NoBlock}]]
    received    \* [node \in Node |-> SUBSET Hash]  (blocks pending validation)

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* HASH CALCULATION (abstract, to be instantiated by CalculateHashImpl)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* The operator that the .cfg file overrides
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* ----------------------------------------------------------------------
\* BLOCK CREATION ACTIONS
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHashVal                      \* can happen only once
    /\ \E n \in Node :
        LET pk == PrivToPub[ n ] IN
        LET b == [
                type    |-> "genesis",
                hash    |-> h,
                prev    |-> NoHashVal,
                account |-> pk,
                amount  |-> GenesisBalance,
                dest    |-> pk,
                src     |-> NoHashVal,
                sig     |-> "sig(" \o n \o ")"
            ] IN
        /\ h = CalculateHash(b, NoHashVal)
        /\ ledger' = [ledger EXCEPT
                ![n] = [ledger[n] EXCEPT ![h] = b]
            ]
        /\ received' = [n \in Node |-> {}]            \* broadcast, all nodes receive
        /\ UNCHANGED << lastHash, received >>
        /\ lastHash' = h

CreateSend ==
    /\ \E n \in Node, amt \in Nat, dest \in PublicKey :
        /\ amt > 0
        /\ LET pk == PrivToPub[n] IN
        LET prevHash == 
            \* find the most recent block of this account in n's ledger
            CHOOSE h \in Hash : ledger[n][h] # NoBlockVal /\ ledger[n][h].account = pk /\ 
                                 \A h2 \in Hash : 
                                     (ledger[n][h2] # NoBlockVal /\ ledger[n][h2].account = pk /\ 
                                      ledger[n][h2].prev = h) => FALSE
        IN
        LET b == [
                type    |-> "send",
                hash    |-> h,
                prev    |-> prevHash,
                account |-> pk,
                amount  |-> amt,
                dest    |-> dest,
                src     |-> NoHashVal,
                sig     |-> "sig(" \o n \o ")"
            ] IN
        /\ h = CalculateHash(b, prevHash)
        /\ ledger' = [ledger EXCEPT
                ![n] = [ledger[n] EXCEPT ![h] = b]
            ]
        /\ received' = [m \in Node |-> received[m] \cup {h}]
        /\ UNCHANGED lastHash
        /\ UNCHANGED << >>

CreateOpen ==
    /\ \E n \in Node, sendHash \in Hash :
        LET pk == PrivToPub[n] IN
        LET sendBlk == ledger[n][sendHash] IN
        /\ sendBlk # NoBlockVal
        /\ sendBlk.type = "send"
        /\ sendBlk.dest = pk
        /\ \A m \in Node : ledger[m][sendHash] # NoBlockVal   \* block already known
        LET b == [
                type    |-> "open",
                hash    |-> h,
                prev    |-> NoHashVal,
                account |-> pk,
                amount  |-> sendBlk.amount,
                dest    |-> pk,
                src     |-> sendHash,
                sig     |-> "sig(" \o n \o ")"
            ] IN
        /\ h = CalculateHash(b, NoHashVal)
        /\ ledger' = [ledger EXCEPT
                ![n] = [ledger[n] EXCEPT ![h] = b]
            ]
        /\ received' = [m \in Node |-> received[m] \cup {h}]
        /\ UNCHANGED lastHash

CreateReceive ==
    /\ \E n \in Node, sendHash \in Hash, prevHash \in Hash :
        LET pk == PrivToPub[n] IN
        LET sendBlk == ledger[n][sendHash] IN
        /\ sendBlk # NoBlockVal
        /\ sendBlk.type = "send"
        /\ sendBlk.dest = pk
        /\ LET prevBlk == ledger[n][prevHash] IN
            prevBlk # NoBlockVal /\ prevBlk.account = pk
        LET b == [
                type    |-> "receive",
                hash    |-> h,
                prev    |-> prevHash,
                account |-> pk,
                amount  |-> sendBlk.amount,
                dest    |-> pk,
                src     |-> sendHash,
                sig     |-> "sig(" \o n \o ")"
            ] IN
        /\ h = CalculateHash(b, prevHash)
        /\ ledger' = [ledger EXCEPT
                ![n] = [ledger[n] EXCEPT ![h] = b]
            ]
        /\ received' = [m \in Node |-> received[m] \cup {h}]
        /\ UNCHANGED lastHash

CreateChange ==
    /\ \E n \in Node, prevHash \in Hash, newRep \in PublicKey :
        LET pk == PrivToPub[n] IN
        LET prevBlk == ledger[n][prevHash] IN
        /\ prevBlk # NoBlockVal /\ prevBlk.account = pk
        LET b == [
                type    |-> "change",
                hash    |-> h,
                prev    |-> prevHash,
                account |-> pk,
                amount  |-> 0,
                dest    |-> pk,
                src     |-> NoHashVal,
                sig     |-> "sig(" \o n \o ")"
            ] IN
        /\ h = CalculateHash(b, prevHash)
        /\ ledger' = [ledger EXCEPT
                ![n] = [ledger[n] EXCEPT ![h] = b]
            ]
        /\ received' = [m \in Node |-> received[m] \cup {h}]
        /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* PROCESS RECEIVED BLOCKS
\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node, h \in received[n] :
        LET b == ledger[n][h] IN
        /\ b # NoBlockVal
        /\ SignatureValid(b)                \* abstract signature check
        /\ \* referenced previous block must exist (except for genesis/open)
            (b.prev = NoHashVal \/ ledger[n][b.prev] # NoBlockVal)
        /\ \* type‑specific validation (simplified)
            IF b.type = "send" THEN
                TRUE
            ELSE IF b.type = "open" THEN
                TRUE
            ELSE IF b.type = "receive" THEN
                TRUE
            ELSE IF b.type = "change" THEN
                TRUE
            ELSE
                FALSE
        /\ ledger' = ledger               \* block already stored; no change
        /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
        /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* NEXT STATE RELATION
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* SAFETY INVARIANT (cryptographic signature correctness)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            (b # NoBlockVal) => SignatureValid(b)

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

====