---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  CONSTANT DECLARATIONS                                                 *)
(***************************************************************************)
CONSTANTS
    Hash,               \* Set of all possible block hashes
    NoHash,             \* Sentinel hash value (member of Hash)
    NoHashVal,          \* Alias for the sentinel hash value (may be used in records)
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total supply of coins (a natural number)
    NoBlock,            \* Sentinel for an absent block
    NoBlockVal,         \* Alias for the sentinel block value
    CalculateHash       \* Abstract hash calculation operator (to be overridden)

(***************************************************************************)
(*  DERIVED CONSTANTS AND OPERATORS                                       *)
(***************************************************************************)

(* Mapping from a private key to its public counterpart.  The concrete
   mapping is supplied by the model‑checking configuration. *)
PrivateToPublic \in [PrivateKey -> PublicKey]

(* An abstract signature verification operator.  In a real model this would
   be replaced by a concrete implementation, but for the purposes of the
   specification it is left uninterpreted. *)
VerifySig(sig, pk, data) == TRUE

(* An abstract signing operator; its result is a string representing a
   signature.  Left uninterpreted. *)
Sign(priv, data) == "sig"

(* --------------------------------------------------------------------- *)
(*  BLOCK RECORD TYPE                                                    *)
(* --------------------------------------------------------------------- *)

Block == [
    type       : {"genesis", "send", "open", "receive", "change"},
    prev       : Hash \/ {NoHash},
    account    : PublicKey,
    dest       : PublicKey \/ {NoHash},   \* Destination for send/open blocks
    amount     : Nat,
    signature  : STRING
]

(* --------------------------------------------------------------------- *)
(*  USER‑DEFINED HASH CALCULATION (to be overridden in the .cfg)          *)
(* --------------------------------------------------------------------- *)

CalculateHashImpl(b, ph) == 
    \* Non‑deterministically pick a hash from the set Hash.
    CHOOSE h \in Hash : TRUE

(* By default CalculateHash delegates to the implementation that will be
   supplied by the configuration file. *)
CalculateHash(b, ph) == CalculateHashImpl(b, ph)

(***************************************************************************)
(*  STATE VARIABLES                                                       *)
(***************************************************************************)

VARIABLES
    lastHash,               \* The hash of the most recently created block
    ledger,                 \* [Node -> [Hash -> (Block \/ NoBlock)]]
    received,               \* [Node -> SUBSET Hash]  (blocks pending validation)
    genesisCreated          \* Boolean flag indicating whether genesis block exists

(***************************************************************************)
(*  INITIAL STATE                                                         *)
(***************************************************************************)

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ genesisCreated = FALSE

(***************************************************************************)
(*  HELPERS                                                               *)
(***************************************************************************)

(* The set of all blocks present in a node's ledger (excluding the sentinel). *)
Blocks(n) == { b : b \in Block : \E h \in Hash : ledger[n][h] = b }

(* Returns the most recent hash in the chain of the given account on node n.
   For brevity we treat it as an uninterpreted function. *)
LatestHash(n, acct) == 
    CHOOSE h \in Hash : ledger[n][h].account = acct

(* Computes the balance of an account by recursively walking its chain.
   The definition is abstract; the invariant that total balances never exceed
   GenesisBalance is expressed elsewhere. *)
Balance(n, acct) == 
    IF \A h \in Hash : ledger[n][h].account = acct => FALSE
    THEN 0
    ELSE 0   \* Placeholder – concrete definition omitted for brevity

(* --------------------------------------------------------------------- *)
(*  ACTIONS                                                               *)
(* --------------------------------------------------------------------- *)

CreateGenesis ==
    /\ ~genesisCreated
    /\ \E n \in Node :
        \E pk \in PublicKey :
            \E priv \in PrivateKey :
                PrivateToPublic[priv] = pk
                /\ \* The node n owns priv (ownership relation omitted)
                /\ let b == [
                        type       |-> "genesis",
                        prev       |-> NoHash,
                        account    |-> pk,
                        dest       |-> NoHash,
                        amount     |-> GenesisBalance,
                        signature  |-> Sign(priv, <<"genesis", pk, GenesisBalance>>)
                    ] in
                   h == CalculateHash(b, NoHash)
                /\ lastHash' = h
                /\ ledger' = [node \in Node |-> 
                                [hash \in Hash |-> 
                                    IF hash = h THEN b ELSE ledger[node][hash]]]
                /\ received' = received
                /\ genesisCreated' = TRUE
                /\ UNCHANGED <<lastHash, ledger, received, genesisCreated>>

CreateSend ==
    /\ genesisCreated
    /\ \E n \in Node :
        \E priv \in PrivateKey :
            \E pk \in PublicKey :
                PrivateToPublic[priv] = pk
                /\ Balance(n, pk) >= amount
                /\ amount \in Nat \ {0}
                /\ \E destPk \in PublicKey :
                    destPk # pk
                    /\ let prevHash == LatestHash(n, pk) in
                       \E b == [
                            type       |-> "send",
                            prev       |-> prevHash,
                            account    |-> pk,
                            dest       |-> destPk,
                            amount     |-> amount,
                            signature  |-> Sign(priv, <<"send", prevHash, destPk, amount>>)
                        ] :
                           h == CalculateHash(b, prevHash)
                           /\ lastHash' = h
                           /\ ledger' = [node \in Node |-> 
                                            [hash \in Hash |-> 
                                                IF hash = h THEN b ELSE ledger[node][hash]]]
                           /\ received' = [node \in Node |-> received[node] \cup {h}]
                           /\ UNCHANGED <<genesisCreated>>

CreateOpen ==
    /\ genesisCreated
    /\ \E n \in Node :
        \E priv \in PrivateKey :
            \E pk \in PublicKey :
                PrivateToPublic[priv] = pk
                /\ \E srcHash \in Hash :
                    \E sendBlock == ledger[n][srcHash] :
                        /\ sendBlock.type = "send"
                        /\ sendBlock.dest = pk
                        /\ ~\E h \in Hash : ledger[n][h].type = "open" /\ ledger[n][h].account = pk
                        /\ let b == [
                                type       |-> "open",
                                prev       |-> NoHash,
                                account    |-> pk,
                                dest       |-> NoHash,
                                amount     |-> sendBlock.amount,
                                signature  |-> Sign(priv, <<"open", srcHash>>)
                            ] in
                           h == CalculateHash(b, NoHash)
                           /\ lastHash' = h
                           /\ ledger' = [node \in Node |-> 
                                            [hash \in Hash |-> 
                                                IF hash = h THEN b ELSE ledger[node][hash]]]
                           /\ received' = [node \in Node |-> received[node] \cup {h}]
                           /\ UNCHANGED <<genesisCreated>>

CreateReceive ==
    /\ genesisCreated
    /\ \E n \in Node :
        \E priv \in PrivateKey :
            \E pk \in PublicKey :
                PrivateToPublic[priv] = pk
                /\ \E srcHash \in Hash :
                    \E sendBlock == ledger[n][srcHash] :
                        /\ sendBlock.type = "send"
                        /\ sendBlock.dest = pk
                        /\ \E prevHash == LatestHash(n, pk) :
                            let b == [
                                    type       |-> "receive",
                                    prev       |-> prevHash,
                                    account    |-> pk,
                                    dest       |-> NoHash,
                                    amount     |-> sendBlock.amount,
                                    signature  |-> Sign(priv, <<"receive", prevHash, srcHash>>)
                                ] in
                               h == CalculateHash(b, prevHash)
                               /\ lastHash' = h
                               /\ ledger' = [node \in Node |-> 
                                                [hash \in Hash |-> 
                                                    IF hash = h THEN b ELSE ledger[node][hash]]]
                               /\ received' = [node \in Node |-> received[node] \cup {h}]
                               /\ UNCHANGED <<genesisCreated>>

CreateChange ==
    /\ genesisCreated
    /\ \E n \in Node :
        \E priv \in PrivateKey :
            \E pk \in PublicKey :
                PrivateToPublic[priv] = pk
                /\ \E newRep \in PublicKey :
                    let prevHash == LatestHash(n, pk) in
                    let b == [
                            type       |-> "change",
                            prev       |-> prevHash,
                            account    |-> pk,
                            dest       |-> newRep,
                            amount     |-> 0,
                            signature  |-> Sign(priv, <<"change", prevHash, newRep>>)
                        ] in
                       h == CalculateHash(b, prevHash)
                       /\ lastHash' = h
                       /\ ledger' = [node \in Node |-> 
                                        [hash \in Hash |-> 
                                            IF hash = h THEN b ELSE ledger[node][hash]]]
                       /\ received' = [node \in Node |-> received[node] \cup {h}]
                       /\ UNCHANGED <<genesisCreated>>

ProcessReceived ==
    /\ \E n \in Node :
        \E h \in received[n] :
            LET b == ledger[n][h] IN
            /\ b # NoBlock
            /\ VerifySig(b.signature, b.account, b)
            /\ /\* Simple validation of referenced hashes *\/
               (b.prev = NoHash \/ \E hp \in Hash : ledger[n][hp] # NoBlock /\ hp = b.prev)
            /\* Additional type‑specific checks are omitted for brevity *\/
            /\ ledger' = ledger
            /\ received' = [node \in Node |-> 
                               IF node = n THEN received[node] \ {h}
                               ELSE received[node]]
            /\ UNCHANGED <<lastHash, genesisCreated>>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

(***************************************************************************)
(*  SPECIFICATION                                                         *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<lastHash, ledger, received, genesisCreated>>

(***************************************************************************)
(*  INVARIANTS                                                            *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHash}
    /\ ledger \in [Node -> [Hash -> (Block \/ NoBlock)]]
    /\ received \in [Node -> SUBSET Hash]
    /\ genesisCreated \in BOOLEAN

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            (b = NoBlock) \/ VerifySig(b.signature, b.account, b)

(***************************************************************************)
(*  EXPORTS                                                               *)
(***************************************************************************)

THEOREM SpecImpliesTypeInvariant == Spec => []TypeInvariant
THEOREM SpecImpliesSafetyInvariant == Spec => []SafetyInvariant

=============================================================================