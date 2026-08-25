---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,          \* Set of all possible block hashes
    NoHashVal,    \* Sentinel value indicating no hash exists yet
    PrivateKey,   \* Set of private keys
    PublicKey,    \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance, \* Total supply of coins at genesis
    NoBlockVal,   \* Sentinel value for an empty block slot in a ledger
    CalculateHash, \* Abstract hash operator (will be overridden)
    NoHash,        \* Alternative sentinel for a missing previous hash
    NoBlock        \* Alternative sentinel for an empty block

\* ----------------------------------------------------------------------
\* Additional constants that are useful for the model (they may also be
\* supplied by the configuration file)
\* ----------------------------------------------------------------------
CONSTANT
    PrivateToPublic, \* Mapping from private keys to their public keys
    NodeKey           \* Mapping from a node to the private key it owns

\* ----------------------------------------------------------------------
\* BLOCK DEFINITION
\* ----------------------------------------------------------------------
BlockType == {"genesis", "send", "open", "receive", "change"}

Block ==
    [ type       : BlockType,
      prev       : Hash \/ {NoHash},
      account    : PublicKey,
      sigKey     : PrivateKey,
      amount     : Nat,
      dest       : PublicKey,
      source     : Hash,
      rep        : PublicKey ]

\* Helper predicates identifying block kinds
IsGenesis(b) == b.type = "genesis"
IsSend(b)    == b.type = "send"
IsOpen(b)    == b.type = "open"
IsReceive(b) == b.type = "receive"
IsChange(b)  == b.type = "change"

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHashVal)
    ledger,     \* Mapping: Node -> (Hash -> Block \/ NoBlockVal)
    received    \* Mapping: Node -> SUBSET Hash (blocks pending validation)

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger  = [ n \in Node |-> [ h \in Hash |-> NoBlockVal ] ]
    /\ received = [ n \in Node |-> {} ]

\* ----------------------------------------------------------------------
\* ABSTRACT HASH OPERATOR (to be overridden by CalculateHashImpl)
\* ----------------------------------------------------------------------
CalculateHash(b, prev) == CalculateHashImpl(b, prev)

\* ----------------------------------------------------------------------
\* ACTION: CREATE GENESIS BLOCK
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E n \in Node :
        LET pk == PrivateToPublic[NodeKey[n]] ;
            b  == [ type    |-> "genesis",
                    prev    |-> NoHash,
                    account |-> pk,
                    sigKey  |-> NodeKey[n],
                    amount  |-> GenesisBalance,
                    dest    |-> pk,
                    source  |-> NoHash,
                    rep     |-> pk ] ;
            h  == CalculateHash(b, NoHash)
        IN
            /\ h \in Hash
            /\ lastHash' = h
            /\ ledger' = [ n2 \in Node |-> [ ledger[n2] EXCEPT ![h] = b ] ]
            /\ received' = received
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: CREATE SEND BLOCK
\* (simplified – does not compute actual balances)
\* ----------------------------------------------------------------------
CreateSend ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node :
        LET pk == PrivateToPublic[NodeKey[n]] ;
            b  == [ type    |-> "send",
                    prev    |-> lastHash,
                    account |-> pk,
                    sigKey  |-> NodeKey[n],
                    amount  |-> 1,                 \* fixed amount for simplicity
                    dest    |-> pk,                \* destination placeholder
                    source  |-> NoHash,
                    rep     |-> pk ] ;
            h  == CalculateHash(b, lastHash)
        IN
            /\ h \in Hash
            /\ lastHash' = h
            /\ ledger' = [ n2 \in Node |-> [ ledger[n2] EXCEPT ![h] = b ] ]
            /\ received' = [ n2 \in Node |-> received[n2] \cup {h} ]
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: CREATE OPEN BLOCK
\* (opens an account using a previously received send block)
\* ----------------------------------------------------------------------
CreateOpen ==
    /\ \E n \in Node :
        \E hSend \in received[n] :
            LET bSend == ledger[n][hSend] ;
                pk    == PrivateToPublic[NodeKey[n]] ;
                bOpen == [ type    |-> "open",
                           prev    |-> NoHash,
                           account |-> pk,
                           sigKey  |-> NodeKey[n],
                           amount  |-> bSend.amount,
                           dest    |-> pk,
                           source  |-> hSend,
                           rep     |-> pk ] ;
                hOpen == CalculateHash(bOpen, NoHash)
            IN
                /\ IsSend(bSend)
                /\ bSend.dest = pk
                /\ hOpen \in Hash
                /\ lastHash' = hOpen
                /\ ledger' = [ n2 \in Node |-> [ ledger[n2] EXCEPT ![hOpen] = bOpen ] ]
                /\ received' = [ n2 \in Node |-> 
                                   IF n2 = n THEN received[n2] \setminus {hSend}
                                   ELSE received[n2] ]
                /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: CREATE RECEIVE BLOCK
\* (receives a previously sent amount)
\* ----------------------------------------------------------------------
CreateReceive ==
    /\ \E n \in Node :
        \E hSend \in received[n] :
            LET bSend == ledger[n][hSend] ;
                pk    == PrivateToPublic[NodeKey[n]] ;
                bPrev == IF lastHash = NoHashVal
                         THEN [ type    |-> "open",
                                prev    |-> NoHash,
                                account |-> pk,
                                sigKey  |-> NodeKey[n],
                                amount  |-> 0,
                                dest    |-> pk,
                                source  |-> NoHash,
                                rep     |-> pk ]
                         ELSE ledger[n][lastHash] ;
                bRecv == [ type    |-> "receive",
                           prev    |-> lastHash,
                           account |-> pk,
                           sigKey  |-> NodeKey[n],
                           amount  |-> bSend.amount,
                           dest    |-> pk,
                           source  |-> hSend,
                           rep     |-> pk ] ;
                hRecv == CalculateHash(bRecv, lastHash)
            IN
                /\ IsSend(bSend)
                /\ bSend.dest = pk
                /\ hRecv \in Hash
                /\ lastHash' = hRecv
                /\ ledger' = [ n2 \in Node |-> [ ledger[n2] EXCEPT ![hRecv] = bRecv ] ]
                /\ received' = [ n2 \in Node |-> 
                                   IF n2 = n THEN received[n2] \setminus {hSend}
                                   ELSE received[n2] ]
                /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: CREATE CHANGE REPRESENTATIVE BLOCK
\* ----------------------------------------------------------------------
CreateChange ==
    /\ \E n \in Node :
        LET pk    == PrivateToPublic[NodeKey[n]] ;
            bPrev == IF lastHash = NoHashVal
                     THEN [ type    |-> "open",
                            prev    |-> NoHash,
                            account |-> pk,
                            sigKey  |-> NodeKey[n],
                            amount  |-> 0,
                            dest    |-> pk,
                            source  |-> NoHash,
                            rep     |-> pk ]
                     ELSE ledger[n][lastHash] ;
            bChange == [ type    |-> "change",
                         prev    |-> lastHash,
                         account |-> pk,
                         sigKey  |-> NodeKey[n],
                         amount  |-> 0,
                         dest    |-> pk,
                         source  |-> NoHash,
                         rep     |-> pk ] ;
            hChange == CalculateHash(bChange, lastHash)
        IN
            /\ hChange \in Hash
            /\ lastHash' = hChange
            /\ ledger' = [ n2 \in Node |-> [ ledger[n2] EXCEPT ![hChange] = bChange ] ]
            /\ received' = received
            /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* ACTION: PROCESS RECEIVED BLOCK
\* (validates a block that is in the received set and adds it to the ledger)
\* ----------------------------------------------------------------------
ProcessReceived ==
    /\ \E n \in Node :
        /\ \E h \in received[n] :
            LET b == ledger[n][h] IN
                /\ b # NoBlockVal
                /\ PrivateToPublic[b.sigKey] = b.account          \* signature check
                /\ ( \/ IsSend(b)   => TRUE
                   \/ IsOpen(b)   => TRUE
                   \/ IsReceive(b)=> TRUE
                   \/ IsChange(b) => TRUE
                   \/ IsGenesis(b)=> TRUE )
                /\ ledger' = [ n2 \in Node |-> [ ledger[n2] EXCEPT ![h] = b ] ]
                /\ received' = [ n2 \in Node |-> 
                                   IF n2 = n THEN received[n2] \setminus {h}
                                   ELSE received[n2] ]
                /\ UNCHANGED lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* COMBINED NEXT ACTION
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHashVal}
    /\ ledger \in [Node -> [Hash -> (Block \/ {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* SAFETY INVARIANT (cryptographic integrity)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlockVal THEN
                LET b == ledger[n][h] IN
                    PrivateToPublic[b.sigKey] = b.account
            ELSE TRUE

====