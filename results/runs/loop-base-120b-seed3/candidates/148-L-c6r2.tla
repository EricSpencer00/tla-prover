---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, CalculateHash, NoHash, NoBlock

\* ----------------------------------------------------------------------
\* Sentinel definitions (allow substitution in the .cfg)
\* ----------------------------------------------------------------------
NoHashVal == NoHash
NoBlockVal == NoBlock

VARIABLES
    lastHash, ledger, received

\* ----------------------------------------------------------------------
\* Types and basic definitions
\* ----------------------------------------------------------------------
Block == [ type      : {"genesis", "send", "open", "receive", "change"},
           hash      : Hash,
           prev      : Hash,
           acct      : PublicKey,
           amount    : Nat,
           recipient : PublicKey,
           sig       : PrivateKey,
           rep       : PublicKey ]

\* Mapping from a private key to its public key (abstract, supplied by the cfg)
PRIVATE_TO_PUBLIC == [pk \in PrivateKey |-> CHOOSE pub \in PublicKey : TRUE]

\* ----------------------------------------------------------------------
\* Hash calculation (abstract, may be overridden by the cfg)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) == CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Helper to construct a block (hash is computed via CalculateHashImpl)
\* ----------------------------------------------------------------------
MakeBlock(type, prev, acct, amount, recipient, sig, rep) ==
    LET h == CalculateHashImpl([type      |-> type,
                                 prev      |-> prev,
                                 acct      |-> acct,
                                 amount    |-> amount,
                                 recipient |-> recipient,
                                 sig       |-> sig,
                                 rep       |-> rep], prev)
    IN [ type      |-> type,
         hash      |-> h,
         prev      |-> prev,
         acct      |-> acct,
         amount    |-> amount,
         recipient |-> recipient,
         sig       |-> sig,
         rep       |-> rep ]

\* ----------------------------------------------------------------------
\* Signature validation (the signature must be a private key whose public
\* key matches the account owning the chain)
\* ----------------------------------------------------------------------
SigValid(b) ==
    /\ b.sig \in PrivateKey
    /\ PRIVATE_TO_PUBLIC[b.sig] = b.acct

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger  = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Genesis block creation (may occur only once)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E genPriv \in PrivateKey :
          LET genPub == PRIVATE_TO_PUBLIC[genPriv] IN
          LET b == MakeBlock("genesis", NoHash, genPub,
                             GenesisBalance, genPub, genPriv, genPub) IN
          /\ lastHash' = b.hash
          /\ ledger'   = [ n \in Node |-> [ h \in Hash |-> IF h = b.hash THEN b ELSE ledger[n][h] ] ]
          /\ received' = [ n \in Node |-> {} ]

\* Creation of a generic block (send, open, receive, change) – for
\* simplicity we allow any type except genesis and broadcast it.
CreateBlock ==
    /\ lastHash # NoHash
    /\ \E priv \in PrivateKey :
          LET pub == PRIVATE_TO_PUBLIC[priv] IN
          \E blkType \in {"send", "open", "receive", "change"} :
          \E amt \in Nat :
          \E rcpt \in PublicKey :
          LET b == MakeBlock(blkType, lastHash, pub, amt, rcpt, priv, pub) IN
          /\ lastHash' = b.hash
          /\ ledger'   = ledger          \* block not yet applied to any ledger
          /\ received' = [ n \in Node |-> received[n] \cup {b} ]

\* Processing of a received block by a node (validation and insertion)
ProcessBlock ==
    /\ \E n \in Node :
          \E b \in received[n] :
                /\ SigValid(b)
                /\ ledger'   = [ ledger EXCEPT ![n][b.hash] = b ]
                /\ received' = [ received EXCEPT ![n] = received[n] \ {b} ]
                /\ lastHash' = lastHash

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateBlock
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHash
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Block]

\* ----------------------------------------------------------------------
\* Cryptographic safety invariant (all stored blocks have valid signatures)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            IF b = NoBlock THEN TRUE ELSE SigValid(b)

==============================================================================