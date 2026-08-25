---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

(*====================================================================*)
(*  Constants (as required by the .cfg file)                           *)
(*====================================================================*)
CONSTANTS
    Hash,               \* set of all possible block hashes
    NoHashVal,          \* sentinel value for “no previous hash”
    PrivateKey,         \* set of private keys
    PublicKey,          \* set of public keys
    Node,               \* set of network nodes
    GenesisBalance,     \* total amount of coins at genesis (Nat)
    NoBlockVal,         \* sentinel value for “empty block”
    CalculateHash,      \* abstract hash operator (will be overridden)
    NoHash,             \* synonym for NoHashVal
    NoBlock             \* synonym for NoBlockVal

(*====================================================================*)
(*  Derived definitions                                                *)
(*====================================================================*)
NoHash == NoHashVal
NoBlock == NoBlockVal

(*  Mapping from each node to the private key it owns                      *)
ASSUME NodeKey \in [Node -> PrivateKey]

(*  Mapping from a private key to its corresponding public key          *)
ASSUME PrivToPub \in [PrivateKey -> PublicKey]

(*====================================================================*)
(*  Block record definition                                            *)
(*====================================================================*)
Block ==
    [ type        : {"genesis","send","open","receive","change"},
      prev        : Hash \/ {NoHash},
      account     : PublicKey,
      destination : PublicKey \/ {NoBlock},
      amount      : Nat,
      sig         : STRING,
      rep         : PublicKey \/ {NoBlock} ]

(*  Abstract cryptographic primitives                                    *)
Sign(priv, data) == "sig"          \* placeholder for a signature
SigValid(sig, pk, data) == TRUE    \* always true in the abstract model

(*  Abstract hash calculation (will be overridden by CalculateHashImpl) *)
CalculateHashImpl(data, prev) == CHOOSE h \in Hash : TRUE

(*====================================================================*)
(*  Helper functions                                                   *)
(*====================================================================*)
Sum(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN x + Sum(S \ {x})

Balance(pk, l) ==
    LET blocks == { h \in Hash : l[h] # NoBlock } IN
    Sum({ IF l[h].type = "genesis" /\ l[h].account = pk THEN l[h].amount
          ELSE IF l[h].type = "receive" /\ l[h].account = pk THEN l[h].amount
          ELSE IF l[h].type = "send" /\ l[h].account = pk THEN -l[h].amount
          ELSE 0
        : h \in blocks })

(*====================================================================*)
(*  Variables                                                          *)
(*====================================================================*)
VARIABLES
    lastHash,   \* the hash of the most recently added block, or NoHash
    ledger,     \* [Hash -> (Block \cup {NoBlock})]
    received    \* [Node -> SUBSET Hash]   (blocks awaiting processing)

vars == << lastHash, ledger, received >>

(*====================================================================*)
(*  Initial state                                                      *)
(*====================================================================*)
Init ==
    /\ lastHash = NoHash
    /\ ledger   = [h \in Hash |-> NoBlock]
    /\ received = [n \in Node |-> {}]

(*====================================================================*)
(*  Actions                                                            *)
(*====================================================================*)
GenesisCreate ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
        LET priv == NodeKey[n] ;
            pk   == PrivToPub[priv] ;
            blk  == [ type        |-> "genesis",
                     prev        |-> NoHash,
                     account     |-> pk,
                     destination |-> NoBlock,
                     amount      |-> GenesisBalance,
                     sig         |-> Sign(priv, "genesis"),
                     rep         |-> NoBlock ] ;
            h    == CalculateHashImpl(blk, NoHash)
        IN  /\ h \in Hash
            /\ ledger'   = [ledger EXCEPT ![h] = blk]
            /\ lastHash' = h
            /\ received' = [n \in Node |-> {}]

SendCreate ==
    /\ lastHash # NoHash
    /\ \E n \in Node :
        LET priv == NodeKey[n] ;
            pk   == PrivToPub[priv] ;
            dst  == CHOOSE d \in PublicKey : TRUE ;
            amt  == CHOOSE a \in Nat : a <= Balance(pk, ledger) ;
            blk  == [ type        |-> "send",
                     prev        |-> lastHash,
                     account     |-> pk,
                     destination |-> dst,
                     amount      |-> amt,
                     sig         |-> Sign(priv, "send"),
                     rep         |-> NoBlock ] ;
            h    == CalculateHashImpl(blk, lastHash)
        IN  /\ h \in Hash
            /\ ledger'   = [ledger EXCEPT ![h] = blk]
            /\ lastHash' = h
            /\ received' = [m \in Node |-> received[m] \cup {h}]

(*  Placeholder actions for the other block types – omitted for brevity *)
OpenCreate    == FALSE
ReceiveCreate == FALSE
ChangeRepCreate == FALSE

Next ==
    \/ GenesisCreate
    \/ SendCreate
    \/ OpenCreate
    \/ ReceiveCreate
    \/ ChangeRepCreate

(*====================================================================*)
(*  Specification                                                      *)
(*====================================================================*)
Spec == Init /\ [][Next]_vars

(*====================================================================*)
(*  Invariants                                                         *)
(*====================================================================*)
TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHash}
    /\ ledger   \in [Hash -> (Block \cup {NoBlock})]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A h \in Hash :
        IF ledger[h] # NoBlock
        THEN SigValid(ledger[h].sig, ledger[h].account, ledger[h])
        ELSE TRUE

(*====================================================================*)
(*  End of module                                                      *)
(*====================================================================*)
====