---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Strings

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock,
    PrivToPub, NodePriv, VerifySignature, Sign, Sig

(* ---------------------------------------------------------------------- *)
(* Derived constants and basic definitions                                 *)
(* ---------------------------------------------------------------------- *)

NoHash == NoHashVal
NoBlock == NoBlockVal

(* Hash values are natural numbers together with a sentinel *)
Hash == Nat \cup { NoHash }

(* Sentinel values *)
NoHashVal == -1
NoBlockVal ==
    [ type      |-> "none",
      hash      |-> NoHash,
      prev      |-> NoHash,
      account   |-> "NoPub",
      amount    |-> 0,
      dest      |-> "NoPub",
      signature |-> "NoSig" ]

(* The set of possible signatures (abstract) *)
Sig == STRING

(* Block record definition *)
Block ==
    { [ type      : {"genesis","send","open","receive","change","none"},
        hash      : Hash,
        prev      : Hash,
        account   : PublicKey,
        amount    : Nat,
        dest      : PublicKey,
        signature : Sig ] }

(* ---------------------------------------------------------------------- *)
(* State variables                                                         *)
(* ---------------------------------------------------------------------- *)

VARIABLES
    LastHash,          \* the most recent global block hash
    Ledger,            \* [Node -> [Hash -> Block]]  (each node's copy)
    Received,          \* [Node -> SUBSET Block]    (blocks awaiting processing)
    AccountHead        \* [PublicKey -> Hash]        (latest block of each account)

(* ---------------------------------------------------------------------- *)
(* Helper operators                                                       *)
(* ---------------------------------------------------------------------- *)

PubKeyOf(b) == b.account

BlockData(b) ==
    [ type    |-> b.type,
      prev    |-> b.prev,
      account |-> b.account,
      amount  |-> b.amount,
      dest    |-> b.dest ]

ValidSignature(b) == VerifySignature(PubKeyOf(b), BlockData(b), b.signature)

(* ---------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ LastHash = NoHash
    /\ Ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ Received = [ n \in Node |-> {} ]
    /\ AccountHead = [ pk \in PublicKey |-> NoHash ]

(* ---------------------------------------------------------------------- *)
(* Actions                                                                *)
(* ---------------------------------------------------------------------- *)

(* Create the genesis block – can happen only once *)
CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E n \in Node :
        LET priv == NodePriv[n] IN
        LET pub  == PrivToPub[priv] IN
        LET blkData ==
            [ type |-> "genesis",
              prev |-> NoHash,
              account |-> pub,
              amount |-> GenesisBalance,
              dest |-> "NoPub" ] IN
        LET blkHash == CalculateHash(blkData, NoHash) IN
        LET sig == Sign(priv, blkData) IN
        LET blk ==
            [ type      |-> "genesis",
              hash      |-> blkHash,
              prev      |-> NoHash,
              account   |-> pub,
              amount    |-> GenesisBalance,
              dest      |-> "NoPub",
              signature |-> sig ] IN
        /\ LastHash' = blkHash
        /\ Ledger' =
           [ m \in Node |-> [ h \in Hash |-> IF h = blkHash THEN blk ELSE Ledger[m][h] ] ]
        /\ Received' = [ m \in Node |-> {} ]
        /\ AccountHead' = [ pk \in PublicKey |-> IF pk = pub THEN blkHash ELSE AccountHead[pk] ]

(* Create a send block; broadcast to all nodes' Received sets *)
CreateSend ==
    /\ \E n \in Node, dest \in PublicKey, amt \in Nat :
        LET priv == NodePriv[n] IN
        LET pub  == PrivToPub[priv] IN
        /\ amt <= GenesisBalance               \* placeholder balance check
        LET prevHash == AccountHead[pub] IN
        /\ prevHash # NoHash
        LET blkData ==
            [ type |-> "send",
              prev |-> prevHash,
              account |-> pub,
              amount |-> amt,
              dest |-> dest ] IN
        LET blkHash == CalculateHash(blkData, prevHash) IN
        LET sig == Sign(priv, blkData) IN
        LET blk ==
            [ type      |-> "send",
              hash      |-> blkHash,
              prev      |-> prevHash,
              account   |-> pub,
              amount    |-> amt,
              dest      |-> dest,
              signature |-> sig ] IN
        /\ Received' = [ m \in Node |-> Received[m] \cup { blk } ]
        /\ UNCHANGED << LastHash, Ledger, AccountHead >>

(* Process a received block at a node, after validation *)
Process ==
    /\ \E n \in Node, b \in Received[n] :
        /\ ValidSignature(b)
        LET h == b.hash IN
        LET owner == PubKeyOf(b) IN
        /\ Ledger' =
           [ m \in Node |-> [ hh \in Hash |-> IF hh = h THEN b ELSE Ledger[m][hh] ] ]
        /\ Received' = [ m \in Node |-> IF m = n THEN Received[m] \ { b } ELSE Received[m] ]
        /\ LastHash' = h
        /\ AccountHead' = [ pk \in PublicKey |-> IF pk = owner THEN h ELSE AccountHead[pk] ]
        /\ UNCHANGED << >>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ Process

Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, AccountHead>>

(* ---------------------------------------------------------------------- *)
(* Invariants                                                              *)
(* ---------------------------------------------------------------------- *)

TypeInvariant ==
    /\ LastHash \in Hash
    /\ Ledger \in [Node -> [Hash -> Block]]
    /\ Received \in [Node -> SUBSET Block]
    /\ AccountHead \in [PublicKey -> Hash]

SafetyInvariant ==
    \A n \in Node : \A h \in Hash :
        IF Ledger[n][h] # NoBlock
        THEN ValidSignature(Ledger[n][h])
        ELSE TRUE

(* ---------------------------------------------------------------------- *)
(* Operator to be substituted by the .cfg (CalculateHashImpl)              *)
(* ---------------------------------------------------------------------- *)

CalculateHashImpl(d, p) == p + 1

====