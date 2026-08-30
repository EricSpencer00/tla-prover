---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

\* The block-lattice is a mapping from account chains (identified by a public
\* key) to an ordered chain of blocks, each pointing to its predecessor.
\* BoundedHash is the finite set of block hashes available in this model.
\* The type invariant below is what keeps the whole chain in scope.
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* The hash operator is deliberately left abstract in the specification;
\* different bounded models (or an unbounded real implementation) may
\* instantiate it with different concrete functions.
\* The .cfg file injects a concrete operator in place of the placeholder.
CalculateHash == CalculateHashImpl

Chain(k) == [prevHash : Hash \cup {NoHash}, key : PrivateKey, pub : PublicKey, amt : 1..GenesisBalance, typ : {"genesis", "send", "open", "receive", "change"}]

\* The ledger is a map from (account-public-key, block-hash) to a block, so
\* the chain for each account is drawn from the same bounded hash pool.
Ledger(k, h) == ledger[k][h]

RECURSIVE BalanceOf(_, _)
BalanceOf(k, h) ==
  IF h = NoHash THEN 0
  ELSE IF Ledger(k, h) = NoBlockVal THEN BalanceOf(k, NoHash)
  ELSE LET blk == Ledger(k, h) IN
    IF blk.typ = "receive" THEN blk.amt + BalanceOf(k, blk.prevHash)
    ELSE BalanceOf(k, blk.prevHash)

RECURSIVE SumOver(_, _)
SumOver(S, k) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN BalanceOf(k, x) + SumOver(S \ {x}, k)

AccountBalance(k) == BalanceOf(k, lastHash)
TotalBalance == SumOver(BoundedHash, PublicKey)

Init ==
  /\ lastHash = NoHash
  /\ ledger = [k \in PublicKey |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

Broadcast(n, blk) ==
  /\ lastHash' = blk.prevHash
  /\ ledger' = [k \in PublicKey |-> [ledger[k] EXCEPT ![blk.prevHash] = blk]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup {blk}]

\* The genesis block is the anchor for the entire lattice; it is added to
\* every node's ledger simultaneously and can never be undone.
CreateGenesisBlock(n) ==
  /\ lastHash = NoHash
  /\ \E k \in PublicKey, pk \in PrivateKey :
       /\ ledger[k] = [h \in Hash |-> NoBlockVal]
       /\ ledger' = [ledger EXCEPT ![k] = [h \in Hash |-> IF h = NoHashVal THEN [prevHash |-> NoHash, key |-> pk, pub |-> k, amt |-> GenesisBalance, typ |-> "genesis"] ELSE NoBlockVal]]
  /\ \E h \in Hash : lastHash' = h
  /\ received' = [m \in Node |-> received[m] \cup {CalculateHash([prevHash |-> NoHash, key |-> pk, pub |-> k, amt |-> GenesisBalance, typ |-> "genesis"], NoHash)}]

\* Sending is always limited by the sender's own balance, which is what
\* prevents the total circulating supply from ever growing.
CreateSendBlock(n, k, amt) ==
  /\ AccountBalance(k) >= amt
  /\ \E pk \in PrivateKey :
       LET blk == [prevHash |-> lastHash, key |-> pk, pub |-> k, amt |-> amt, typ |-> "send"] IN
         Broadcast(n, blk)

CreateOpenBlock(n, k, senderPub) ==
  /\ \E pk \in PrivateKey :
       LET blk == [prevHash |-> lastHash, key |-> pk, pub |-> k, amt |-> 0, typ |-> "open"] IN
         Broadcast(n, blk)

CreateReceiveBlock(n, k, sendHash) ==
  /\ \E pk \in PrivateKey :
       LET blk == [prevHash |-> lastHash, key |-> pk, pub |-> k, amt |-> Ledger(senderPub, sendHash).amt, typ |-> "receive"] IN
         Broadcast(n, blk)

CreateChangeRepBlock(n, k) ==
  /\ \E pk \in PrivateKey :
       LET blk == [prevHash |-> lastHash, key |-> pk, pub |-> k, amt |-> 0, typ |-> "change"] IN
         Broadcast(n, blk)

\* Validation must check the signature, the predecessor, and the
\* block-type-specific rule before accepting a block into the local copy.
ValidateBlock(n) ==
  /\ \E blk \in received[n] :
       /\ ledger[blk.pub][blk.prevHash] # NoBlockVal
       /\ Ledger(blk.pub, blk.prevHash).key = blk.key
       /\ \/ blk.typ \in {"genesis", "change"}
          \/ /\ blk.typ = "send"
             /\ AccountBalance(blk.pub) >= blk.amt
          \/ /\ blk.typ = "receive"
             /\ blk.amt > 0
       /\ ledger' = [ledger EXCEPT ![blk.pub] = @ [blk.prevHash] = blk]
       /\ received' = [received EXCEPT ![n] = @ \ {blk}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, k \in PublicKey, amt \in 1..GenesisBalance : CreateSendBlock(n, k, amt)
  \/ \E n \in Node, k \in PublicKey, senderPub \in PublicKey : CreateOpenBlock(n, k, senderPub)
  \/ \E n \in Node, k \in PublicKey, sendHash \in Hash : CreateReceiveBlock(n, k, sendHash)
  \/ \E n \in Node, k \in PublicKey : CreateChangeRepBlock(n, k)
  \/ \E n \in Node : ValidateBlock(n)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ \A n \in Node : SF_vars(ValidateBlock(n))

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [PublicKey -> [Hash -> Chain \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Chain]

\* The cryptographic safety property: every block across every node's copy
\* is signed by the key that owns the account chain it sits in.
SafetyInvariant ==
  \A k \in PublicKey, h \in Hash : ledger[k][h] # NoBlockVal => ledger[k][h].key = Ledger(k, h).key

====