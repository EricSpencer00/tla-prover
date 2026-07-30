---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

(* The Nano blockchain's block-lattice accounts and their ordering are kept  *)
(* in separate nodes' ledgers.  Ed25519-style signatures and Blake2b-style   *)
(* hashes are modeled abstractly: a hash is computed by an external constant *)
(* operator, and a signature is simply the private key that produced it.    *)
(* The invariant protects confidentiality by asserting every block is      *)
(* signed by the account that owns the chain it appears in.                  *)

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

RECURSIVE ChainBalance(_, _)
ChainBalance(h, acc) ==
  IF h = NoHashVal THEN 0
  ELSE IF NoBlockVal.h = NoBlock THEN 0
  ELSE IF NoBlockVal.h.account = acc
          THEN NoBlockVal.h.amount + ChainBalance(NoBlockVal.h.previous, acc)
       ELSE ChainBalance(NoBlockVal.h.previous, acc)

RECURSIVE LedgerBalance(_)
LedgerBalance(acc) ==
  IF acc = NoHashVal THEN 0
  ELSE ChainBalance(NoBlockVal.acc.hash, acc) + LedgerBalance(NoBlockVal.acc.next)

RECURSIVE ChainCount(_, _)
ChainCount(h, acc) ==
  IF h = NoHashVal THEN 0
  ELSE IF NoBlockVal.h = NoBlock THEN 0
  ELSE IF NoBlockVal.h.account = acc
          THEN 1 + ChainCount(NoBlockVal.h.previous, acc)
       ELSE ChainCount(NoBlockVal.h.previous, acc)

\* Funds are never created or destroyed: the total across all account chains
\* stays at the genesis balance.  This is separate from the signature check.
BalanceConservation == LedgerBalance(NoHashVal) = GenesisBalance

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

Broadcast(b) ==
  { [to |-> n, block |-> b] : n \in Node }

CreateBlock(n, typ, tgt) ==
  /\ lastHash # NoHashVal
  /\ LET b ==
       [hash |-> CalculateHash(tgt, lastHash), account |-> n, type |-> typ,
        previous |-> lastHash, source |-> tgt, target |-> n,
        amount |-> IF typ = "send" THEN 1 ELSE 0, signer |-> tgt] IN
     /\ lastHash' = b.hash
     /\ ledger' = [x \in Node |-> [ledger[x] EXCEPT ![b.hash] = b]]
     /\ received' = [x \in Node |-> received[x] \cup Broadcast(b)]

\* A node must sign every block on its own chain; the validator checks that.
ValidateBlock(n, r) ==
  /\ r.to = n
  /\ r.block.type \in {"send", "open", "receive", "changeRepresentative"}
  /\ LET b == r.block IN
       /\ ledger[n][b.previous] # NoBlockVal
       /\ b.account = n
       /\ b.signer = PrivateKey[n]
       /\ b.type = "send" => b.amount <= ChainBalance(b.previous, n)
       /\ b.type = "open" => ledger[n][b.source] # NoBlockVal
                              /\ ledger[n][b.source].type = "send"
                              /\ ledger[n][b.source].target = n
       /\ b.type = "receive" => ledger[n][b.source] # NoBlockVal
                                 /\ ledger[n][b.source].type = "send"
                                 /\ ledger[n][b.source].target = n
       /\ ledger[n][b.hash] = NoBlockVal
       /\ ledger' = [ledger EXCEPT ![n][b.hash] = b]
  /\ received' = [received EXCEPT ![n] = received[n] \ {r}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateBlock(n, "genesis", n)
  \/ \E n \in Node, tgt \in PrivateKey : CreateBlock(n, "send", tgt)
  \/ \E n \in Node : CreateBlock(n, "open", n)
  \/ \E n \in Node : CreateBlock(n, "receive", n)
  \/ \E n \in Node : CreateBlock(n, "changeRepresentative", n)
  \/ \E n \in Node, r \in received[n] : ValidateBlock(n, r)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> [hash: Hash, account: Node, type: {"genesis", "send", "open", "receive", "changeRepresentative"},
                                previous: Hash \cup {NoHashVal}, source: PrivateKey,
                                target: Node, amount: Nat, signer: PrivateKey]]]
  /\ received \subseteq [to: Node, block: [hash: Hash, account: Node, type: {"genesis", "send", "open", "receive", "changeRepresentative"},
                                          previous: Hash \cup {NoHashVal}, source: PrivateKey,
                                          target: Node, amount: Nat, signer: PrivateKey]]

\* Signature authenticity: every recorded block is signed by the account that
\* actually owns the chain it lives in.
SafetyInvariant ==
  \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal =>
     ledger[n][h].signer = PrivateKey[ledger[n][h].account]

====