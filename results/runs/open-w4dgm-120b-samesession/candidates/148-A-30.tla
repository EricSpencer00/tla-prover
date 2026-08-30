---- MODULE Nano ----
EXTENDS Naturals, Sequences

\* Ed25519 signatures are modeled abstractly: Signed is an opaque envelope
\* that pairs the signer with the block data; no payload, no randomness.
Signed == [by: PrivateKey, data: [ptype: {"genesis", "send", "open", "receive", "change"},
                                  account: PublicKey, linked: Hash]]

\* Block chains form a lattice: each account's chain is an ordered history of
\* signed blocks whose hashes are derived from the previous hash, so the
\* block order is recorded in the hashes themselves, not in a separate log.
ChainOf(a) == {b.account : b \in {x \in {y \in Signed : y.by \in PrivateKey} :
                                 PublicKeyOf[x.by] = a}}

\* An account's balance is the net effect of its chain's blocks, summed from
\* the chain's genesis onward so the invariant below stays tied to the chain.
NetInChain(a) ==
  LET ChainSeq(S) ==
         IF S = {} THEN <<>>
         ELSE LET b == CHOOSE x \in S : TRUE IN <<b>> \o ChainSeq(S \ {b})
  IN LET seq == ChainSeq(ChainOf(a))
     IN LET Amount(i) ==
            IF seq[i].ptype = "send" THEN -GenesisBalance
            ELSE IF seq[i].ptype = "open" THEN GenesisBalance
            ELSE IF seq[i].ptype = "receive" THEN GenesisBalance
            ELSE 0
     IN LET F[k \in 1..Len(seq)] ==
            IF k = Len(seq) THEN Amount(k)
            ELSE Amount(k) + F[k + 1]
     IN IF seq = <<>> THEN 0 ELSE F[1]

RECURSIVE SumFn(_, _)
SumFn(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumFn(f, S \ {x})

\* Ledger and Received model the network separately, so two nodes may disagree
\* about whether a block is committed, or about which blocks landed first.
Node == "node"
Hash == "hash"
NoHashVal == "nohash"
NoBlock == "noblock"
NoHash == NoHashVal
NoBlockVal == NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Signed \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Signed]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Cryptographic primitives are uninterpreted except for type signatures, so
\* secrecy and collision resistance are assumed properties of the primitives.
CalculateHash == CalculateHashImpl
PublicKeyOf == PUBLICKEYOF

\* The genesis block is seeded on every node at once and never again.
CreateGenesis ==
  /\ lastHash = NoHash
  /\ \E pr \in PrivateKey :
       LET b == [ptype |-> "genesis", account |-> PublicKeyOf[pr], linked |-> NoHash]
           s == [by |-> pr, data |-> b]
           h == CalculateHash(<<b>>, NoHash)
       IN /\ lastHash' = h
          /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = s]]
          /\ UNCHANGED received

CreateAccountBlock ==
  /\ \E src \in Node, pr \in PrivateKey, rec \in PublicKey :
       /\ PublicKeyOf[pr] \in ChainOf(ledger[src][lastHash].data.account)
       /\ \E h \in Hash :
            /\ ledger[src][h] # NoBlockVal
            /\ ledger[src][h].data.ptype \notin {"genesis", "open"}
            /\ NetInChain(ledger[src][h].data.account) - GenesisBalance >= 0
            /\ LET b == [ptype |-> "send", account |-> PublicKeyOf[pr],
                         linked |-> h]
                   s == [by |-> pr, data |-> b]
                   nh == CalculateHash(<<b>>, lastHash)
               IN /\ lastHash' = nh
                  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![nh] = s]]
                  /\ received' = [received EXCEPT ![src] = received[src] \cup {s}]
    /\ UNCHANGED <<>>

CreateOpenBlock ==
  /\ \E nd \in Node, sender \in PublicKey :
       /\ \E h \in Hash :
            /\ ledger[nd][h] # NoBlockVal
            /\ ledger[nd][h].data.ptype = "send"
            /\ ledger[nd][h].data.account = sender
            /\ LET b == [ptype |-> "open", account |-> sender,
                         linked |-> h]
                   s == [by |-> CHOOSE pr \in PrivateKey :
                               PublicKeyOf[pr] = sender, data |-> b]
                   nh == CalculateHash(<<b>>, lastHash)
               IN /\ lastHash' = nh
                  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![nh] = s]]
                  /\ received' = [received EXCEPT ![nd] = received[nd] \cup {s}]
    /\ UNCHANGED <<>>

CreateReceiveBlock ==
  /\ \E nd \in Node, src \in Node, h \in Hash :
       /\ ledger[nd][h] # NoBlockVal
       /\ ledger[nd][h].data.ptype = "send"
       /\ ledger[nd][h].data.account \in ChainOf(ledger[src][lastHash].data.account)
       /\ NetInChain(ledger[nd][h].data.account) - GenesisBalance >= 0
       /\ LET b == [ptype |-> "receive", account |-> ledger[nd][h].data.account,
                    linked |-> h]
              s == [by |-> CHOOSE pr \in PrivateKey :
                              PublicKeyOf[pr] = ledger[nd][h].data.account, data |-> b]
              nh = CalculateHash(<<b>>, lastHash)
          IN /\ lastHash' = nh
             /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![nh] = s]]
             /\ received' = [received EXCEPT ![nd] = received[nd] \cup {s}]
    /\ UNCHANGED <<>>

CreateChangeRepresentative ==
  /\ \E nd \in Node, pr \in PrivateKey :
       LET b == [ptype |-> "change", account |-> PublicKeyOf[pr], linked |-> lastHash]
           s == [by |-> pr, data |-> b]
           h == CalculateHash(<<b>>, lastHash)
       IN /\ lastHash' = h
          /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = s]]
          /\ received' = [received EXCEPT ![nd] = received[nd] \cup {s}]

ValidateBlock ==
  /\ \E nd \in Node, s \in received[nd] :
       /\ received' = [received EXCEPT ![nd] = received[nd] \ {s}]
       /\ IF ledger[nd][s.by].data.account = s.data.account
             /\ ledger[nd][s.data.linked] # NoBlockVal
             /\ (s.data.ptype = "send" => NetInChain(s.data.account) - GenesisBalance >= 0)
             /\ (s.data.ptype \in {"open", "receive"}
                   => ledger[nd][s.data.linked].data.ptype = "send")
             /\ (s.data.ptype \in {"receive", "open"}
                   => \A h \in Hash : (ledger[nd][h] # NoBlockVal
                                      /\ ledger[nd][h].data.linked = s.data.linked)
                        => ledger[nd][h].data.ptype # "receive")
            THEN ledger' = [ledger EXCEPT ![nd][s.by] = s]
            ELSE ledger' = ledger
       /\ UNCHANGED lastHash

Next == CreateGenesis \/ CreateAccountBlock \/ CreateOpenBlock \/ CreateReceiveBlock
        \/ CreateChangeRepresentative \/ ValidateBlock

Spec == Init /\ [][Next]_vars

\* The cryptographic invariant is the only thing keeping a forged, out-of-chain,
\* double-spend block out of a node's replicated ledger.
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal
                     => ledger[n][h].by \in PrivateKey
                        /\ ledger[n][h].data.account = PublicKeyOf[ledger[n][h].by]

====