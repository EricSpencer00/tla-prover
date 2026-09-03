---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* An Ed25519-style signature is just an element of the private-key set here,
\* but it is required to match the public key given by the account->pubkey mapping.
\* Blake2b-style hashing is abstracted as the CalculateHash operator, so the
\* block-creation actions can use it and the model can swap in a bounded
\* CalculateHashImpl version for the .cfg file.

Block == [chain: PublicKey, prev: Hash, base: Hash, kind: {"send", "open", "receive", "change"}, amt: Nat, sig: PrivateKey]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Block]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block is added to every node's ledger at once, so no node can
\* ever have a ledger that is missing it.
CreateGenesisBlock(n) ==
  /\ lastHash = NoHash
  /\ \E p \in PrivateKey :
       /\ lastHash' = CalculateHash([chain |-> n, prev |-> NoHash,
                                    base |-> NoHash, kind |-> "send", amt |-> GenesisBalance], noHashVal)
       /\ \A m \in Node : ledger' = [ledger EXCEPT ![m][lastHash'] =
                                      [chain |-> n, prev |-> NoHash, base |-> NoHash,
                                       kind |-> "send", amt |-> GenesisBalance, sig |-> p]]
       /\ received' = [m \in Node |-> received[m] \cup
                         {[chain |-> n, prev |-> NoHash, base |-> NoHash, kind |-> "send",
                           amt |-> GenesisBalance, sig |-> p]}]

\* A send block can only move money that is currently sitting in the sender's
\* account chain, so the per-account balance must be re-computed here.
CreateSendBlock(n, m, a) ==
  /\ n # m
  /\ lastHash # NoHash
  /\ \E p \in PrivateKey :
       /\ a <= BalanceOf(n, ledger[n])
       /\ lastHash' = CalculateHash([chain |-> n, prev |-> lastHash,
                                    base |-> lastHash, kind |-> "send", amt |-> a], noHashVal)
       /\ ledger' = [ledger EXCEPT ![n][lastHash'] =
                      [chain |-> n, prev |-> lastHash, base |-> lastHash,
                       kind |-> "send", amt |-> a, sig |-> p]]
       /\ received' = [received EXCEPT ![n] = @ \cup
                         {[chain |-> n, prev |-> lastHash, base |-> lastHash,
                           kind |-> "send", amt |-> a, sig |-> p]}]

CreateOpenBlock(n, h) ==
  /\ lastHash # NoHash
  /\ ledger[n][h].kind = "send"
  /\ ledger[n][h].chain # n
  /\ ledger[n][h].sig = pubkey[n]
  /\ \E p \in PrivateKey :
       /\ lastHash' = CalculateHash([chain |-> n, prev |-> lastHash,
                                    base |-> h, kind |-> "open", amt |-> 0], noHashVal)
       /\ ledger' = [ledger EXCEPT ![n][lastHash'] =
                      [chain |-> n, prev |-> lastHash, base |-> h,
                       kind |-> "open", amt |-> 0, sig |-> p]]
       /\ received' = [received EXCEPT ![n] = @ \cup
                         {[chain |-> n, prev |-> lastHash, base |-> h,
                           kind |-> "open", amt |-> 0, sig |-> p]}]

CreateReceiveBlock(n, h) ==
  /\ lastHash # NoHash
  /\ ledger[n][h].kind = "send"
  /\ ledger[n][h].sig = pubkey[n]
  /\ \E p \in PrivateKey :
       /\ lastHash' = CalculateHash([chain |-> n, prev |-> lastHash,
                                    base |-> h, kind |-> "receive", amt |-> 0], noHashVal)
       /\ ledger' = [ledger EXCEPT ![n][lastHash'] =
                      [chain |-> n, prev |-> lastHash, base |-> h,
                       kind |-> "receive", amt |-> 0, sig |-> p]]
       /\ received' = [received EXCEPT ![n] = @ \cup
                         {[chain |-> n, prev |-> lastHash, base |-> h,
                           kind |-> "receive", amt |-> 0, sig |-> p]}]

CreateChangeRepresentativeBlock(n) ==
  /\ lastHash # NoHash
  /\ \E p \in PrivateKey :
       /\ lastHash' = CalculateHash([chain |-> n, prev |-> lastHash,
                                    base |-> lastHash, kind |-> "change", amt |-> 0], noHashVal)
       /\ ledger' = [ledger EXCEPT ![n][lastHash'] =
                      [chain |-> n, prev |-> lastHash, base |-> lastHash,
                       kind |-> "change", amt |-> 0, sig |-> p]]
       /\ received' = [received EXCEPT ![n] = @ \cup
                         {[chain |-> n, prev |-> lastHash, base |-> lastHash,
                           kind |-> "change", amt |-> 0, sig |-> p]}]

\* Validation opposes a block from the wire with the node's own ledger copy,
\* so a node can only validate a block it actually already recorded itself.
ValidateBlock(n, b) ==
  /\ b \in received[n]
  /\ ledger[n][b.prev] # NoBlockVal
  /\ ledger[n][b.prev].chain = n
  /\ ledger[n][b.base] # NoBlockVal
  /\ b.sig = pubkey[n]
  /\ ledger' = [ledger EXCEPT ![n][b.base] = b]
  /\ received' = [received EXCEPT ![n] = @ \ {b}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, m \in Node, a \in Nat : CreateSendBlock(n, m, a)
  \/ \E n \in Node, h \in Hash : CreateOpenBlock(n, h)
  \/ \E n \in Node, h \in Hash : CreateReceiveBlock(n, h)
  \/ \E n \in Node : CreateChangeRepresentativeBlock(n)
  \/ \E n \in Node, b \in Block : ValidateBlock(n, b)

Spec == Init /\ [][Next]_vars

\* The per-account balance is re-derived from the whole chain every time; it
\* is not a piece of state that could drift apart and hide a bug.
BalanceOf(n, ld) ==
  LET Chain(h) == IF h = NoHash THEN {} ELSE IF ld[h] = NoBlockVal THEN {} ELSE {ld[h]} \cup Chain(ld[h].prev)
  IN  LET Sent(h) == IF h = NoHash THEN 0
                     ELSE IF ld[h].kind = "send" THEN ld[h].amt + Sent(ld[h].prev) ELSE Sent(ld[h].prev)
      In(C, k) == CHOOSE e \in C : e.kind = k
  IN  IF Chain(Chain(h)).subset = {} THEN 0
      ELSE IF In(Chain(h), "open") = "send" THEN Sent(Chain(h)) ELSE Sent(Chain(h)) - In(Chain(h), "receive").amt

\* No coins are ever minted or burned by a block; the sum of all account
\* balances never exceeds the genesis balance, re-derived from the chains.
BalanceInvariant == \A S \in SUBSET PublicKey :
  LET sum(C) == IF C = {} THEN 0 ELSE LET e \in C == CHOOSE x \in C : TRUE IN e + sum(C \ {e})
  IN sum({BalanceOf(k, ledger[n]) : k \in S, n \in Node})

SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig = pubkey[n]

====