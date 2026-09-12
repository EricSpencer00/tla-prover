---- MODULE W4Od3m5p5t2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Fund, Payout, Quorum, Voters, Round, Approval, PayoutLatch, ApprovalLatch

VARIABLES balance, payout, quorum, votes, round, approval, payoutLatch, approvalLatch

vars == <<balance, payout, quorum, votes, round, approval, payoutLatch, approvalLatch>>

Init ==
    /\ balance = Fund
    /\ payout = 0
    /\ quorum = Quorum
    /\ votes = [][]
    /\ round = 0
    /\ approval = FALSE
    /\ payoutLatch = 0
    /\ approvalLatch = 0

Next ==
    /\ IF payout > 0
        /\ payout' = payout
        /\ balance' = balance - payout
        /\ payout' = 0
        /\ payoutLatch' = 1
    /\ ELSE
        /\ payout' = 0
        /\ balance' = balance
        /\ payoutLatch' = payoutLatch
    /\ /\ IF approval
        /\ approval' = approval
        /\ approvalLatch' = approvalLatch
    /\ ELSE
        /\ approval' = FALSE
        /\ approvalLatch' = approvalLatch
    /\ /\ IF votes = [][]
        /\ votes' = [][]
        /\ round' = 0
        /\ approval' = FALSE
        /\ payoutLatch' = 0
        /\ approvalLatch' = 0
    /\ ELSE
        /\ votes' = [][]
        /\ round' = round + 1
        /\ approval' = FALSE
        /\ payoutLatch' = 0
        /\ approvalLatch' = 0
    /\ /\ UNCHANGED <<balance, payout, quorum, round, approval, payoutLatch, approvalLatch>>

Spec == Init /\ [][Next]_vars

PayOnlyIfApproved ==
    /\ (payout > 0) => (approvalLatch > 0)
    /\ (payout > 0) => (payoutLatch < 2)
    /\ (payout > 0) => (payoutLatch > 0)
    /\ (payout = 0) => (payoutLatch = 0)
    /\ (payout = 0) => (approvalLatch > 0)
    /\ (payout = 0) => (approvalLatch < 2)
    /\ (payout = 0) => (approvalLatch > 0)

====