from pathlib import Path


PBS = Path("tools/protected_checkpoint_preflight_polaris_v3.pbs").read_text()


def test_v3_binds_the_verified_isolated_xgrammar_closure():
    assert "XGRAMMAR_SITE=/grand/EVITA/eric-spencer/tla-checkpoint-preflight-deps/xgrammar-0.2.2-cp312" in PBS
    assert '--xgrammar-site "$XGRAMMAR_SITE"' in PBS


def test_v3_keeps_the_preflight_bounded_and_checkpoint_faithful():
    assert "#PBS -l select=1:system=polaris:ngpus=1" in PBS
    assert "#PBS -l walltime=00:15:00" in PBS
    assert "policy_optimizer.pt" in PBS
    assert "sha256sum -c SHA256SUMS" in PBS
