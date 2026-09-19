from __future__ import annotations

from subprocess import CompletedProcess, TimeoutExpired

from tools.tlakit_cluster_backend import ClusterBackend, default_backends


def test_default_backends_can_be_overridden_without_secrets():
    backends = default_backends(
        {
            "TLAKIT_POLARIS_SSH": "polaris-test",
            "TLAKIT_POLARIS_ENDPOINT": "http://127.0.0.1:8765",
        }
    )
    assert [(item.name, item.ssh_alias) for item in backends] == [
        ("Polaris", "polaris-test"),
        ("Sophia", "sophia"),
    ]
    assert backends[0].endpoint == "http://127.0.0.1:8765"
    assert backends[1].endpoint is None


def test_probe_reports_remote_tlakit(monkeypatch):
    def fake_run(*args, **kwargs):
        return CompletedProcess(args[0], 0, "polaris-login\n0.1.1\n", "")

    monkeypatch.setattr("tools.tlakit_cluster_backend.subprocess.run", fake_run)
    status = ClusterBackend("Polaris", "polaris").probe()
    assert status.ssh_reachable is True
    assert status.hostname == "polaris-login"
    assert status.tlakit_version == "0.1.1"
    assert status.endpoint_healthy is None


def test_probe_turns_expired_auth_into_status(monkeypatch):
    def fake_run(*args, **kwargs):
        raise TimeoutExpired(args[0], kwargs["timeout"])

    monkeypatch.setattr("tools.tlakit_cluster_backend.subprocess.run", fake_run)
    status = ClusterBackend("Sophia", "sophia").probe(timeout=1)
    assert status.ssh_reachable is False
    assert status.hostname is None
    assert "timed out" in status.detail


def test_processes_return_safe_metadata_only(monkeypatch):
    def fake_run(*args, **kwargs):
        return CompletedProcess(
            args[0],
            0,
            "123 S 1.5 0.2 42 python\n456 S 0.0 0.1 99 cloudflared\n",
            "",
        )

    monkeypatch.setattr("tools.tlakit_cluster_backend.subprocess.run", fake_run)
    processes = ClusterBackend("Polaris", "polaris").processes()
    assert [item.pid for item in processes] == [123, 456]
    assert processes[0].purpose == "Python or TLAKit service"
    assert processes[1].purpose == "Encrypted web tunnel"
