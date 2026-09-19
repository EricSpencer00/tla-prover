"""Small, non-interactive bridge from a TLAKit notebook to cluster runners.

The bridge deliberately separates SSH reachability from a TLAKit HTTP runner:
neither one is reported as model/proof success.  It never prompts for MFA and
does not submit work; the notebook can therefore probe Polaris and Sophia
without accidentally starting a scheduler job.
"""

from __future__ import annotations

import os
import subprocess
from dataclasses import dataclass
from typing import Mapping


@dataclass(frozen=True)
class ClusterStatus:
    name: str
    ssh_alias: str
    ssh_reachable: bool
    hostname: str | None
    tlakit_version: str | None
    endpoint: str | None
    endpoint_healthy: bool | None
    detail: str


@dataclass(frozen=True)
class ClusterProcess:
    """A deliberately small, non-sensitive view of one user-owned process."""

    pid: int
    state: str
    cpu_percent: float
    memory_percent: float
    elapsed_seconds: int
    command: str
    purpose: str


@dataclass(frozen=True)
class ClusterBackend:
    name: str
    ssh_alias: str
    endpoint: str | None = None

    @classmethod
    def from_env(
        cls, name: str, env: Mapping[str, str] | None = None
    ) -> "ClusterBackend":
        values = os.environ if env is None else env
        key = name.upper()
        return cls(
            name=name,
            ssh_alias=values.get(f"TLAKIT_{key}_SSH", name.lower()),
            endpoint=values.get(f"TLAKIT_{key}_ENDPOINT") or None,
        )

    def probe(self, timeout: float = 8.0) -> ClusterStatus:
        """Probe an existing SSH login and optional TLAKit HTTP endpoint.

        BatchMode keeps this suitable for notebooks: expired MFA becomes a
        truthful unavailable status instead of a hidden interactive prompt.
        """
        command = [
            "ssh",
            "-o",
            "BatchMode=yes",
            "-o",
            f"ConnectTimeout={max(1, int(timeout))}",
            self.ssh_alias,
            "hostname; python3 -c 'import tlakit; print(tlakit.__version__)'",
        ]
        try:
            completed = subprocess.run(
                command,
                check=False,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return ClusterStatus(
                self.name,
                self.ssh_alias,
                False,
                None,
                None,
                self.endpoint,
                self._endpoint_health(timeout),
                str(exc),
            )

        lines = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
        reachable = completed.returncode == 0
        detail = "ready" if reachable else self._brief_error(completed.stderr)
        return ClusterStatus(
            self.name,
            self.ssh_alias,
            reachable,
            lines[0] if reachable and lines else None,
            lines[1] if reachable and len(lines) > 1 else None,
            self.endpoint,
            self._endpoint_health(timeout),
            detail,
        )

    def _endpoint_health(self, timeout: float) -> bool | None:
        if not self.endpoint:
            return None
        try:
            from tlakit.remote import RemoteRunner

            RemoteRunner(endpoint=self.endpoint, timeout=timeout).health()
        except Exception:  # A probe reports failure; it does not hide the run.
            return False
        return True

    def processes(self, timeout: float = 8.0) -> list[ClusterProcess]:
        """Return safe process metadata for this user's research services.

        The remote command is fixed, batch-only, and scoped to the SSH user's
        processes. It returns command names and resource counters, never full
        argv strings, environment variables, scheduler arguments, or logs.
        This is a status view: it cannot submit, stop, or modify a job.
        """
        command = [
            "ssh",
            "-o",
            "BatchMode=yes",
            "-o",
            f"ConnectTimeout={max(1, int(timeout))}",
            self.ssh_alias,
            (
                "ps -u \"$(id -u)\" -o pid=,state=,pcpu=,pmem=,etimes=,comm= "
                "| awk '$6 ~ /^(python|python3|jupyter|cloudflared|tlakit|srun|sbatch|qsub|torchrun|accelerate)$/ {print}'"
            ),
        ]
        try:
            completed = subprocess.run(
                command,
                check=False,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
        except (OSError, subprocess.TimeoutExpired):
            return []
        if completed.returncode != 0:
            return []

        processes: list[ClusterProcess] = []
        for line in completed.stdout.splitlines():
            fields = line.split()
            if len(fields) != 6:
                continue
            try:
                pid, state = int(fields[0]), fields[1]
                cpu, memory = float(fields[2]), float(fields[3])
                elapsed = int(fields[4])
            except ValueError:
                continue
            command_name = fields[5]
            processes.append(
                ClusterProcess(
                    pid=pid,
                    state=state,
                    cpu_percent=cpu,
                    memory_percent=memory,
                    elapsed_seconds=elapsed,
                    command=command_name,
                    purpose=self._process_purpose(command_name),
                )
            )
        return processes

    @staticmethod
    def _process_purpose(command: str) -> str:
        if command in {"jupyter", "python", "python3", "tlakit"}:
            return "Python or TLAKit service"
        if command == "cloudflared":
            return "Encrypted web tunnel"
        if command in {"srun", "sbatch", "qsub"}:
            return "Scheduler process"
        if command in {"torchrun", "accelerate"}:
            return "Training launcher"
        return "Research process"

    @staticmethod
    def _brief_error(stderr: str) -> str:
        lines = [line.strip() for line in stderr.splitlines() if line.strip()]
        return lines[-1][:240] if lines else "SSH probe failed"


def default_backends(env: Mapping[str, str] | None = None) -> list[ClusterBackend]:
    """Return the two project backends in a stable display order."""
    return [
        ClusterBackend.from_env("Polaris", env),
        ClusterBackend.from_env("Sophia", env),
    ]
