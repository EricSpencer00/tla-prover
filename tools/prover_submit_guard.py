"""Atomically claim a stable experiment/payload identity before qsub.

The claim is deliberately persistent: a second invocation for the same
identity returns the original owner/handle instead of submitting again, while
an identity collision fails closed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import socket
import sys
import time


def identity_hash(identity):
    return hashlib.sha256(identity.encode()).hexdigest()


def claim(state_dir, identity, owner=None):
    state_dir = Path(state_dir)
    state_dir.mkdir(parents=True, exist_ok=True)
    key = identity_hash(identity)
    path = state_dir / f'{key}.json'
    record = {'identity': identity, 'identity_sha256': key,
              'owner': owner or os.environ.get('USER', 'unknown'),
              'host': socket.gethostname(), 'claimed_unix': time.time()}
    payload = (json.dumps(record, sort_keys=True) + '\n').encode()
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        try:
            existing = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            raise RuntimeError(f'claim exists but is unreadable: {path}') from exc
        if existing.get('identity') != identity or existing.get('identity_sha256') != key:
            raise RuntimeError(f'identity collision: {path}')
        return {'status': 'existing', 'path': str(path), 'claim': existing}
    with os.fdopen(fd, 'wb') as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    return {'status': 'claimed', 'path': str(path), 'claim': record}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('state_dir', type=Path)
    parser.add_argument('identity')
    parser.add_argument('--owner')
    args = parser.parse_args()
    try:
        print(json.dumps(claim(args.state_dir, args.identity, args.owner), sort_keys=True))
    except RuntimeError as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(2)


if __name__ == '__main__':
    main()
