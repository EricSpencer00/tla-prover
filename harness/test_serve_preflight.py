import io
import json
import sys
from concurrent.futures import ThreadPoolExecutor
import threading

import pytest
from tools.smoke import serve_preflight as preflight


def test_protected_launcher_exports_readiness_log():
    launcher = open('tools/protected_transport_controls.pbs', encoding='utf-8').read()
    assert 'for attempt in range(48)' in launcher
    assert 'exc.code < 500 or exc.code >= 600' in launcher
    assert 'export VLLM_LOG=' in launcher


def test_parallel_long_probes(monkeypatch):
    monkeypatch.setattr(sys, 'argv', ['preflight', '--base-url', 'http://test/v1',
                                      '--model', 'test', '--concurrency', '8'])
    monkeypatch.setattr(preflight.urllib.request, 'urlopen',
                        lambda *a, **k: io.BytesIO(json.dumps({'data': [{'id': 'test'}]}).encode()))
    barrier = threading.Barrier(8)
    def post(url, body):
        if body['max_tokens'] != 32:
            barrier.wait(timeout=5)
        return {'choices': [{'message': {'content': 'OK'}}]}
    monkeypatch.setattr(preflight, '_post', post)
    preflight.main()


def test_empty_long_response_is_failure(monkeypatch):
    monkeypatch.setattr(sys, 'argv', ['preflight', '--base-url', 'http://test/v1', '--model', 'test'])
    monkeypatch.setattr(preflight.urllib.request, 'urlopen',
                        lambda *a, **k: io.BytesIO(b'{"data":[{"id":"test"}]}'))
    monkeypatch.setattr(preflight, '_post', lambda url, body:
                        {'choices': [{'message': {'content': 'OK' if body['max_tokens'] == 32 else ''}}]})
    with pytest.raises(ValueError, match='no completion'):
        preflight.main()
