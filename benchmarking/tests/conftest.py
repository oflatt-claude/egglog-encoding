"""Shared boundary fixtures for benchmark tooling tests."""

from __future__ import annotations

import gzip
from pathlib import Path
from typing import Any

import pytest


@pytest.fixture
def non_utf8_text_defaults(monkeypatch: pytest.MonkeyPatch) -> None:
    """Model a cp1252 host without changing explicitly requested text encodings."""
    path_open, gzip_open = Path.open, gzip.open

    def open_path(path: Path, mode: str = "r", *args: Any, **kwargs: Any) -> Any:
        if "b" not in mode and kwargs.get("encoding") in (None, "locale"):
            kwargs["encoding"] = "cp1252"
        return path_open(path, mode, *args, **kwargs)

    def open_gzip(path: Any, mode: str = "rb", *args: Any, **kwargs: Any) -> Any:
        if "t" in mode and kwargs.get("encoding") in (None, "locale"):
            kwargs["encoding"] = "cp1252"
        return gzip_open(path, mode, *args, **kwargs)

    monkeypatch.setattr(Path, "open", open_path)
    monkeypatch.setattr(gzip, "open", open_gzip)
