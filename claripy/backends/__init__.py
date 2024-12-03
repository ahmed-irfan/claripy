from __future__ import annotations

from .backend import Backend
from .backend_concrete import BackendConcrete
from .backend_vsa import BackendVSA
from .backend_z3 import BackendZ3

concrete = BackendConcrete()
z3 = BackendZ3()
vsa = BackendVSA()

try:
    import yices
    _has_yices = True
except ImportError:
    _has_yices = False

if _has_yices:
    from .backend_yices import BackendYices
    yices = BackendYices()
    all_backends = [concrete, z3, yices, vsa]
else:
    all_backends = [concrete, z3, vsa]

backends_by_type = {b.__class__.__name__: b for b in all_backends}

__all__ = (
    "Backend",
    "BackendZ3",
    "BackendYices",
    "BackendConcrete",
    "BackendVSA",
    "all_backends",
    "backends_by_type",
    "concrete",
    "z3",
    "yices",
    "vsa",
)
