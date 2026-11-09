"""Run SMT-LIB using a Z3 executable, or its installed shared library."""
from __future__ import annotations
import ctypes
import ctypes.util
import os
import shutil
import subprocess
from pathlib import Path


def run_z3(smt: str, *, proofs: bool = False) -> str:
    """Return Z3's output; SMT inputs should set their own solver timeout."""
    if proofs and '(set-option :produce-proofs true)' not in smt:
        smt = '(set-option :produce-proofs true)\n' + smt
    executable = shutil.which('z3')
    if executable:
        result = subprocess.run([executable, '-in'], input=smt, text=True,
                                capture_output=True, timeout=30, check=False)
        if result.returncode:
            raise RuntimeError(f'Z3 exited with {result.returncode}:\n{result.stdout}\n{result.stderr}')
        return result.stdout
    library = os.environ.get('LIBZ3') or ctypes.util.find_library('z3')
    fallback = Path('/usr/lib/x86_64-linux-gnu/libz3.so.4')
    if not library and fallback.is_file():
        library = str(fallback)
    if not library:
        raise RuntimeError('Z3 was not found. Install Z3 or run the saved .smt2 files with z3.')
    lib = ctypes.CDLL(library)
    lib.Z3_mk_config.restype = ctypes.c_void_p
    lib.Z3_mk_context.argtypes = [ctypes.c_void_p]
    lib.Z3_mk_context.restype = ctypes.c_void_p
    lib.Z3_del_config.argtypes = [ctypes.c_void_p]
    lib.Z3_eval_smtlib2_string.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    lib.Z3_eval_smtlib2_string.restype = ctypes.c_char_p
    lib.Z3_del_context.argtypes = [ctypes.c_void_p]
    lib.Z3_set_param_value.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
    config = lib.Z3_mk_config()
    if proofs:
        lib.Z3_set_param_value(config, b'proof', b'true')
    context = lib.Z3_mk_context(config)
    lib.Z3_del_config(config)
    try:
        output = lib.Z3_eval_smtlib2_string(context, smt.encode('utf-8'))
        if output is None:
            raise RuntimeError('Z3 returned no output.')
        return output.decode('utf-8')
    finally:
        lib.Z3_del_context(context)
