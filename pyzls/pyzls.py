from abc import ABC, abstractmethod
import subprocess
import ast
from tempfile import NamedTemporaryFile
from os.path import splitext, basename, dirname
import importlib.util
from typing import Dict, Any
from inspect import getsource
import sys
from functools import wraps
import builtins
import runpy


class Node(ABC):
    @abstractmethod
    def __init__(self):
        pass

    @abstractmethod
    def reset(self, *args):
        pass

    @abstractmethod
    def step(self):
        pass


class CNode(Node):
    @abstractmethod
    def copy(self):
        pass


def _ml_type(f):
    ty = " * ".join(
        [
            t.__name__ if hasattr(t, "__name__") else str(t)
            for a, t in f.__annotations__.items()
            if a != "return"
        ]
    )
    r = f.__annotations__["return"]
    ty += f' -> {r.__name__ if hasattr(r, "__name__") else str(r)}'
    return ty


def _compile_libs(libs):
    for libname, lib in libs.items():
        with open(libname + ".zli", "w") as fzli, open(libname + ".py", "w") as fpyl:
            for f, d in lib.items():
                fzli.write(f'val {f}: {d["type"]}\n')
                fpyl.write(d["py"])
            fzli.seek(0)
            fpyl.seek(0)
            subprocess.check_call(["../bin/zeluc", fzli.name])
            if libname in sys.modules:
                importlib.reload(sys.modules[libname])


def _compile_code(name, src, opt=[], libname=None):
    with open(name + ".zls", "w") as fzls:
        if libname:
            fzls.write(f"open {libname.capitalize()}")
            fzls.write(src)
            fzls.seek(0)
        subprocess.check_call(
            ["../bin/zeluc", "-python", "-noreduce", "-copy",] + opt + [fzls.name]
        )


_libs: Dict[str, Any] = {"libtop": {}}


def lib(libname):
    def inner(f):
        if libname not in _libs:
            _libs[libname] = {}
        _libs[libname][f.__name__] = {
            "type": _ml_type(f),
            "py": getsource(f).split("\n", 1)[1],
        }

        @wraps(f)
        def wrapper(*args):
            return f(*args)

        return wrapper

    return inner


toplib = lib("libtop")


def load(src, scope=builtins, opt=[]):
    _compile_libs(_libs)
    _compile_code("top", src, opt, libname="libtop")

    # Load python module as class attribute
    spec = importlib.util.spec_from_file_location("zlpyc", "top.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    for name, val in mod.__dict__.items():
        if not name.startswith("__"):
            setattr(scope, name, val)
