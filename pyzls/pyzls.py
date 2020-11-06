from abc import ABC, abstractmethod
import subprocess
import ast
import importlib.util
from inspect import getsource
import sys
from functools import wraps
import builtins


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


def _exec(cmd):
    try:
        output = subprocess.check_output(
            cmd, stderr=subprocess.PIPE, universal_newlines=True
        )
        if output:
            print(output, file=sys.stdout)
    except subprocess.CalledProcessError as exc:
        print(f"Error {exc.returncode}: {exc.stderr}", file=sys.stderr)


def _compile_code(name, src, opt=[], libname=None, clean=False):
    with open(name + ".zls", "w" if clean else "a") as fzls:
        if libname:
            fzls.write(f"open {libname.capitalize()}")
            fzls.write(src)
            fzls.seek(0)
        _exec(
            [
                "../bin/zeluc",
                "-python",
                "-noreduce",
                "-copy",
            ]
            + opt
            + [fzls.name]
        )


def lib(libname, clean=False):
    def inner(f):
        with open(libname + ".zli", "w" if clean else "a") as fzli, open(
            libname + ".py", "w" if clean else "a"
        ) as fpyl:
            fzli.write(f"val {f.__name__}: {_ml_type(f)}\n")
            fpyl.write(getsource(f).split("\n", 1)[1])
        _exec(["../bin/zeluc", libname + ".zli"])
        if libname in sys.modules:
            importlib.reload(sys.modules[libname])

        @wraps(f)
        def wrapper(*args):
            return f(*args)

        return wrapper

    return inner


open('libtop.zli', 'w+').close()
open('libtop.py', 'w+').close()
_exec(["../bin/zeluc", "libtop.zli"])
toplib = lib("libtop")


def load(src, name="top", clean=False, scope=builtins, opt=[]):
    _compile_code(name, src, opt, clean=clean, libname="libtop")

    # Load python module as class attribute
    mod = importlib.import_module("top")
    importlib.reload(mod)
    for name, val in mod.__dict__.items():
        if not name.startswith("__"):
            setattr(scope, name, val)
