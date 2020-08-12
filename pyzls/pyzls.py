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


def _compile_code(name, src, opt=[], libname=None, clean=False):
    with open(name + ".zls", "w" if clean else "a") as fzls:
        if libname:
            fzls.write(f"open {libname.capitalize()}")
            fzls.write(src)
            fzls.seek(0)
        subprocess.check_call(
            ["../bin/zeluc", "-python", "-noreduce", "-copy",] + opt + [fzls.name]
        )


def lib(libname):
    def inner(f):
        with open(libname + "zli", "a") as fzli, open(libname + ".py", "w") as fpyl:
            fzli.write(f"val {f}: {_ml_type(f)}\n")
            fpyl.write(getsource(f).split("\n", 1)[1])
        subprocess.check_call(["../bin/zeluc", libname + ".zli"])
        if libname in sys.modules:
            importlib.reload(sys.modules[libname])

        @wraps(f)
        def wrapper(*args):
            return f(*args)

        return wrapper

    return inner


toplib = lib("libtop")


def load(src, name="top", clean=False, scope=builtins, opt=[]):
    _compile_code(name, src, opt, clean=clean, libname="libtop")

    # Load python module as class attribute
    spec = importlib.util.spec_from_file_location("zlpyc", "top.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    for name, val in mod.__dict__.items():
        if not name.startswith("__"):
            setattr(scope, name, val)
