from abc import ABC, abstractmethod
import subprocess
import ast
from tempfile import NamedTemporaryFile
from os.path import splitext, basename, dirname
import importlib.util
from typing import Dict
from inspect import getsource
import sys
from functools import wraps


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


_pyzlslib: Dict[str, str] = {}


def ml_type(f):
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


def zllib(f):
    _pyzlslib[f.__name__] = {"type": ml_type(f), "py": getsource(f).split("\n", 1)[1]}

    @wraps(f)
    def wrapper(*args):
        return f(*args)

    return wrapper


class PyZL:
    def __init__(self, src):
        self.zl_code = src
        with NamedTemporaryFile(
            suffix=".zls", delete=False
        ) as fzls, NamedTemporaryFile(suffix=".zli", delete=False) as fzli, open(
            splitext(fzli.name)[0] + ".py", "w"
        ) as fpyl:

            # Compile lib
            if _pyzlslib:
                for f, d in _pyzlslib.items():
                    fzli.write(f'val {f}: {d["type"]}\n'.encode())
                    fpyl.write(d["py"])
                fzli.seek(0)
                fpyl.seek(0)
                subprocess.check_call(["../bin/zeluc", fzli.name])
                lib = splitext(basename(fzli.name))[0].capitalize()
                fzls.write(f"open {lib}".encode())
                sys.path.insert(0, dirname(fzli.name))

            # Compile code
            fzls.write(src.encode())
            fzls.seek(0)
            subprocess.check_call(
                [
                    "../bin/zeluc",
                    "-python",
                    "-noreduce",
                    f"-I {dirname(fzli.name)}",
                    fzls.name,
                ]
            )
            with open(splitext(fzls.name)[0] + ".py") as fpy:
                self.py_code = fpy.read()

            # Load python module as class attributes
            modname = splitext(fzls.name)[0]
            spec = importlib.util.spec_from_file_location("zlpyc", modname + ".py")
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            for name, cls in mod.__dict__.items():
                setattr(self, name, cls)

    def __repr__(self):
        return f"(* Zelus code *)\n{self.zl_code}\n{'-'*80}\n\n# Python Code\n\n{self.py_code}"
