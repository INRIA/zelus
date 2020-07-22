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
    ty = " * ".join([t.__name__ for a, t in f.__annotations__.items() if a != "return"])
    ty += f' -> {f.__annotations__["return"].__name__}'
    return ty


def pyzlslib(f):
    _pyzlslib[f.__name__] = {"type": ml_type(f), "py": getsource(f).split("\n", 1)[1]}

    @wraps(f)
    def wrapper(*args):
        return f(*args)

    return wrapper


class PyZL:
    def __init__(self, src):
        self.zl_code = src
        with NamedTemporaryFile(suffix=".zls", delete=False) as fz, NamedTemporaryFile(
            suffix=".zli", delete=False
        ) as fzi:
            # Compile lib
            for f, d in _pyzlslib.items():
                fzi.write(f'val {f}: {d["type"]}\n'.encode())
            fzi.seek(0)
            subprocess.check_call(["../bin/zeluc", fzi.name])

            with open(splitext(fzi.name)[0] + ".py", "w") as fpi:
                for _, d in _pyzlslib.items():
                    fpi.write(d["py"])

            # Compile code
            lib = splitext(basename(fzi.name))[0].capitalize()
            fz.write(f"open {lib}".encode())
            fz.write(src.encode())
            fz.seek(0)
            subprocess.check_call(
                ["../bin/zeluc", "-python", "-noreduce", f"-I {dirname(fzi.name)}", fz.name]
            )

            # Load python module
            sys.path.insert(0, dirname(fzi.name))
            with open(splitext(fz.name)[0] + ".py") as fp:
                self.py_code = fp.read()
            modname = splitext(fz.name)[0]
            spec = importlib.util.spec_from_file_location("zlpyc", modname + ".py")
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            for name, cls in mod.__dict__.items():
                setattr(self, name, cls)

    def __repr__(self):
        return self.zl_code
