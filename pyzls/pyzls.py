import subprocess
import ast
import sys
import importlib
import IPython
from abc import ABC, abstractmethod
from inspect import getsource
from functools import wraps
from IPython.core.magic import Magics, magics_class, cell_magic
from IPython.core.magic_arguments import argument, magic_arguments, parse_argstring


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
    ty += f' -AD-> {r.__name__ if hasattr(r, "__name__") else str(r)}'
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


def _compile_code(name, src, opt=[], clear=False):
    with open(name + ".zls", "w" if clear else "a") as fzls:
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


def lib(libname, clear=False):
    def inner(f):
        with open(libname + ".zli", "w" if clear else "a") as fzli, open(
            libname + ".py", "w" if clear else "a"
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


@magics_class
class ZlsMagic(Magics):
    @magic_arguments()
    @argument("-clear", action="store_true", help="Clear zelus buffer")
    @argument(
        "-zopt", type=str, action="append", default=[], help="Optinal flags for zeluc"
    )
    @cell_magic
    def zelus(self, line=None, cell=None):
        args = parse_argstring(self.zelus, line)
        glob = self.shell.user_ns
        zopt = [zo[1:-1] for zo in args.zopt]
        _compile_code("top", cell, opt=zopt, clear=args.clear)
        with open("top.py", "r") as top:
            exec(top.read(), glob)


# Load ipython magic
try:
    ip = get_ipython()
    ip.register_magics(ZlsMagic)
    ipc = "IPython.CodeCell.options_default.highlight_modes['magic_ocaml'] = {'reg':[/^%%zelus/]};"
    IPython.core.display.display_javascript(ipc, raw=True)
except NameError:
    print("No IPython detected: magic disabled", file=sys.stderr)
    pass
