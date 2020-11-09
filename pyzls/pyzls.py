import subprocess
import ast
import sys
import importlib
import IPython
import os
import pathlib
import logging
from abc import ABC, abstractmethod
from inspect import getsource
from contextlib import contextmanager
from functools import wraps
from IPython.core.magic import Magics, magics_class, cell_magic
from IPython.core.magic_arguments import argument, magic_arguments, parse_argstring


logger = logging.getLogger(__name__)


class ZelucError(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)


@contextmanager
def cd(newdir):
    prevdir = os.getcwd()
    os.chdir(os.path.expanduser(newdir))
    try:
        yield
    finally:
        os.chdir(prevdir)


@contextmanager
def safe_edit(file, content):
    pos = file.tell()
    file.write(content)
    file.seek(pos)
    try:
        yield
    except ZelucError as ze:
        file.seek(pos)
        file.truncate(pos)
        logger.error(ze.message)


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
        raise ZelucError(f"Error {exc.returncode}: {exc.stderr}")


def _compile_code(name, src, opt=[], clear=False):
    zlfile = f"_tmp/{name}.zls"
    with open(zlfile, "w" if clear else "a") as fzls:
        with safe_edit(fzls, src):
            _exec(
                [
                    "../bin/zeluc",
                    "-python",
                    "-noreduce",
                    "-copy",
                    "-I _tmp",
                ]
                + opt
                + [zlfile]
            )


def lib(libname, clear=False):
    def inner(f):
        libfile = f"_tmp/{libname}.zli"
        tyfile = f"_tmp/{libname}.py"
        with open(libfile, "w" if clear else "a") as fzli, open(
            tyfile, "w" if clear else "a"
        ) as fpyl:
            ty = f"val {f.__name__}: {_ml_type(f)}\n"
            src = getsource(f).split("\n", 1)[1]
            with safe_edit(fzli, ty):
                _exec(["../bin/zeluc", libfile])
                fpyl.write(src)
                fpyl.seek(0)
                if f"_tmp.{libname}" in sys.modules:
                    importlib.reload(sys.modules[f"_tmp.{libname}"])

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
        with cd("_tmp"), open("top.py", "r") as top:
            exec(top.read(), glob)


# Load ipython magic
try:
    ip = get_ipython()
    ip.register_magics(ZlsMagic)
    ipc = "IPython.CodeCell.options_default.highlight_modes['magic_ocaml'] = {'reg':[/^%%zelus/]};"
    IPython.core.display.display_javascript(ipc, raw=True)
except NameError:
    logger.error("No IPython detected: magic disabled", file=sys.stderr)
    pass

# Create tmp dir to store compiled files
if not os.path.exists("_tmp"):
    os.makedirs("_tmp")
    pathlib.Path("_tmp/__init__.py").touch()
