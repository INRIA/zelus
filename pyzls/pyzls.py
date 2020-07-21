from abc import ABC, abstractmethod
import subprocess
import ast
from tempfile import NamedTemporaryFile
from os.path import splitext
import importlib.util

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
    
class PyZL:
    def __init__(self, src):
        self.zl_code = src
        with NamedTemporaryFile(suffix='.zls') as fz:
            fz.write(src.encode())
            fz.seek(0)
            subprocess.check_call(['../bin/zeluc', '-python', fz.name])
            with open(splitext(fz.name)[0] + '.py') as fp:
                self.py_code = fp.read()
            modname = splitext(fz.name)[0]
            spec = importlib.util.spec_from_file_location('zlpyc', modname + '.py')
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            for name, cls in mod.__dict__.items():
                if isinstance(cls, type):
                    setattr(self, name, cls)
                
    def __repr__(self):
        return self.zl_code
    