from abc import ABC, abstractmethod
from jax.tree_util import tree_flatten, tree_unflatten, register_pytree_node_class, register_pytree_node
from dataclasses import dataclass, asdict


@register_pytree_node_class
class Node(ABC):
    def __init__(self, state=None):
        self.state = self.init() if state == None else state

    ## JAX methods to be able to vectorize Nodes
    def tree_flatten(self):
        return tree_flatten(self.state)
    @classmethod
    def tree_unflatten(cls, aux_data, children):
        return cls(state=tree_unflatten(aux_data, children))

    ## Abstract methods
    @abstractmethod
    def init(self):
        raise NotImplementedError ("Abstract method init not implemented.")
    @abstractmethod
    def step(self, *args):
        raise NotImplementedError ("Abstract method step not implemented.")

def step(instance, args):
    s, o = instance.step(instance.state, args)
    return type(instance)(state=s), o

def init(node):
    return node()

def reset(instance):
    return type(instance)(), ()


def register_pytree_node_dataclass(cls):
  _flatten = lambda obj: tree_flatten(asdict(obj))
  _unflatten = lambda d, children: cls(**d.unflatten(children))
  register_pytree_node(cls, _flatten, _unflatten)
  return cls

@register_pytree_node_dataclass
@dataclass
class J_dataclass():
    _kind : int
    
    def __eq__(self, x):
        assert isinstance(x, type(self)), "Bad type"
        return x._kind == self._kind
