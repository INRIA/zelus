from operator import *
from pyzls import Node
import libtop
import buffer

class wavetable(Node):
    def __init__ (self):
        pass
        self.m_16 = 42
        
    def copy(self, dest):
        dest.m_16 = self.m_16
        
    def reset (self, ):
        self.m_16 = 0
        
    def step (self, b_12 , speed_13):
        x_17 = self.m_16
        i_14 = mod(x_17, buffer.size(b_12))
        y_15 = buffer.get(b_12 , i_14)
        self.m_16 = add(i_14, speed_13)
        return y_15
        

