# -*- coding: utf-8 -*-

from enum import Enum

class Scope(Enum):
    PRIVATE = 0
    PUBLIC = 1

class Staticity(Enum):
    STATIC = 0
    DEFINABLE = 1
    DEFINABLEAC = 2
    INJECTIVE = 3

class Signature:
    def __init__(self,mident):
        self.mident = mident
        self.sig = {}
        self.ext_rules = []
        self.deps = []

    def add_rule(self,mident,ident,rule):
        pass

    def add_symbol(self,ident,scope,staticity,idtype):
        if ident in self.sig:
            raise KeyError(f"Symbol already in signature: {ident}")
        else:
            self.sig[ident] = {
                  'scope'     :  scope,
                  'staticity' : staticity,
                  'type'      : idtype,
                  'rules'     : []
                }

    def is_ac(self,ident):
        return (self.sig[ident] == Staticity.DEFINABLEAC)

