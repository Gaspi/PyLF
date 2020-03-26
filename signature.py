# -*- coding: utf-8 -*-
"""
@author: Gaspard FEREY
"""

from enum import Enum

class Scope(Enum):
    PRIVATE = 0
    PUBLIC = 1

class Staticity(Enum):
    STATIC = 0
    DEFINABLE = 1
    DEFINABLEAC = 2
    INJECTIVE = 3

class _Entry():
    def __init__(self,entry):
        self.entry = entry

class Symbol(_Entry):
    def __init__(self,ident,typea,scope,stat):
        super(Symbol,self).__init__("symbol")
        self.ident = ident
        self.typea = typea
        self.scope = scope
        self.stat = stat
    def __str__(self):
        return("%s%r : %r" %
               ("" if self.stat == Staticity.STATIC else "def ",
                self.ident, self.typea))
    def __repr__(self):
        return self.__str__()

class Command(_Entry):
    def __init__(self,command,args):
        super(Command,self).__init__("command")
        self.command = command
        self.args = args
    def __str__(self):
        return("#%s %r" % (self.command, self.args))
    def __repr__(self):
        return self.__str__()

class Rule(_Entry):
    def __init__(self,name,ctx,lhs,rhs):
        super(Rule,self).__init__("rule")
        self.name= name
        self.ctx = ctx
        self.lhs = lhs
        self.rhs = rhs
    def __str__(self):
        return("%s%r %r --> %r" %
               ("" if not self.name
                else "{%s} " % self.name,
                self.ctx, self.lhs, self.rhs))
    def __repr__(self):
        return self.__str__()

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
