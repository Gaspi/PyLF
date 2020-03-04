
class Term:
    def __str__(self):
        return("[Abstract Term]")
    def __repr__(self):
        return("%s" % self)
    def __wp_str__(self):
        return "(%s)" % self

class Kind(Term):
    def __str__(self):
        return("Kind")
    def __wp_str__(self):
        return(self.__str__())

class Type(Term):
    def __str__(self):
        return("Type")
    def __wp_str__(self):
        return(self.__str__())

class DB(Term):
    def __init__(self,ident,index):
        self.ident=ident
        self.index=index
    def __str__(self):
        return("%s[%d]" % (self.ident, self.index))
    def __wp_str__(self):
        return(self.__str__())

class Const(Term):
    def __init__(self,name):
        self.name=name
    def __str__(self):
        return("%s" % self.name)
    def __wp_str__(self):
        return(self.__str__())

class App(Term):
    def __init__(self,t,args):
        self.t=t
        self.args=args
    def __str__(self):
        if self.args == []:
            return "%s" % self.t
        else:
            def g(x):
                return(x.__wp_str__())
            return("%s %s" % (self.t.__wp_str__(), " ".join(map(g,self.args))))

class Lam(Term):
    def __init__(self,ident,annot,term):
        self.ident=ident
        self.annot=annot
        self.term =term
    def __str__(self):
        if self.annot == None:
            return("%s => %s" % (self.ident,self.term))
        else:
            return("(%s : %s) => %s" % (self.ident, self.annot,self.term))

class Pi(Term):
    def __init__(self,ident,dom,codom):
        self.ident=ident
        self.dom  =dom
        self.codom=codom
    def __str__(self):
        return("(%s : %s) -> %s" % (self.ident,self.dom,self.codom))


myterm = Lam("u",Pi("z",Const("Nat"),Type()),App(Const("f"), [DB("x",2), Lam("z",None,DB("y",1))]))


print(myterm)
