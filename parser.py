# -*- coding: utf-8 -*-
"""
Created on Tue Mar 24 17:17:09 2020

@author: gaspa
"""

import term
import signature

reserved = {
    'Type'      : 'TYPE',
    '_'         : 'UNDERSCORE',
    'def'       : 'KW_DEF',
    'defac'     : 'KW_DEFAC',
    'injective' : 'KW_INJ',
    'thm'       : 'KW_THM',
    'private'   : 'KW_PRV',
 }

tokens = [
        'DOT','COMMA','COLON','EQUAL','LEFTSQU','RIGHTSQU','LEFTBRA','RIGHTBRA',
        'LEFTPAR','RIGHTPAR','LONGARROW','ARROW','FATARROW','DEF',
        'NAME','REQUIRE','EVAL','INFER','CHECK','CHECKNOT',
        'ASSERT','ASSERTNOT','PRINT','GDT','IDENT','QIDENT'
        ] + list(reserved.values())

# Tokens
t_DOT        = r'\.'
t_COMMA      = r','
t_COLON      = r':'
t_EQUAL      = r'=='
t_LEFTSQU    = r'\['
t_RIGHTSQU   = r'\]'
t_LEFTBRA    = r'{'
t_RIGHTBRA   = r'}'
t_LEFTPAR    = r'\('
t_RIGHTPAR   = r'\)'
t_LONGARROW  = r'-->'
t_ARROW      = r'->'
t_FATARROW   = r'=>'
t_DEF        = r':='
t_NAME       = r'\#NAME'
t_REQUIRE    = r'\#REQUIRE'
t_EVAL       = r'\#EVAL'
t_INFER      = r'\#INFER'
t_CHECK      = r'\#CHECK'
t_CHECKNOT   = r'\#CHECKNOT'
t_ASSERT     = r'\#ASSERT'
t_ASSERTNOT  = r'\#ASSERTNOT'
t_PRINT      = r'\#PRINT'
t_GDT        = r'\#GDT'
t_QIDENT     = r'(([a-zA-Z0-9_][a-zA-Z0-9_!?\']*)|(\{\|.*\|\}))\.(([a-zA-Z0-9_][a-zA-Z0-9_!?\']*)|(\{\|.*\|\}))'
def t_IDENT(t):
    r'([a-zA-Z0-9_][a-zA-Z0-9_!?\']*)|(\{\|.*\|\})'
    t.type = reserved.get(t.value,'IDENT')
    return t

# Ignored characters
t_ignore = " \t\r"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")

def t_COMMENT(t):
    r'\(\*(.|\n)*?\*\)'
    pass

def t_error(t):
    print(f"Illegal character at line {t.lexer.lineno}:  {t.value[0]!r}")
    t.lexer.skip(1)

# Build the lexer
import ply.lex as lex
lex.lex()


# dictionary of names (for storing variables)
dbs = []


def mkident(p):
    print(f"Ident: {p} in {dbs}")
    if p in dbs:
        return term.DB(p,len(dbs) - dbs.index(p)-1)
    else:
        return term.Const(p)

def p_signature(p):
    'signature : modules'
    p[0] = p[1]

def p_empty(p):
    'empty : '
    pass

def p_modules(p):
    '''modules : module modules
               | empty'''
    p[0] = [] if p[1] is None else [ p[1] ] + p[2]

def p_module(p):
    'module : NAME IDENT DOT entries'
    p[0] = (p[2],p[4])

def p_entries(p):
    '''entries : entry clear entries
               | empty'''
    p[0] = [] if p[1] is None else p[1] + p[3]

# Clear local DB indices between entries
def p_clear(p):
    'clear : '
    dbs.clear()

def p_params(p):
    '''params : param params
              | empty'''
    p[0] = [] if p[1] is None else [ p[1] ] + p[2]

def p_param(p):
    'param : LEFTPAR IDENT COLON expr RIGHTPAR'
    p[0] = (p[2], p[4])
    dbs.append(p[2])

def p_private_priv(p):
    'priv : KW_PRV'
    p[0] = signature.Scope.PRIVATE

def p_private_pub(p):
    'priv : '
    p[0] = signature.Scope.PUBLIC

def p_entry_smb_decl(p):
    'entry : priv IDENT params COLON expr DOT'
    p[0] = [ (p[2], term.mk_pies(p[3],p[5]), p[1], signature.Staticity.STATIC) ]

def p_entry_smb_def(p):
    'entry : priv KW_DEF IDENT params COLON expr DOT'
    p[0] = [ (p[3], term.mk_pies(p[4],p[6]), p[1], signature.Staticity.DEFINABLE) ]

def p_entry_smb_ac(p):
    'entry : priv KW_DEFAC IDENT LEFTSQU expr RIGHTSQU DOT'
    p[0] = [ (p[3], term.mk_pies([("_",p[5]),("_",p[5])], p[5]), p[1],
              signature.Staticity.DEFINABLEAC) ]

def p_entry_typed_def(p):
    'entry : priv KW_DEF IDENT params COLON expr DEF expr DOT'
    p[0] = [ (p[3], term.mk_pies(p[4],p[6]), p[1], signature.Staticity.DEFINABLE),
             ([], term.Const(p[3]), term.mk_lams(p[4],p[8]))  ]

def p_entry_untyped_def(p):
    'entry : priv KW_DEF IDENT params DEF expr DOT'
    p[0] = [ (p[3], None, p[1], signature.Staticity.DEFINABLE),
             ([], term.Const(p[3]), term.mk_lams(p[4],p[6]))  ]

def p_entry_thm(p):
    'entry : KW_THM IDENT params COLON expr DEF expr DOT'
    p[0] = [ (p[2], term.mk_pies(p[3],p[5]),
              signature.Scope.PUBLIC, signature.Staticity.DEFINABLE),
             ([], term.Const(p[2]), term.mk_lams(p[3],p[7]))  ]

def p_entry_rules(p):
    'entry : rules DOT'
    p[0] = p[1]

def p_rules(p):
    '''rules : rule rules
             | empty'''
    p[0] = [] if p[1] is None else [ p[1] ] + p[3]

def p_rule(p):
    'rule : LEFTSQU idents RIGHTSQU expr LONGARROW expr'
    p[0] = (p[2], p[4])

def p_entry_cmd_eval(p):
    'entry : EVAL IDENT DOT'
    p[0] = p[1]


def p_qualid_id(p):
    'qualid : IDENT'
    p[0] = term.DB(p[1],len(dbs) - dbs.index(p[1])-1) if p[1] in dbs else term.Const( p[1] )

def p_qualid_qual(p):
    'qualid : QIDENT'
    p[0] = term.Const(p[1])

def p_idents_more(p):
    'idents : IDENT COMMA idents'
    p[0] = [ p[1] ] + p[3]

def p_idents_one(p):
    'idents : IDENT'
    p[0] = [ p[1] ]

def p_idents_none(p):
    'idents : '
    p[0] = []

def p_expr_type(p):
    'expr : TYPE'
    p[0] = term.Type()

def p_expr_lam(p):
    'expr : bindannot FATARROW expr'
    p[0] = term.Lam(p[1][0],p[1][1],p[3])
    dbs.pop()

def p_expr_pi(p):
    'expr : bindannot ARROW expr'
    p[0] = term.Pi(p[1][0],p[1][1],p[3])
    dbs.pop()

def p_expr_app(p):
    'expr : LEFTPAR expr expr RIGHTPAR'
    p[0] = term.App(p[2],[ p[3] ])

def p_expr_arr(p):
    'expr : bindanon ARROW expr'
    p[0] = term.Pi(p[1][0],p[1][1],p[3])
    dbs.pop()

def p_bindannot(p):
    "bindannot : LEFTPAR IDENT COLON expr RIGHTPAR"
    # Create a new scope for local variables
    dbs.append(p[2])
    p[0] = (p[2], p[4])

def p_bindanon(p):
    "bindanon :  IDENT"
    # Create a new scope for local variables
    dbs.append("_")
    p[0] = (None, p[1])

def p_expr_var(p):
    'expr : qualid'
    p[0] = p[1]

def p_expr_group(p):
    'expr : LEFTPAR expr RIGHTPAR'
    p[0] = p[2]

def t_module_decl(p):
    'module_decl : NAME IDENT DOT'
    pass

def t_module_req(p):
    'module_req : REQUIRE IDENT DOT'
    pass

def p_error(p):
    if p is None:
        print(f"Unexpected EOF")
    else:
        print(f"Syntax error at line {p.lexer.lineno}: {p}")

import ply.yacc as yacc
sigparser = yacc.yacc(start='signature')

dkcode = '''
#NAME test .
A : Type.
private B : Type.
def x : A.
private defac sz [ A ].
def f : (x : A) -> A.
[A] f A B --> A.
def a (x:Type) : x := (y : A) => x.
private append (u:Type) : (x : (t)) -> (x).
'''

a = sigparser.parse(dkcode)

for (mod,sig) in a:
    print(f"Module: {mod}")
    for i in sig:
        print(i)


#termparser = yacc.yacc(start='expr')
#b = termparser.parse("(x : (t)) -> (x)")
