# -*- coding: utf-8 -*-
"""
@author: Gaspard FEREY
"""

import term
import signature as sig
import ply.lex as lex
import ply.yacc as yacc

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
        'LEFTPAR','RIGHTPAR','LONGARROW','ARROW','FATARROW','DEF','STRING',
        'NAME','REQUIRE','EVAL','INFER','CHECK','CHECKNOT',
        'ASSERT','ASSERTNOT','PRINT','GDT','IDENT','QIDENT'
        ] + list(reserved.values())

def t_COMMENT(t):
    r'\(\*(.|\n)*?\*\)'
    pass

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
def t_STRING(t):
    r'".*"'
    t.value=t.value[1:-1]
    return t

# Ignored characters
t_ignore = " \t\r"

last_line = [ 0 ]

def t_newline(t : lex.LexToken) -> lex.LexToken:
    r'\n+'
    t.lexer.lineno += t.value.count("\n")
    last_line[0] = t.lexpos

def t_error(t):
    print(f"Illegal character at line {t.lexer.lineno}:  {t.value[0]!r}")
    t.lexer.skip(1)

# Build the lexer
lex.lex()




# dictionary of names (for storing variables)
dbs = []
pat = { 'vars' : [], 'id' : 0 }
def clearpat():
    pat['vars'].clear()
    pat['id'] = 0
def freshpatvar():
    pat['id'] = pat.id+1
    return('_' + str(pat.id-1))


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
    '''entries : entry cleardbs entries
               | empty'''
    p[0] = [] if p[1] is None else p[1] + p[3]

# Clear local DB indices between entries
def p_cleardbs(p):
    'cleardbs : '
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
    p[0] = sig.Scope.PRIVATE

def p_private_pub(p):
    'priv : '
    p[0] = sig.Scope.PUBLIC

def p_entry_smb_decl(p):
    'entry : priv IDENT params COLON expr DOT'
    p[0] = [ sig.Symbol(p[2], term.mk_pies(p[3],p[5]),
                        p[1], sig.Staticity.STATIC) ]

def p_entry_smb_def(p):
    'entry : priv KW_DEF IDENT params COLON expr DOT'
    p[0] = [ sig.Symbol(p[3], term.mk_pies(p[4],p[6]),
                        p[1], sig.Staticity.DEFINABLE) ]

def p_entry_smb_inj(p):
    'entry : priv KW_INJ IDENT params COLON expr DOT'
    p[0] = [ sig.Symbol(p[3], term.mk_pies(p[4],p[6]),
                        p[1], sig.Staticity.INJECTIVE) ]

def p_entry_smb_ac(p):
    'entry : priv KW_DEFAC IDENT LEFTSQU expr RIGHTSQU DOT'
    p[0] = [sig.Symbol(p[3],
                       term.mk_pies([(None,p[5]),(None,p[5])],
                                    p[5]),
                       p[1], sig.Staticity.DEFINABLEAC) ]

def p_entry_typed_def(p):
    'entry : priv KW_DEF IDENT params COLON expr DEF expr DOT'
    p[0] = [ sig.Symbol(p[3], term.mk_pies(p[4],p[6]),
                        p[1], sig.Staticity.DEFINABLE),
             sig.Rule(None,[], term.Const(p[3]),
                      term.mk_lams(p[4],p[8]))  ]

def p_entry_untyped_def(p):
    'entry : priv KW_DEF IDENT params DEF expr DOT'
    p[0] = [ sig.Symbol(p[3], None,
                        p[1], sig.Staticity.DEFINABLE),
             sig.Rule(None,[], term.Const(p[3]),
                      term.mk_lams(p[4],p[6]))  ]

def p_entry_thm(p):
    'entry : KW_THM IDENT params COLON expr DEF expr DOT'
    p[0] = [ sig.Symbol(p[2], term.mk_pies(p[3],p[5]),
              sig.Scope.PUBLIC, sig.Staticity.DEFINABLE),
             sig.Rule(None,[], term.Const(p[2]),
                      term.mk_lams(p[3],p[7]))  ]

def p_entry_rules(p):
    'entry : rules DOT'
    p[0] = p[1]
def p_rules(p):
    '''rules : rule rules
             | empty'''
    p[0] = [] if p[1] is None else [ p[1] ] + p[2]
def p_rule(p):
    'rule : rulename LEFTSQU patvars RIGHTSQU pat LONGARROW expr'
    p[0] = sig.Rule(p[1],p[3],p[5],p[7])

def p_rulename(p):
    '''rulename : LEFTBRA IDENT RIGHTBRA
                | '''
    p[0] = p[2] if len(p) > 1 else None
    clearpat()

def p_entry_cmd_eval(p):
    'entry : EVAL expr DOT'
    p[0] = [ sig.Command("EVAL", p[2]) ]
def p_entry_cmd_infer(p):
    'entry : INFER expr DOT'
    p[0] = [ sig.Command("INFER", p[2]) ]
def p_entry_cmd_gdt(p):
    'entry : GDT IDENT DOT'
    p[0] = [ sig.Command("GDT", p[2]) ]
def p_entry_cmd_require(p):
    'entry : REQUIRE IDENT DOT'
    p[0] = [ sig.Command("REQUIRE", p[2]) ]
def p_entry_cmd_print(p):
    'entry : PRINT STRING DOT'
    p[0] = [ sig.Command("PRINT", p[2]) ]

def p_kwcheck(p):
    '''kwcheck : CHECK
               | CHECKNOT
               | ASSERT
               | ASSERTNOT'''
    p[0] = p[1]
def p_kwrel(p):
    '''kwrel : COLON
             | EQUAL'''
    p[0] = "TYPE" if p[1] == ":" else "CONV"
def p_entry_cmd_check(p):
    'entry : kwcheck expr kwrel expr DOT'
    p[0] = [ sig.Command(p[1]+p[3], [p[2], p[4]]) ]



def p_qualid_id(p):
    'qualid : IDENT'
    if p[1] in dbs:
        p[0] = term.DB(p[1],len(dbs) - dbs.index(p[1])-1)
    elif p[1] in pat['vars']:
        p[0] = term.MVar(p[1])
    else:
        p[0] = term.Const(p[1])
def p_qualid_qual(p):
    'qualid : QIDENT'
    p[0] = term.Const(p[1])

def p_idents_more(p):
    'patvars : patvar COMMA patvars'
    p[0] = [ p[1] ] + p[3]
def p_idents_one(p):
    'patvars : patvar'
    p[0] = [ p[1] ]
def p_idents_none(p):
    'patvars : '
    p[0] = []
def p_patvar(p):
    'patvar : IDENT'
    p[0] = p[1]
    if p[1] in pat['vars']:
        raise Exception(f'Duplicated rule variable %r at line %d' %
                        (p[1], p.lexer.lineno))
    pat['vars'].append(p[1])

def p_expr_type(p):
    'expr : TYPE'
    p[0] = term.Type()

def p_expr_Rexpr(p):
    'expr : rexpr'
    p[0] = p[1]
def p_expr_Lexpr(p):
    'expr : lexprs rexpr'
    p[0] = term.App(p[1],[ p[2] ])
def p_expr_pi(p):
    'expr : bindannot ARROW expr'
    p[0] = term.Pi(p[1][0],p[1][1],p[3])
    dbs.pop()
def p_expr_arr(p):
    'expr : bindannon ARROW expr'
    p[0] = term.Pi(p[1][0],p[1][1],p[3])
    dbs.pop()

def p_lexprs_app(p):
    'lexprs : lexprs lexpr'
    p[0] = term.App(p[1],[ p[2] ])
def p_lexprs_t(p):
    'lexprs : lexpr'
    p[0] = p[1]

def p_expr_var(p):
    'lexpr : qualid'
    p[0] = p[1]
def p_expr_group(p):
    'lexpr : LEFTPAR expr RIGHTPAR'
    p[0] = p[2]

def p_rexpr_lexpr(p):
    'rexpr : lexpr'
    p[0] = p[1]
def p_rexpr_lam(p):
    'rexpr : bindannot FATARROW expr'
    p[0] = term.Lam(p[1][0],p[1][1],p[3])
    dbs.pop()


################### Patterns
def p_pat_Rpat(p):
    'pat : rpat'
    p[0] = p[1]
def p_pat_Lpat(p):
    'pat : lpats rpat'
    p[0] = term.App(p[1],[ p[2] ])

def p_lpats_app(p):
    'lpats : lpats lpat'
    p[0] = term.App(p[1],[ p[2] ])
def p_lpats_t(p):
    'lpats : lpat'
    p[0] = p[1]

def p_lpat_var(p):
    'lpat : qualid'
    p[0] = p[1]
def p_lpat_underscore(p):
    'lpat : UNDERSCORE'
    p[0] = term.MVar(freshpatvar())
def p_lpat_group(p):
    'lpat : LEFTPAR pat RIGHTPAR'
    p[0] = p[2]
def p_lpat_bracket(p):
    'lpat : LEFTBRA pat RIGHTBRA'
    p[0] = p[2]

def p_rpat_lpat(p):
    'rpat : lpat'
    p[0] = p[1]
def p_rpat_lam(p):
    'rpat : bindannon FATARROW pat'
    p[0] = term.Lam(p[1][0],p[1][1],p[3])
    dbs.pop()
################### Patterns



def p_bindannot(p):
    "bindannot : LEFTPAR IDENT COLON expr RIGHTPAR"
    # Create a new scope for local variables
    dbs.append(p[2])
    p[0] = (p[2], p[4])

def p_bindannotn(p):
    "bindannot : LEFTPAR UNDERSCORE COLON expr RIGHTPAR"
    # Create a new scope for local variables
    dbs.append("_")
    p[0] = (None, p[4])

def p_bindannon(p):
    "bindannon :  IDENT"
    # Create a new scope for local variables
    dbs.append("_")
    p[0] = (None, p[1])

def t_module_decl(p):
    'module_decl : NAME IDENT DOT'
    pass

def t_module_req(p):
    'module_req : REQUIRE IDENT DOT'
    pass

def p_error(p):
    if not p:
        print(f"Unexpected EOF")
    else:
        pos = p.lexer.lexpos
        line_start = p.lexer.lexdata.rfind('\n', 0, pos)
        col = pos - line_start
        print("Syntax error at line %d, column %d: %r" %
              (p.lexer.lineno,col,p))

sigparser = yacc.yacc(start='signature')

# termparser = yacc.yacc(start='expr')
