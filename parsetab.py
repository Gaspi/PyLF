
# parsetab.py
# This file is automatically generated. Do not edit.
# pylint: disable=W,C,R
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = 'signatureARROW ASSERT ASSERTNOT CHECK CHECKNOT COLON DEF DOT EQUAL EVAL FATARROW GDT IDENT INFER KW_DEF KW_DEFAC KW_INJ KW_PRV KW_THM LEFTBRA LEFTPAR LEFTSQU LONGARROW NAME PRINT REQUIRE RIGHTBRA RIGHTPAR RIGHTSQU TYPE UNDERSCOREsignature : modulesempty : modules : module modules\n               | emptymodule : NAME IDENT DOT entriesentries : entry entries\n               | emptyentry : symbol_decl\n             | rule_decl\n             | commandparams : param params\n              | emptyparam : LEFTPAR IDENT COLON expression RIGHTPARpriv : KW_PRVpriv : symbol_decl : priv IDENT params COLON expression DOTsymbol_decl : priv KW_DEF IDENT params COLON expression DOTsymbol_decl : priv KW_DEFAC IDENT LEFTSQU expression RIGHTSQU DOTqualid : IDENTqualid : IDENT DOT IDENTidents : IDENT idents\n              | emptyrule_decl : LEFTSQU idents RIGHTSQU expression LONGARROW expression DOTcommand : EVAL IDENT DOTexpression : TYPEexpression : bindannot ARROW expressionexpression : LEFTPAR expression expression RIGHTPARexpression : bindanon ARROW expressionbindannot : LEFTPAR IDENT COLON expression RIGHTPARbindanon :  IDENTexpression : qualidexpression : LEFTPAR expression RIGHTPAR'
    
_lr_action_items = {'NAME':([0,3,8,9,10,11,12,13,14,19,35,58,70,71,72,],[5,5,-2,-5,-2,-7,-8,-9,-10,-6,-24,-16,-17,-18,-23,]),'$end':([0,1,2,3,4,6,8,9,10,11,12,13,14,19,35,58,70,71,72,],[-2,0,-1,-2,-4,-3,-2,-5,-2,-7,-8,-9,-10,-6,-24,-16,-17,-18,-23,]),'IDENT':([5,8,10,12,13,14,15,16,17,18,21,22,24,30,33,35,36,40,42,44,46,47,49,50,52,53,54,55,56,57,58,63,65,66,67,68,70,71,72,73,],[7,-15,-15,-8,-9,-10,20,24,26,-14,31,32,24,38,47,-24,47,47,-25,55,-31,-19,47,47,47,47,47,-19,47,68,-16,-26,-32,47,-28,-20,-17,-18,-23,-27,]),'DOT':([7,26,42,46,47,48,55,60,61,62,63,65,67,68,73,],[8,35,-25,-31,57,58,57,70,71,72,-26,-32,-28,-20,-27,]),'LEFTSQU':([8,10,12,13,14,32,35,58,70,71,72,],[16,16,-8,-9,-10,40,-24,-16,-17,-18,-23,]),'EVAL':([8,10,12,13,14,35,58,70,71,72,],[17,17,-8,-9,-10,-24,-16,-17,-18,-23,]),'KW_PRV':([8,10,12,13,14,35,58,70,71,72,],[18,18,-8,-9,-10,-24,-16,-17,-18,-23,]),'KW_DEF':([8,10,12,13,14,15,18,35,58,70,71,72,],[-15,-15,-8,-9,-10,21,-14,-24,-16,-17,-18,-23,]),'KW_DEFAC':([8,10,12,13,14,15,18,35,58,70,71,72,],[-15,-15,-8,-9,-10,22,-14,-24,-16,-17,-18,-23,]),'RIGHTSQU':([16,23,24,25,34,42,46,47,51,63,65,67,68,73,],[-2,33,-2,-22,-21,-25,-31,-19,61,-26,-32,-28,-20,-27,]),'LEFTPAR':([20,28,31,33,36,40,42,44,46,47,49,50,52,53,54,55,56,63,65,66,67,68,69,73,],[30,30,30,44,44,44,-25,44,-31,-19,44,44,44,44,44,-19,44,-26,-32,44,-28,-20,-13,-27,]),'COLON':([20,27,28,29,31,37,38,39,55,69,],[-2,36,-2,-12,-2,-11,49,50,66,-13,]),'TYPE':([33,36,40,42,44,46,47,49,50,52,53,54,55,56,63,65,66,67,68,73,],[42,42,42,-25,42,-31,-19,42,42,42,42,42,-19,42,-26,-32,42,-28,-20,-27,]),'LONGARROW':([41,42,46,47,63,65,67,68,73,],[52,-25,-31,-19,-26,-32,-28,-20,-27,]),'RIGHTPAR':([42,46,47,54,55,59,63,64,65,67,68,73,74,],[-25,-31,-19,65,-19,69,-26,73,-32,-28,-20,-27,75,]),'ARROW':([43,45,47,55,75,],[53,56,-30,-30,-29,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'signature':([0,],[1,]),'modules':([0,3,],[2,6,]),'module':([0,3,],[3,3,]),'empty':([0,3,8,10,16,20,24,28,31,],[4,4,11,11,25,29,25,29,29,]),'entries':([8,10,],[9,19,]),'entry':([8,10,],[10,10,]),'symbol_decl':([8,10,],[12,12,]),'rule_decl':([8,10,],[13,13,]),'command':([8,10,],[14,14,]),'priv':([8,10,],[15,15,]),'idents':([16,24,],[23,34,]),'params':([20,28,31,],[27,37,39,]),'param':([20,28,31,],[28,28,28,]),'expression':([33,36,40,44,49,50,52,53,54,56,66,],[41,48,51,54,59,60,62,63,64,67,74,]),'bindannot':([33,36,40,44,49,50,52,53,54,56,66,],[43,43,43,43,43,43,43,43,43,43,43,]),'bindanon':([33,36,40,44,49,50,52,53,54,56,66,],[45,45,45,45,45,45,45,45,45,45,45,]),'qualid':([33,36,40,44,49,50,52,53,54,56,66,],[46,46,46,46,46,46,46,46,46,46,46,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> signature","S'",1,None,None,None),
  ('signature -> modules','signature',1,'p_signature','parser.py',89),
  ('empty -> <empty>','empty',0,'p_empty','parser.py',93),
  ('modules -> module modules','modules',2,'p_modules','parser.py',97),
  ('modules -> empty','modules',1,'p_modules','parser.py',98),
  ('module -> NAME IDENT DOT entries','module',4,'p_module','parser.py',102),
  ('entries -> entry entries','entries',2,'p_entries','parser.py',106),
  ('entries -> empty','entries',1,'p_entries','parser.py',107),
  ('entry -> symbol_decl','entry',1,'p_entry','parser.py',111),
  ('entry -> rule_decl','entry',1,'p_entry','parser.py',112),
  ('entry -> command','entry',1,'p_entry','parser.py',113),
  ('params -> param params','params',2,'p_params','parser.py',117),
  ('params -> empty','params',1,'p_params','parser.py',118),
  ('param -> LEFTPAR IDENT COLON expression RIGHTPAR','param',5,'p_param','parser.py',122),
  ('priv -> KW_PRV','priv',1,'p_private_priv','parser.py',126),
  ('priv -> <empty>','priv',0,'p_private_pub','parser.py',130),
  ('symbol_decl -> priv IDENT params COLON expression DOT','symbol_decl',6,'p_symbol_static','parser.py',134),
  ('symbol_decl -> priv KW_DEF IDENT params COLON expression DOT','symbol_decl',7,'p_symbol_def','parser.py',138),
  ('symbol_decl -> priv KW_DEFAC IDENT LEFTSQU expression RIGHTSQU DOT','symbol_decl',7,'p_symbol_ac','parser.py',142),
  ('qualid -> IDENT','qualid',1,'p_qualid_id','parser.py',146),
  ('qualid -> IDENT DOT IDENT','qualid',3,'p_qualid_qual','parser.py',150),
  ('idents -> IDENT idents','idents',2,'p_idents','parser.py',154),
  ('idents -> empty','idents',1,'p_idents','parser.py',155),
  ('rule_decl -> LEFTSQU idents RIGHTSQU expression LONGARROW expression DOT','rule_decl',7,'p_rule_decl','parser.py',159),
  ('command -> EVAL IDENT DOT','command',3,'p_command','parser.py',163),
  ('expression -> TYPE','expression',1,'p_expr_type','parser.py',167),
  ('expression -> bindannot ARROW expression','expression',3,'p_expr_pi','parser.py',171),
  ('expression -> LEFTPAR expression expression RIGHTPAR','expression',4,'p_expr_app','parser.py',176),
  ('expression -> bindanon ARROW expression','expression',3,'p_expr_arr','parser.py',180),
  ('bindannot -> LEFTPAR IDENT COLON expression RIGHTPAR','bindannot',5,'p_bindannot','parser.py',185),
  ('bindanon -> IDENT','bindanon',1,'p_bindanon','parser.py',191),
  ('expression -> qualid','expression',1,'p_expr_var','parser.py',197),
  ('expression -> LEFTPAR expression RIGHTPAR','expression',3,'p_expression_group','parser.py',201),
]