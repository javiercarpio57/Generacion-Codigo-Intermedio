from prettytable.prettytable import NONE
from antlr4 import *
from antlr4.tree.Trees import TerminalNode
from antlr4.error.ErrorListener import ErrorListener
from DecafLexer import DecafLexer
from DecafListener import DecafListener
from DecafParser import DecafParser
from itertools import groupby
from utilities import *

class GeneracionCodigoPrinter(DecafListener):
    def __init__(self):
        self.root = None
        self.temp = 0
        self.ifcont = 0
        self.whilecont = 0
        self.inst = 0
        
        self.STRING = 'char'
        self.INT = 'int'
        self.BOOLEAN = 'boolean'
        self.VOID = 'void'
        self.ERROR = 'error'

        self.data_type = {
            'char': self.STRING,
            'int': self.INT,
            'boolean': self.BOOLEAN,
            'void': self.VOID,
            'error': self.ERROR
        }

        self.sizes = {
            self.INT: 4,
            self.BOOLEAN: 2,
            self.STRING: 1
        }

        self.ambitos = []
        self.current_scope = None
        self.tabla_tipos = TablaTipos()
        self.errores = SemanticError()
        self.tabla_methods = TablaMetodos()
        self.tabla_struct = TablaStruct()
        self.tabla_parameters = TablaParametros()
        
        self.node_type = {}
        self.node_code = {}

        super().__init__()

    def newTemp(self):
        temp = f't{self.temp}'
        self.temp += 1
        return temp

    def NewLabel(self, flow = ''):
        if flow == 'if':
            control = f'END_IF_{self.ifcont}'
            trueIf = f'IF_TRUE_{self.ifcont}'
            falseIf = f'IF_FALSE_{self.ifcont}'
            self.ifcont += 1
            return control, trueIf, falseIf
        elif flow == 'while':
            begin = f'BEGIN_WHILE_{self.whilecont}'
            control = f'END_WHILE_{self.whilecont}'
            trueWhile = f'WHILE_TRUE_{self.whilecont}'
            falseWhile = f'WHILE_FALSE_{self.whilecont}'
            self.whilecont += 1
            return begin, control, trueWhile, falseWhile
        else: 
            control = f'INST_{self.inst}'
            return control

    def TopGet(self, id):
        variable = self.current_scope.LookUp(id)
        if variable != 0:
            offset = variable['Offset']
                
            addr = f'L[{offset}]'
            return addr

        elif self.Find(id) != 0:
            variable = self.Find(id)
            offset = variable['Offset']
            addr = f'G[{offset}]'
            return addr


    def PopScope(self):
        self.current_scope.ToTable()
        self.current_scope = self.ambitos.pop()        

    def NewScope(self):
        self.ambitos.append(self.current_scope)
        self.current_scope = TablaSimbolos()

    def Find(self, var):
        lookup = self.current_scope.LookUp(var)
        if lookup == 0:
            ambitos_reverse = self.ambitos.copy()
            ambitos_reverse.reverse()
            for scope in ambitos_reverse:
                lookup2 = scope.LookUp(var)
                if lookup2 != 0:
                    return lookup2
            return 0
        else:
            return lookup

    def Intersection(self, a, b):
        return [v for v in a if v in b]

    def all_equal(self, iterable):
        g = groupby(iterable)
        return next(g, True) and not next(g, False)

    def ChildrenHasError(self, ctx):
        non_terminals = [self.node_type[i] for i in ctx.children if type(i) in [DecafParser.LocationContext, DecafParser.ExprContext, DecafParser.BlockContext, DecafParser.DeclarationContext]]
        if self.ERROR in non_terminals:
            return True
        return False

    def enterProgram(self, ctx: DecafParser.ProgramContext):
        print('---------- INICIO --------------')
        self.root = ctx
        self.current_scope = TablaSimbolos()

    def enterMethod_declr(self, ctx: DecafParser.Method_declrContext):
        method = ctx.method_name().getText()
        parameters = []

        if ctx.return_type().var_type() is not None:
            tipo = ctx.return_type().var_type().getText()
        else:
            tipo = ctx.return_type().getText()
        hijos = ctx.getChildCount()

        for i in range(hijos):
            if isinstance(ctx.getChild(i), DecafParser.Var_typeContext):
                typeParameter = self.data_type[ctx.getChild(i).getText()]
                idParameter = ctx.getChild(i + 1).getText()

                parameters.append({'Tipo': typeParameter, 'Id': idParameter})
                self.tabla_parameters.Add(typeParameter, idParameter)

        
        self.tabla_methods.Add(tipo, method, parameters, None)
        
        self.NewScope()

        for parameter in parameters:
            type_symbol = self.tabla_tipos.LookUp(parameter['Tipo'])
            size = type_symbol['Size']
            offset = self.current_scope._offset
            self.current_scope.Add(parameter['Tipo'], parameter['Id'], size, offset, True)


    def exitMethod_declr(self, ctx: DecafParser.Method_declrContext):
        method = ctx.method_name().getText()
        self.tabla_parameters.Clear()
        self.PopScope()
        print('Saliendo metodo', method)

        self.node_type[ctx] = self.VOID
        entrada = f'DEF {method}'
        salida = f'EXIT DEF {method}'
        block = self.node_code[ctx.block()]
        code = [entrada] + ['\t' + x for x in block['code']] + [salida]
        for c in code:
            print(c)

    def enterVardeclr(self, ctx: DecafParser.VardeclrContext):
        tipo = ctx.var_type().getText()

        # TOMAR EN CUENTA DECLARACION DE ARRAY'S
        if ctx.field_var().var_id() is not None:
            id = ctx.field_var().var_id().getText()

            # Si no encuentra una variable, la guarda en la tabla de simbolos
            # En caso contrario, ya está declarada, y eso es ERROR.
            type_symbol = self.tabla_tipos.LookUp(tipo)
            
            size = type_symbol['Size']
            offset = self.current_scope._offset

            self.current_scope.Add(tipo, id, size, offset, False)
            
        elif ctx.field_var().array_id() is not None:
            id = ctx.field_var().array_id().getChild(0).getText()
                
            type_symbol = self.tabla_tipos.LookUp(tipo)

            tipo_array = 'array' + tipo
            size = 0

            if ctx.field_var().array_id().int_literal() is not None:
                size = int(ctx.field_var().array_id().int_literal().getText()) * self.sizes[tipo]

            if 'struct' in tipo_array:
                self.tabla_tipos.Add(tipo_array, size, self.tabla_tipos.ARRAY + self.tabla_tipos.STRUCT)
            else:
                self.tabla_tipos.Add(tipo_array, size, self.tabla_tipos.ARRAY)

            type_symbol = self.tabla_tipos.LookUp(tipo_array)

            size = type_symbol['Size']
            offset = self.current_scope._offset

            self.current_scope.Add(tipo_array, id, size, offset, False)

    def enterStatement_while(self, ctx: DecafParser.Statement_whileContext):
        begin, siguiente, true, false = self.NewLabel('while')
        self.node_code[ctx] = {
            'begin': begin,
            'next': siguiente,
            'true': true,
            'false': false
        }

        self.node_code[ctx.expr()] = {
            'true': true,
            'false': siguiente,
            'next': siguiente
        }

        self.node_code[ctx.block()] = {
            'next': begin
        }

    def enterStatement_if(self, ctx: DecafParser.Statement_ifContext):
        siguiente, true, false = self.NewLabel('if')
        # if ctx in self.node_code.keys():
        #     print('asignando next de while')
        #     siguiente = self.node_code[ctx]['next']

        self.node_code[ctx] = {
            'next': siguiente,
            'true': true,
            'false': false
        }
        if ctx.ELSE():
            self.node_code[ctx.expr()] = {
                'next': siguiente,
                'true': true,
                'false': false
            }
        else:
            self.node_code[ctx.expr()] = {
                'next': siguiente,
                'true': true,
                'false': siguiente
            }

    # def enterStruct_declr(self, cstx: DecafParser.Struct_declrContext):
    #     self.NewScope()

    # def exitStruct_declr(self, ctx: DecafParser.Struct_declrContext):
    #     tipo = ctx.getChild(0).getText() + ctx.getChild(1).getText()

    #     if self.tabla_tipos.LookUp(tipo) == 0:
    #         size_scope = self.current_scope.GetSize()
    #         self.tabla_tipos.Add(tipo, size_scope, self.tabla_tipos.STRUCT)
    #         self.tabla_struct.ExtractInfo(tipo, self.current_scope, self.tabla_tipos)
    #         self.PopScope()

    #         self.node_type[ctx] = self.VOID
    #         for child in ctx.children:
    #             if not isinstance(child, TerminalNode):
    #                 if self.node_type[child] == self.ERROR:
    #                     self.node_type[ctx] = self.ERROR
    #                     break
    #     else:
    #         self.node_type[ctx] = self.ERROR
    #         line = ctx.start.line
    #         col = ctx.start.column
    #         self.errores.Add(line, col, self.errores.IDENTIFICADOR_DECLARADO_MUCHAS_VECES)

    def enterVar_id(self, ctx: DecafParser.Var_idContext):
        parent = ctx.parentCtx
        if parent in self.node_type.keys():
            self.node_type[ctx] = self.node_type[parent]

    def exitVar_id(self, ctx: DecafParser.Var_idContext):
        # parent = ctx.parentCtx
        # if parent in self.node_type.keys() or ctx in self.node_type.keys():
        #     return

        # if ctx.getChildCount() == 1:
        id = ctx.getText()
        variable = self.Find(id)
        tipo = ''
        
        if variable['Tipo'] in [self.INT, self.STRING, self.BOOLEAN]:
            tipo = self.data_type[variable['Tipo']]
        else:
            tipo = self.VOID

        self.node_type[ctx] = tipo
        topget = self.TopGet(id)
        codigo = {
            'addr': topget,
            'code': []
        }

        self.node_code[ctx] = codigo

        

    # def enterArray_id(self, ctx: DecafParser.Array_idContext):
    #     parent = ctx.parentCtx
    #     if parent in self.node_type.keys():
    #         self.node_type[ctx] = self.node_type[parent]

    # def exitArray_id(self, ctx: DecafParser.Array_idContext):
    #     parent = ctx.parentCtx
    #     if parent in self.node_type.keys() or ctx in self.node_type.keys():
    #         return

    #     id = ctx.getChild(0).getText()
    #     variable = self.Find(id)
    #     if variable == 0:
    #         line = ctx.start.line
    #         col = ctx.start.column
    #         self.errores.Add(line, col, f'Variable "{id}" no ha sido declarada previamente.')
    #         self.node_type[ctx] = self.ERROR
    #     else:
    #         tipo = variable['Tipo']
    #         if ctx.int_literal() is not None:
    #             if 'array' in tipo:
    #                 if tipo.split('array')[-1] in [self.INT, self.STRING, self.BOOLEAN]:
    #                     self.node_type[ctx] = self.data_type[tipo.split('array')[-1]]
    #                 else:
    #                     self.node_type[ctx] = self.VOID
    #             else:
    #                 line = ctx.start.line
    #                 col = ctx.start.column
    #                 self.errores.Add(line, col, f'Variable "{id}" debe ser un array.')
    #                 self.node_type[ctx] = self.ERROR
    #         elif ctx.var_id() is not None:
    #             tipo = variable['Tipo']
    #             tipo_var = self.Find(ctx.var_id().getText())
    #             self.CheckErrorInArrayId(ctx, tipo, tipo_var)

    # def exitVar_type(self, ctx: DecafParser.Var_typeContext):
    #     self.node_type[ctx] = self.VOID

    # def exitField_var(self, ctx: DecafParser.Field_varContext):
    #     if ctx not in self.node_type.keys():
    #         if ctx.var_id() is not None:
    #             self.node_type[ctx] = self.node_type[ctx.getChild(0)]
    #         elif ctx.array_id() is not None:
    #             self.node_type[ctx] = self.node_type[ctx.getChild(0)]

    # def enterField_declr(self, ctx: DecafParser.Field_declrContext):
    #     tipo = ctx.var_type().getText()

    #     for child in ctx.children:
    #         if not isinstance(child, TerminalNode) and isinstance(child, DecafParser.Field_varContext):
    #             id = child.var_id().getText()

    #             if self.current_scope.LookUp(id) == 0:
    #                 type_symbol = self.tabla_tipos.LookUp(tipo)
    #                 size = type_symbol['Size']
    #                 offset = self.current_scope._offset
                    
    #                 self.current_scope.Add(tipo, id, size, offset, False)
    #             else:
    #                 self.node_type[child] = self.ERROR
    #                 line = child.var_id().start.line
    #                 col = child.var_id().start.column
    #                 self.errores.Add(line, col, self.errores.IDENTIFICADOR_DECLARADO_MUCHAS_VECES)

    # def exitField_declr(self, ctx: DecafParser.Field_declrContext):
    #     self.node_type[ctx] = self.VOID
    #     for child in ctx.children:
    #         if not isinstance(child, TerminalNode):
    #             if self.node_type[child] == self.ERROR:
    #                 self.node_type[ctx] = self.ERROR
    #                 break

    def exitVardeclr(self, ctx: DecafParser.VardeclrContext):
        self.node_type[ctx] = self.VOID

    def exitString_literal(self, ctx: DecafParser.String_literalContext):
        self.node_type[ctx] = self.STRING
        self.node_code[ctx] = {
            'code': [],
            'addr': ctx.getText()
        }

    def exitInt_literal(self, ctx: DecafParser.Int_literalContext):
        self.node_type[ctx] = self.INT
        self.node_code[ctx] = {
            'code': [],
            'addr': ctx.getText()
        }

    def exitBool_literal(self, ctx: DecafParser.Bool_literalContext):
        self.node_type[ctx] = self.BOOLEAN
        self.node_code[ctx] = {
            'code': [],
            'addr': ctx.getText()
        }

    def exitLiteral(self, ctx: DecafParser.LiteralContext):
        self.node_type[ctx] = self.node_type[ctx.getChild(0)]
        self.node_code[ctx] = self.node_code[ctx.getChild(0)]

    def enterBlock(self, ctx: DecafParser.BlockContext):
        if ctx in self.node_code.keys():
            for state in ctx.statement():
                self.node_code[state] = self.node_code[ctx]

    def exitBlock(self, ctx: DecafParser.BlockContext):
        hijos_tipo = [self.node_type[i] for i in ctx.children if isinstance(i, DecafParser.StatementContext)]
        filtered = list(filter(lambda tipo: tipo != self.VOID, hijos_tipo))

        addr = ''
        code = []
        statements = ctx.statement()
        # if len(statements) == 1:
        #     print('SOLO UN STATEMENT')
        #     code = self.node_code[statements[0]]['code']
        #     if 'next' in self.node_code[statements[0]].keys():
        #         print('TENGO NEXT EN BLOCK 1')
        #         code += [self.node_code[statements[0]]['next']]
        # else:
        for i in range(len(statements)):
            print('EXIT BLOCK', self.node_code[statements[i]])
            code += self.node_code[statements[i]]['code']
            # print(i, len(statements) - 1)
            # if i < len(statements) - 1:
            if 'next' in self.node_code[statements[i]].keys(): #and 'next' in self.node_code[statements[i + 1]].keys():
                print('TENGO NEXT EN BLOCK')
                code += [self.node_code[statements[i]]['next']]
                print(code)
            else:
                print('NO TENGO NEXT EN BLOCK :(')

        self.node_code[ctx] = {
            'addr': addr,
            'code': code
        }

        if len(filtered) == 0:
            self.node_type[ctx] = self.VOID
            return

        if len(filtered) == 1:
            self.node_type[ctx] = filtered.pop()
            return

        if self.all_equal(filtered):
            self.node_type[ctx] = filtered.pop()

    # def exitMethod_call(self, ctx: DecafParser.Method_callContext):
    #     name = ctx.method_name().getText()
    #     parameters = []

    #     for child in ctx.children:
    #         if isinstance(child, DecafParser.ExprContext):
    #             parameters.append(child)

    #     method_info = self.tabla_methods.LookUp(name)
    #     if method_info == 0:
    #         self.node_type[ctx] = self.ERROR
    #         line = ctx.method_name().start.line
    #         col = ctx.method_name().start.column
    #         self.errores.Add(line, col, f'El método "{name}" no existe o no hay definición del método previamente a ser invocado.')
    #         return

    #     if len(parameters) != len(method_info['Parameters']):
    #         self.node_type[ctx] = self.ERROR
    #         line = ctx.method_name().start.line
    #         col = ctx.method_name().start.column
    #         self.errores.Add(line, col, self.errores.NUMERO_PARAMETROS_METODO)
    #         return

    #     if len(parameters) == 0:
    #         self.node_type[ctx] = method_info['Tipo']
    #         return

    #     hasError = False
    #     for i in range(len(parameters)):
    #         tipo_parametro = self.node_type[parameters[i]]
    #         if tipo_parametro == self.ERROR:
    #             self.node_type[ctx] = self.ERROR
    #             return

    #         tipo_metodo = method_info['Parameters'][i]['Tipo']

    #         if tipo_parametro != tipo_metodo:
    #             hasError = True

    #             line = parameters[i].start.line
    #             col = parameters[i].start.column
    #             self.errores.Add(line, col, self.errores.TIPO_PARAMETROS_METODO)

    #         if hasError:
    #             self.node_type[ctx] = self.ERROR
    #         else:
    #             self.node_type[ctx] = method_info['Tipo']

    # def GetMethodType(self, ctx):
    #     nodo = ctx.parentCtx
    #     hijos = [str(type(i)) for i in nodo.children if not isinstance(i, TerminalNode)]
    #     # print('GET METHOD', type(nodo), nodo.getChildCount())
    #     # print('get method type:', [str(type(i)) for i in nodo.children if not isinstance(i, TerminalNode)], str(DecafParser.Return_typeContext), str(DecafParser.Return_typeContext) in [str(type(i)) for i in nodo.children if not isinstance(i, TerminalNode)])
    #     while str(DecafParser.Return_typeContext) not in hijos:
    #         nodo = nodo.parentCtx
    #         hijos = [str(type(i)) for i in nodo.children if not isinstance(i, TerminalNode)]
    #         # if isinstance(nodo, DecafParser.StatementContext):
    #         #     nodo = ctx.parentCtx.
    #         # print('GET METHOD', type(nodo), nodo.getChildCount())
    #         # print('get method type:', [str(type(i)) for i in nodo.children if not isinstance(i, TerminalNode)], str(DecafParser.Return_typeContext), str(DecafParser.Return_typeContext) in [str(type(i)) for i in nodo.children if not isinstance(i, TerminalNode)])
    #         # break

    #     if nodo.return_type().var_type() is not None:
    #         return nodo.return_type().var_type().getText()
    #     else:
    #         return nodo.return_type().getText()

    def exitStatement_if(self, ctx: DecafParser.Statement_ifContext):
        tipo_if = self.node_type[ctx.expr()]
        hijos_tipo = [i for i in ctx.children if isinstance(i, DecafParser.BlockContext)]

        if len(hijos_tipo) == 1:
            hijo_1 = hijos_tipo.pop()
            self.node_type[ctx] = self.node_type[hijo_1]
        else:
            self.node_type[ctx] = self.node_type[hijos_tipo.pop()]
        
        code = []
        siguiente = self.node_code[ctx]['next']
        if ctx.ELSE():
            print('else', self.node_code[ctx])
            # print('else', self.node_code[ctx.expr()])
            code = self.node_code[ctx.expr()]['code'] + [self.node_code[ctx]['true']] + \
                ['\t' + x for x in self.node_code[ctx.block()[0]]['code']] + ['\tGOTO ' + self.node_code[ctx]['next']] + \
                [self.node_code[ctx]['false']] + ['\t' + x for x in self.node_code[ctx.block()[-1]]['code']] 
                # + \
                # [self.node_code[ctx]['next']]

        else:
            print('BLOCK', self.node_code[ctx])
            code = self.node_code[ctx.expr()]['code'] + \
                [self.node_code[ctx]['true']] + \
                ['\t' + x for x in self.node_code[ctx.block()[0]]['code']] # + [self.node_code[ctx]['next']]

        # if ctx in self.node_code.keys():
        #     self.node_code[ctx]['code'] = code
        # else:
        self.node_code[ctx] = {
            'code': code,
            'next': siguiente
        }
            

    def exitStatement_while(self, ctx: DecafParser.Statement_whileContext):
        hijos_tipo = [self.node_type[i] for i in ctx.children if isinstance(i, DecafParser.BlockContext)]
        if len(hijos_tipo) == 1:
            self.node_type[ctx] = hijos_tipo.pop()

        code = [self.node_code[ctx]['begin']] + ['\t' + x for x in self.node_code[ctx.expr()]['code']] + \
            [self.node_code[ctx.expr()]['true']] + ['\t' + x for x in self.node_code[ctx.block()]['code']] + \
            ['\tGOTO ' + self.node_code[ctx]['begin']]
            #  + \
            # [self.node_code[ctx]['next']]
        siguiente = self.node_code[ctx]['next']
        self.node_code[ctx] = {
            'code': code,
            'next': siguiente
        }

    # def exitStatement_return(self, ctx: DecafParser.Statement_returnContext):
    #     error = self.ChildrenHasError(ctx)
    #     if error:
    #         self.node_type[ctx] = self.ERROR
    #         return

    #     self.node_type[ctx] = self.node_type[ctx.expr()]

    # def exitStatement_methodcall(self, ctx: DecafParser.Statement_methodcallContext):
    #     error = self.ChildrenHasError(ctx)
    #     if error:
    #         self.node_type[ctx] = self.ERROR
    #         return

    #     self.node_type[ctx] = self.node_type[ctx.method_call()]

    # def exitStatement_break(self, ctx: DecafParser.Statement_breakContext):
    #     error = self.ChildrenHasError(ctx)
    #     if error:
    #         self.node_type[ctx] = self.ERROR
    #         return

    #     self.node_type[ctx] = self.VOID

    def exitStatement_assign(self, ctx: DecafParser.Statement_assignContext):
        left = ctx.location()
        right = ctx.expr()
        result_type = self.VOID

        self.node_type[ctx] = result_type

        E = self.node_code[right]
        if left.var_id():
            id = left.var_id().getText()
            topget = self.TopGet(id)
            code = E['code'] + [topget + ' = ' + E['addr']]
            self.node_code[ctx] = {
                'code': code,
                'addr': ''
            }
        elif left.array_id():
            print('array id')

    def enterExpr(self, ctx: DecafParser.ExprContext):
        if ctx in self.node_code.keys():
            for expr in ctx.expr():
                self.node_code[expr] = self.node_code[ctx]

            if ctx.OR():
                inst = self.NewLabel()
                self.node_code[ctx.getChild(0)] = {
                    'true': self.node_code[ctx.getChild(0)]['true'],
                    'next': self.node_code[ctx.getChild(0)]['next'],
                    'false': inst
                }
            elif ctx.AND():
                inst = self.NewLabel()
                self.node_code[ctx.getChild(0)] = {
                    'true': inst,
                    'next': self.node_code[ctx.getChild(0)]['next'],
                    'false': self.node_code[ctx.getChild(0)]['false']
                }
            elif ctx.NOT():
                false = self.node_code[ctx]['false']
                true = self.node_code[ctx]['true']
                next_ = self.node_code[ctx]['next']
                
                self.node_code[ctx.expr()[0]] = {
                    'false': true,
                    'true': false,
                    'next': next_
                }
                

    def exitExpr(self, ctx: DecafParser.ExprContext):
        nodes_nonterminals = []
        for child in ctx.children:
            if not isinstance(child, TerminalNode):
                nodes_nonterminals.append(child)

        if len(nodes_nonterminals) == 1:
            non_terminal = nodes_nonterminals.pop()
            self.node_type[ctx] = self.node_type[non_terminal]
            if ctx.SUB():
                addr = self.newTemp()
                code = self.node_code[non_terminal]['code'] + [addr + ' = ' + '-' + self.node_code[non_terminal]['addr']]
                self.node_code[ctx] = {
                    'addr': addr,
                    'code': code
                }
            elif ctx.NOT():
                # print('NOT', self.node_code[ctx.expr()[0]])
                self.node_code[ctx] = self.node_code[ctx.expr()[0]]

                # falso = self.node_code[parent]['false']
                
                # self.node_code[parent]['false'] = self.node_code[parent]['true']
                # self.node_code[parent]['true'] = falso
            else:
                self.node_code[ctx] = self.node_code[non_terminal]
        # elif len(nodes_nonterminals) == 0:
        #     self.node_type[ctx] = self.VOID
        else:
            tipo1 = self.node_type[ctx.getChild(0)]
            tipo2 = self.node_type[ctx.getChild(2)]
            left = ctx.getChild(0)
            right = ctx.getChild(2)

            result_type = self.ERROR

            if ctx.eq_op() is not None:
                result_type = self.BOOLEAN
                me = self.node_code[ctx]
                
                code = self.node_code[left]['code'] + self.node_code[right]['code'] + \
                    ['IF ' + self.node_code[left]['addr'] + f' {ctx.eq_op().getText()} ' + self.node_code[right]['addr'] + ' GOTO ' + me['true']] + \
                    ['GOTO ' + me['false']]
                false = self.node_code[ctx]['false']
                true = self.node_code[ctx]['true']
                next_ = self.node_code[ctx]['next']
                self.node_code[ctx] = {
                    'code': code,
                    'false': false,
                    'true': true,
                    'next': next_
                }
            elif (ctx.MULTIPLY() or ctx.DIVIDE() or ctx.ADD() or ctx.SUB() or ctx.REMINDER()):
                result_type = self.INT
                addr = self.newTemp()
                code = self.node_code[left]['code'] + \
                    self.node_code[right]['code'] + \
                    [addr + ' = ' + self.node_code[left]['addr'] + ' ' + ctx.getChild(1).getText() + ' ' + self.node_code[right]['addr']]
                self.node_code[ctx] = {
                    'addr': addr,
                    'code': code
                }
            elif ctx.rel_op() is not None:
                result_type = self.BOOLEAN
                me = self.node_code[ctx]
                code = self.node_code[left]['code'] + self.node_code[right]['code'] + \
                    ['IF ' + self.node_code[left]['addr'] + f' {ctx.rel_op().getText()} ' + self.node_code[right]['addr'] + ' GOTO ' + me['true']] + \
                    ['GOTO ' + me['false']]

                false = self.node_code[ctx]['false']
                true = self.node_code[ctx]['true']
                self.node_code[ctx] = {
                    'code': code,
                    'false': false,
                    'true': true
                }
            elif ctx.OR():
                result_type = self.BOOLEAN
                parent = ctx.parentCtx
                code = self.node_code[left]['code'] + [self.node_code[left]['false']] + ['\t' + x for x in self.node_code[right]['code']]

                false = self.node_code[ctx]['false']
                true = self.node_code[ctx]['true']
                next_ = self.node_code[ctx]['next']
                self.node_code[ctx] = {
                    'false': false,
                    'true': true,
                    'next': next_,
                    'code': code
                }
                
            elif ctx.AND():
                print('ENTRANDO A AND')
                result_type = self.BOOLEAN
                parent = ctx.parentCtx

                print('LEFT', self.node_code[left])
                print('right', self.node_code[right])
                code = self.node_code[left]['code'] + [self.node_code[left]['true']] + ['\t' + x for x in self.node_code[right]['code']]

                false = self.node_code[ctx]['false']
                true = self.node_code[ctx]['true']
                next_ = self.node_code[ctx]['next']
                self.node_code[ctx] = {
                    'false': false,
                    'true': true,
                    'next': next_,
                    'code': code
                }
            else:
                result_type = self.VOID

            self.node_type[ctx] = result_type


    def CheckErrorInArrayId(self, ctx, tipo, tipo_var):
        id = ctx.getChild(0).getText()

        if ctx.int_literal() is not None:
            if 'array' in tipo:
                if tipo.split('array')[-1] in [self.INT, self.STRING, self.BOOLEAN]:
                    self.node_type[ctx] = self.data_type[tipo.split('array')[-1]]
                else:
                    self.node_type[ctx] = self.VOID
        elif ctx.var_id() is not None:

            if 'array' in tipo and tipo_var['Tipo'] == self.INT:
                if tipo.split('array')[-1] in [self.INT, self.STRING, self.BOOLEAN]:
                    self.node_type[ctx] = self.data_type[tipo.split('array')[-1]]
                else:
                    self.node_type[ctx] = self.VOID

    # def IterateChildren(self, location, parent_type, description):
    #     if location.var_id() is not None:
    #         # CASO BASE
    #         if location.var_id().location() is None:
    #             tipo_retorno = self.ERROR
    #             id = location.var_id().getChild(0).getText()
    #             if description is None:
    #                 self.node_type[location] = self.ERROR
    #                 # line = location.start.line
    #                 # col = location.start.column
    #                 # self.errores.Add(line, col, f'Variable "{id}" no ha sido declarada previamente.')
    #             else:
    #                 if 'struct' in description:
    #                     child = self.tabla_struct.GetChild(parent_type, id)
    #                     if child == 0:
    #                         self.node_type[location] = self.ERROR
    #                         line = location.start.line
    #                         col = location.start.column
    #                         self.errores.Add(line, col, f'Variable "{id}" no ha sido declarada previamente.')
    #                     else:
    #                         tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])
    #                         tipo_retorno = tipo_nodo['Tipo']
    #                         self.node_type[location] = tipo_nodo['Tipo']
    #                 else:
    #                     line = location.start.line
    #                     col = location.start.column
    #                     self.errores.Add(line, col, self.errores.MUST_STRUCT)
    #                     self.node_type[location] = self.ERROR

    #             return tipo_retorno
             
            
    #         print('----------------------------------------------------------------------------------------')
    #         id = location.var_id().getChild(0).getText()
    #         tipo_nodo = None
    #         child_type = None
    #         child_desc = None

    #         if description is None:
    #             line = location.start.line
    #             col = location.start.column
    #             self.errores.Add(line, col, self.errores.MUST_STRUCT)
    #         else:
    #             if 'struct' in description:
    #                 child = self.tabla_struct.GetChild(parent_type, id)
    #                 if child == 0:
    #                     line = location.start.line
    #                     col = location.start.column
    #                     self.errores.Add(line, col, f'Variable "{id}" no ha sido declarada previamente.')
    #                 else:
    #                     child_type = child['Tipo']
    #                     child_desc = child['Description']
    #                     tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])
    #             else:
    #                 line = location.start.line
    #                 col = location.start.column
    #                 self.errores.Add(line, col, self.errores.MUST_STRUCT)

    #         result_type = self.IterateChildren(location.var_id().location(), child_type, child_desc)
    #         self.node_type[location] = result_type
    #         return result_type

    #     elif location.array_id() is not None:
    #         # CASO BASE
            
    #         if location.array_id().location() is None:
    #             tipo_retorno = self.ERROR
    #             id = location.array_id().getChild(0).getText()
    #             if description is None:
    #                 self.node_type[location] = self.ERROR
    #                 # line = location.start.line
    #                 # col = location.start.column
    #                 # self.errores.Add(line, col, f'Variable "{id}" no ha sido declarada previamente.')
    #             else:
    #                 if 'struct' in description:
    #                     child = self.tabla_struct.GetChild(parent_type, id)
    #                     if child == 0:
    #                         self.node_type[location] = self.ERROR
    #                         line = location.start.line
    #                         col = location.start.column
    #                         self.errores.Add(line, col, f'Variable "{id}" no ha sido declarada previamente.')
    #                     else:
    #                         # HIJO IZQUIERDO
    #                         tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])
    #                         tipo_retorno = tipo_nodo['Tipo'].split('array')[-1]

    #                         # HIJO DERECHO
    #                         if location.array_id().int_literal() is not None:
    #                             if 'array' not in child['Tipo']:
    #                                 line = location.array_id().start.line
    #                                 col = location.array_id().start.column
    #                                 self.errores.Add(line, col, f'Variable "{id}" debe ser un array.') # ATENCION
    #                                 self.node_type[location] = self.ERROR
    #                             else:
    #                                 self.node_type[location] = child['Tipo'].split('array')[-1]
    #                         elif location.array_id().var_id() is not None:
    #                             tipo = child['Tipo']
    #                             tipo_var = self.Find(location.array_id().var_id().getText())
    #                             self.CheckErrorInArrayId(location.array_id(), tipo, tipo_var)
                
    #                             if self.node_type[location.array_id()] != self.ERROR:
    #                                 self.node_type[location] = tipo_nodo['Tipo'].split('array')[-1]
    #                             else:
    #                                 tipo_retorno = self.ERROR
    #                                 self.node_type[location] = self.ERROR
    #                 else:
    #                     line = location.start.line
    #                     col = location.start.column
    #                     self.errores.Add(line, col, self.errores.MUST_STRUCT)
    #                     self.node_type[location] = self.ERROR
    #             return tipo_retorno
            
    #         print('----------------------------------------------------------------------------------------')
    #         id = location.array_id().getChild(0).getText()
    #         tipo_nodo = None
    #         child_type = None
    #         child_desc = None

    #         tipo_retorno = self.VOID
    #         if 'struct' in description:
    #             child = self.tabla_struct.GetChild(parent_type, id)
    #             if child == 0:
    #                 line = location.start.line
    #                 col = location.start.column
    #                 self.errores.Add(line, col, f'Variable "{id}" no ha sido declarada previamente.')
    #             else:
    #                 child_type = child['Tipo']
    #                 child_desc = child['Description']
    #                 # tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])

    #                 # HIJO IZQUIERDO
    #                 tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])

    #                 # HIJO DERECHO
    #                 if location.array_id().int_literal() is not None:
    #                     if 'array' not in child['Tipo']:
    #                         line = location.array_id().start.line
    #                         col = location.array_id().start.column
    #                         self.errores.Add(line, col, f'Variable "{id}" debe ser un array.')
    #                         self.node_type[location] = self.ERROR
    #                 elif location.array_id().var_id() is not None:
    #                     tipo = child['Tipo']
    #                     tipo_var = self.Find(location.array_id().var_id().getText())
    #                     self.CheckErrorInArrayId(location.array_id(), tipo, tipo_var)

    #                 if location.array_id() in self.node_type.keys():
    #                     if self.node_type[location.array_id()] == self.ERROR:
    #                         tipo_retorno = self.ERROR
    #                     # self.node_type[location] = self.ERROR
    #         else:
    #             line = location.start.line
    #             col = location.start.column
    #             self.errores.Add(line, col, self.errores.MUST_STRUCT)

    #         result_type = self.IterateChildren(location.array_id().location(), child_type, child_desc)
    #         self.node_type[location] = result_type
    #         if tipo_retorno == self.ERROR:
    #             self.node_type[location] = tipo_retorno
    #             result_type = tipo_retorno
    #         return result_type

    def enterLocation(self, ctx: DecafParser.LocationContext):
        parent = ctx.parentCtx

        if ctx in self.node_type.keys():
            return
        if ctx.var_id() is not None:
            if ctx.var_id().location() is None:
                return
        elif ctx.array_id() is not None:
            if ctx.array_id().location() is None:
                return

        
        if ctx.var_id() is not None:
            if ctx.var_id().location() is not None:
                print('------------ LOCATION ENTRADA -------------------')
                id = ctx.var_id().getChild(0).getText()
                # self.current_scope.ToTable()
                
                symbol = self.Find(id)
                tipo_id = self.tabla_tipos.LookUp(symbol['Tipo'])
                print('TIPO VARIABLE', tipo_id) 
                result_type = self.IterateChildren(ctx.var_id().location(), tipo_id['Tipo'], tipo_id['Description'])
                self.node_type[ctx] = result_type
                print('------------ LOCATION SALIDA -------------------', result_type)

        if ctx.array_id() is not None:
            if ctx.array_id().location() is not None:
                print('------------ LOCATION ENTRADA -------------------')
                id = ctx.array_id().getChild(0).getText()
                symbol = self.Find(id)
                tipo_id = self.tabla_tipos.LookUp(symbol['Tipo'])
                # print('ARRAY ID ENTER LOCATION', id, tipo_id)
                result_type = self.IterateChildren(ctx.array_id().location(), tipo_id['Tipo'], tipo_id['Description'])
                self.node_type[ctx] = result_type


            # HIJO IZQUIERDO
            # tipo_nodo = self.tabla_tipos.LookUp(tipo_id['Tipo'])

            # HIJO DERECHO
                if ctx.array_id().var_id() is not None:
                    tipo = tipo_id['Tipo']
                    tipo_var = self.Find(ctx.array_id().var_id().getText())
                    self.CheckErrorInArrayId(ctx.array_id(), tipo, tipo_var)


                print('------------ LOCATION SALIDA -------------------', result_type)

    def exitLocation(self, ctx: DecafParser.LocationContext):
        if ctx not in self.node_type.keys():
            self.node_type[ctx] = self.node_type[ctx.getChild(0)]
        if ctx not in self.node_code.keys():
            self.node_code[ctx] = self.node_code[ctx.getChild(0)]
        


    # def exitDeclaration(self, ctx: DecafParser.DeclarationContext):
    #     self.node_type[ctx] = self.node_type[ctx.getChild(0)]

    def exitProgram(self, ctx: DecafParser.ProgramContext):

        self.current_scope.ToTable()
        print('---------- FIN --------------')

        # self.tabla_methods.ToTable()
        # self.tabla_struct.ToTable()

        # for i, j in self.node_type.items():
        #     if isinstance(i, DecafParser.Var_idContext):
        #         print(i, j)
