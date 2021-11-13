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

        self.pool_temps = []
        self.fill_temps()
        
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

        self.ambitos = []
        self.current_scope = None
        self.tabla_tipos = TablaTipos()
        self.errores = SemanticError()
        self.tabla_methods = TablaMetodos()
        self.tabla_struct = TablaStruct()
        self.tabla_parameters = TablaParametros()

        self.codigogenerado = []
        
        self.node_type = {}
        self.node_code = {}

        super().__init__()

    def fill_temps(self):
        for i in range(5):
            tmp = f't{self.temp}'
            self.temp += 1
            self.pool_temps.append(tmp)
            # self.pool_temps.reverse()

    def return_temp(self, tmp):
        var, isTemp = [*tmp]
        if isTemp:
            self.pool_temps.append(var)

    def newTemp(self):
        if len(self.pool_temps) == 0:
            self.fill_temps()

        self.pool_temps.sort()
        temp = self.pool_temps.pop(0)
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
            self.inst += 1
            return control

    def TopGet(self, id, offset_required = None):
        variable = self.current_scope.LookUp(id)
        if variable != 0:
            offset = variable['Offset']
            if offset_required:
                offset = offset_required
                
            addr = f'L[{offset}]'
            return addr

        elif self.Find(id) != 0:
            variable = self.Find(id)
            offset = variable['Offset']
            if offset_required:
                offset = offset_required
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

        self.node_code[ctx] = {
            'code': code
        }

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
                tipo_complejo = self.tabla_tipos.LookUp(tipo)
                size = int(ctx.field_var().array_id().int_literal().getText()) * tipo_complejo['Size']

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

    def enterStruct_declr(self, cstx: DecafParser.Struct_declrContext):
        self.NewScope()

    def exitStruct_declr(self, ctx: DecafParser.Struct_declrContext):
        tipo = ctx.getChild(0).getText() + ctx.getChild(1).getText()

        size_scope = self.current_scope.GetSize()
        self.tabla_tipos.Add(tipo, size_scope, self.tabla_tipos.STRUCT)
        self.tabla_struct.ExtractInfo(tipo, self.current_scope, self.tabla_tipos)
        self.PopScope()

        self.node_type[ctx] = self.VOID

    def enterVar_id(self, ctx: DecafParser.Var_idContext):
        parent = ctx.parentCtx
        if parent in self.node_type.keys():
            self.node_type[ctx] = self.node_type[parent]

    def exitVar_id(self, ctx: DecafParser.Var_idContext):
        parent = ctx.parentCtx
        if parent in self.node_type.keys() or ctx in self.node_type.keys():
            return

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
            'addr': (topget, False),
            'code': []
        }

        self.node_code[ctx] = codigo

    def enterArray_id(self, ctx: DecafParser.Array_idContext):
        parent = ctx.parentCtx
        if parent in self.node_type.keys():
            self.node_type[ctx] = self.node_type[parent]

    def exitArray_id(self, ctx: DecafParser.Array_idContext):
        parent = ctx.parentCtx
        if parent in self.node_type.keys() or ctx in self.node_type.keys():
            return

        id = ctx.getChild(0).getText()
        variable = self.Find(id)
        tipo = variable['Tipo']
        offset = variable['Offset']
        if ctx.int_literal() is not None:
            if 'array' in tipo:
                if tipo.split('array')[-1] in [self.INT, self.STRING, self.BOOLEAN]:
                    self.node_type[ctx] = self.data_type[tipo.split('array')[-1]]
                else:
                    self.node_type[ctx] = self.VOID
        elif ctx.var_id() is not None:
            tipo = variable['Tipo']
            tipo_var = self.Find(ctx.var_id().getText())
            self.CheckErrorInArrayId(ctx, tipo, tipo_var)

        if isinstance(ctx.parentCtx, DecafParser.Field_varContext):
            return

        temp = self.newTemp()
        temp2 = self.newTemp()
        tipo_real = tipo.split('array')[-1]
        size = self.tabla_tipos.LookUp(tipo_real)['Size']

        addr_viejo = self.node_code[ctx.getChild(2)]['addr'][0]
        code = self.node_code[ctx.getChild(2)]['code'] + \
            [f'{temp} = {size} * {addr_viejo}'] + \
            [f'{temp2} = {temp} + {offset}']

        self.return_temp(self.node_code[ctx.getChild(2)]['addr'])
        self.return_temp((temp, True))
        self.node_code[ctx] = {
            'code': code,
            'addr': (temp2, True)
        }
        

    def exitVar_type(self, ctx: DecafParser.Var_typeContext):
        self.node_type[ctx] = self.VOID

    def exitField_var(self, ctx: DecafParser.Field_varContext):
        if ctx not in self.node_type.keys():
            if ctx.var_id() is not None:
                self.node_type[ctx] = self.node_type[ctx.getChild(0)]
            elif ctx.array_id() is not None:
                self.node_type[ctx] = self.node_type[ctx.getChild(0)]

    def exitVardeclr(self, ctx: DecafParser.VardeclrContext):
        self.node_type[ctx] = self.VOID

    def exitString_literal(self, ctx: DecafParser.String_literalContext):
        self.node_type[ctx] = self.STRING
        self.node_code[ctx] = {
            'code': [],
            'addr': (ctx.getText(), False)
        }

    def exitInt_literal(self, ctx: DecafParser.Int_literalContext):
        self.node_type[ctx] = self.INT
        self.node_code[ctx] = {
            'code': [],
            'addr': (ctx.getText(), False)
        }

    def exitBool_literal(self, ctx: DecafParser.Bool_literalContext):
        self.node_type[ctx] = self.BOOLEAN
        self.node_code[ctx] = {
            'code': [],
            'addr': (ctx.getText(), False)
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
        for i in range(len(statements)):
            code += self.node_code[statements[i]]['code']
            
            if 'next' in self.node_code[statements[i]].keys(): #and 'next' in self.node_code[statements[i + 1]].keys():
                code += [self.node_code[statements[i]]['next']]
            else:
                pass

        self.node_code[ctx] = {
            'addr': (addr, False),
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

    def exitMethod_call(self, ctx: DecafParser.Method_callContext):
        name = ctx.method_name().getText()
        parameters = []

        for child in ctx.children:
            if isinstance(child, DecafParser.ExprContext):
                parameters.append(child)

        method_info = self.tabla_methods.LookUp(name)
        code = f'CALL {name}, '
        if len(parameters) == 0:
            code += str(0)
            self.node_type[ctx] = method_info['Tipo']
            self.node_code[ctx] = {
                'code': [code],
                'addr': ('R', False)
            }
            return

        parameter_code = []
        total_code = []
        for i in range(len(parameters)):
            param = self.node_code[parameters[i]]['addr'][0]
            
            self.return_temp(self.node_code[parameters[i]]['addr'])

            total_code += self.node_code[parameters[i]]['code']
            parameter_code += [f'PARAM {param}']

            self.node_type[ctx] = method_info['Tipo']

        code += str(len(parameters))
        self.node_code[ctx] = {
            'code': total_code + parameter_code + [code],
            'addr': ('R', False)
        }

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
            code = self.node_code[ctx.expr()]['code'] + [self.node_code[ctx]['true']] + \
                ['\t' + x for x in self.node_code[ctx.block()[0]]['code']] + ['\tGOTO ' + self.node_code[ctx]['next']] + \
                [self.node_code[ctx]['false']] + ['\t' + x for x in self.node_code[ctx.block()[-1]]['code']]

        else:
            code = self.node_code[ctx.expr()]['code'] + \
                [self.node_code[ctx]['true']] + \
                ['\t' + x for x in self.node_code[ctx.block()[0]]['code']]

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

        siguiente = self.node_code[ctx.expr()]['false']

        self.node_code[ctx] = {
            'code': code,
            'next': siguiente
        }

    def exitStatement_return(self, ctx: DecafParser.Statement_returnContext):
        self.node_type[ctx] = self.node_type[ctx.expr()]

        addr = self.node_code[ctx.expr()]['addr']
        code = self.node_code[ctx.expr()]['code'] + [f'RETURN {addr[0]}']

        self.return_temp(addr)

        self.node_code[ctx] = {
            'code': code
        }

    def exitStatement_methodcall(self, ctx: DecafParser.Statement_methodcallContext):
        self.node_type[ctx] = self.node_type[ctx.method_call()]
        self.node_code[ctx] = self.node_code[ctx.method_call()]

    def exitStatement_assign(self, ctx: DecafParser.Statement_assignContext):
        left = ctx.location()
        right = ctx.expr()
        result_type = self.VOID

        self.node_type[ctx] = result_type

        E = self.node_code[right]
        if left.var_id():
            id = left.var_id().getText()
            
            optional = []
            if left in self.node_code.keys():
                topget = self.node_code[left]['addr'][0]
                optional = self.node_code[left]['code']
            else:
                topget = self.TopGet(id)
                
            code = E['code'] + optional + [topget + ' = ' + E['addr'][0]]
            self.return_temp(E['addr'])
            self.node_code[ctx] = {
                'code': code,
                'addr': ('', False)
            }
        elif left.array_id():
            id = left.array_id().ID().getText()
            topget = self.TopGet(id, self.node_code[left]['addr'][0])
            addr = E['addr']
            
            code = self.node_code[left]['code'] + E['code'] + \
                [f'{topget} = {addr[0]}']

            self.return_temp(self.node_code[left]['addr'])
            self.return_temp(addr)
                
            self.node_code[ctx] = {
                'code': code,
                'addr': ('', False)
            }   

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
                code = self.node_code[non_terminal]['code'] + [addr + ' = ' + '-' + self.node_code[non_terminal]['addr'][0]]
                self.return_temp(self.node_code[non_terminal]['addr'])
                self.node_code[ctx] = {
                    'addr': (addr, True),
                    'code': code
                }
            elif ctx.NOT():
                self.node_code[ctx] = self.node_code[ctx.expr()[0]]
            else:
                self.node_code[ctx] = self.node_code[non_terminal]
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
                    ['IF ' + self.node_code[left]['addr'][0] + f' {ctx.eq_op().getText()} ' + self.node_code[right]['addr'][0] + ' GOTO ' + me['true']] + \
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
                    [addr + ' = ' + self.node_code[left]['addr'][0] + ' ' + ctx.getChild(1).getText() + ' ' + self.node_code[right]['addr'][0]]

                self.return_temp(self.node_code[left]['addr'])
                self.return_temp(self.node_code[right]['addr'])
                self.node_code[ctx] = {
                    'addr': (addr, True),
                    'code': code
                }
            elif ctx.rel_op() is not None:
                result_type = self.BOOLEAN
                me = self.node_code[ctx]
                code = self.node_code[left]['code'] + self.node_code[right]['code'] + \
                    ['IF ' + self.node_code[left]['addr'][0] + f' {ctx.rel_op().getText()} ' + self.node_code[right]['addr'][0] + ' GOTO ' + me['true']] + \
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
                result_type = self.BOOLEAN
                parent = ctx.parentCtx

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

    def IterateChildren(self, location, parent_type, description):
        if location.var_id():
            # CASO BASE
            if location.var_id().location() is None:
                tipo_retorno = self.ERROR
                id = location.var_id().getChild(0).getText()

                child = self.tabla_struct.GetChild(parent_type, id)
                tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])
                self.tabla_struct.ToTable()
                tipo_retorno = tipo_nodo['Tipo']
                self.node_type[location] = tipo_nodo['Tipo']

                num = child['Offset']
                total = {
                    'code': [],
                    'addr': (str(num), False)
                }
                self.node_code[location] = total

                return tipo_retorno, total
             
            
            print('----------------------------------------------------------------------------------------')
            id = location.var_id().getChild(0).getText()
            tipo_nodo = None
            child_type = None
            child_desc = None

            child = self.tabla_struct.GetChild(parent_type, id)
            child_type = child['Tipo']
            child_desc = child['Description']
            tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])

            result_type, num = self.IterateChildren(location.var_id().location(), child_type, child_desc)

            temp = self.newTemp()
            code = [temp + ' = ' + str(num['addr'][0]) + ' + ' + str(child['Offset'])]
            self.return_temp(num['addr'])
            total = {
                'code': num['code'] + code,
                'addr': (temp, True)
            }
            self.node_type[location] = result_type
            self.node_code[location] = total
            return result_type, total

        elif location.array_id():
            # CASO BASE
            
            if location.array_id().location() is None:
                tipo_retorno = self.ERROR
                id = location.array_id().getChild(0).getText()

                child = self.tabla_struct.GetChild(parent_type, id)
                # HIJO IZQUIERDO
                tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])
                tipo_retorno = tipo_nodo['Tipo'].split('array')[-1]

                # HIJO DERECHO
                addr = ''
                tipo_ = ''
                if location.array_id().int_literal():
                    self.node_type[location] = child['Tipo'].split('array')[-1]
                    tipo_ = child['Tipo'].split('array')[-1]

                    num = location.array_id().int_literal().getText()
                    addr = num
                elif location.array_id().var_id():
                    tipo = child['Tipo']
                    tipo_ = tipo
                    tipo_var = self.Find(location.array_id().var_id().getText())
                    self.CheckErrorInArrayId(location.array_id(), tipo, tipo_var)
    
                    self.node_type[location] = tipo_nodo['Tipo'].split('array')[-1]
                    num = self.TopGet(location.array_id().var_id().getText())
                    addr = num
                
                temp = self.newTemp()
                temp2 = self.newTemp()
                offset = child['Offset']
                size = self.tabla_tipos.LookUp(tipo_)['Size']
                code = [f'{temp} = {size} * {addr}']
                code += [f'{temp2} = {temp} + {offset}']

                self.return_temp((temp, True))
                total = {
                    'code': code,
                    'addr': (temp2, True)
                }
                self.node_code[location] = total
                return tipo_retorno, total
            
            print('----------------------------------------------------------------------------------------')
            id = location.array_id().getChild(0).getText()
            tipo_nodo = None
            child_type = None
            child_desc = None

            tipo_retorno = self.VOID
            child = self.tabla_struct.GetChild(parent_type, id)

            child_type = child['Tipo']
            child_desc = child['Description']
            # tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])

            # HIJO IZQUIERDO
            tipo_nodo = self.tabla_tipos.LookUp(child['Tipo'])

            # HIJO DERECHO
            if location.array_id().var_id():
                tipo = child['Tipo']
                tipo_var = self.Find(location.array_id().var_id().getText())
                self.CheckErrorInArrayId(location.array_id(), tipo, tipo_var)

            result_type, num = self.IterateChildren(location.array_id().location(), child_type, child_desc)
            self.node_type[location] = result_type

            topget_aux = ''
            if isinstance(location.array_id().getChild(2), DecafParser.Int_literalContext):
                topget_aux = location.array_id().int_literal().getText()
            elif isinstance(location.array_id().getChild(2), DecafParser.Var_idContext):
                topget_aux = self.TopGet(location.array_id().var_id().getText())
            temp = self.newTemp()
            temp2 = self.newTemp()
            temp3 = self.newTemp()

            offset = child['Offset']
            size = self.tabla_tipos.LookUp(child['Tipo'].split('array')[-1])['Size']

            addr = num['addr']

            code = [f'{temp} = {size} * {topget_aux}']
            code += [f'{temp2} = {temp} + {offset}']
            code += [f'{temp3} = {temp2} + {addr[0]}']

            self.return_temp(addr)
            self.return_temp((temp, True))
            self.return_temp((temp2, True))
            total = {
                'code': num['code'] + code,
                'addr': (temp3, True)
            }
            self.node_code[location] = total

            return result_type, total

    def enterLocation(self, ctx: DecafParser.LocationContext):
        parent = ctx.parentCtx

        if ctx in self.node_type.keys():
            return
        if ctx.var_id():
            if ctx.var_id().location() is None:
                return
        elif ctx.array_id():
            if ctx.array_id().location() is None:
                return

        
        if ctx.var_id():
            if ctx.var_id().location():
                print('------------ LOCATION ENTRADA -------------------')
                id = ctx.var_id().getChild(0).getText()
                
                symbol = self.Find(id)
                tipo_id = self.tabla_tipos.LookUp(symbol['Tipo'])
                result_type, total = self.IterateChildren(ctx.var_id().location(), tipo_id['Tipo'], tipo_id['Description'])
                self.node_type[ctx] = result_type

                temp = self.newTemp()
                offset = symbol['Offset']
                code = f'{temp} = {offset} + ' + total['addr'][0]

                topget = self.TopGet(id, temp)
                self.return_temp(total['addr'])
                self.return_temp((temp, True))

                self.node_code[ctx] = {
                    'code': total['code'] + [code],
                    'addr': (topget, False)
                }

                print('------------ LOCATION SALIDA -------------------', result_type)

        if ctx.array_id():
            if ctx.array_id().location():
                print('------------ LOCATION ENTRADA -------------------')
                id = ctx.array_id().getChild(0).getText()
                symbol = self.Find(id)
                tipo_id = self.tabla_tipos.LookUp(symbol['Tipo'])

                result_type, total = self.IterateChildren(ctx.array_id().location(), tipo_id['Tipo'], tipo_id['Description'])
                self.node_type[ctx] = result_type

                temp = self.newTemp()
                temp2 = self.newTemp()
                temp3 = self.newTemp()

                topget_aux = ''
                if isinstance(ctx.array_id().getChild(2), DecafParser.Int_literalContext):
                    topget_aux = ctx.array_id().int_literal().getText()
                elif isinstance(ctx.array_id().getChild(2), DecafParser.Var_idContext):
                    topget_aux = self.TopGet(ctx.array_id().var_id().getText())

                size = self.tabla_tipos.LookUp(symbol['Tipo'].split('array')[-1])['Size']
                code = [f'{temp} = {topget_aux} * {size}']

                offset = symbol['Offset']
                code += [f'{temp2} = {offset} + {temp}']

                addr = total['addr']
                code += {f'{temp3} = {temp2} + {addr[0]}'}

                self.return_temp(addr)
                self.return_temp((temp, True))
                self.return_temp((temp2, True))
                self.node_code[ctx] = {
                    'code': total['code'] + code,
                    'addr': (temp3, True)
                }

                print('------------ LOCATION SALIDA -------------------', result_type)

    def exitLocation(self, ctx: DecafParser.LocationContext):
        try:
            if ctx not in self.node_type.keys():
                self.node_type[ctx] = self.node_type[ctx.getChild(0)]
                # return
        except:
            self.node_type[ctx] = self.VOID
            
        if ctx not in self.node_code.keys():
            self.node_code[ctx] = self.node_code[ctx.getChild(0)]
        
    def exitDeclaration(self, ctx: DecafParser.DeclarationContext):
        self.node_type[ctx] = self.node_type[ctx.getChild(0)]

        if ctx.getChild(0) in self.node_code.keys():
            self.node_code[ctx] = self.node_code[ctx.getChild(0)]

    def exitProgram(self, ctx: DecafParser.ProgramContext):

        self.current_scope.ToTable()
        print('---------- FIN --------------')

        code = []
        for declr in ctx.declaration():
            if declr in self.node_code.keys():
                code += self.node_code[declr]['code'] + ['\n']

        self.codigogenerado = code.copy()
