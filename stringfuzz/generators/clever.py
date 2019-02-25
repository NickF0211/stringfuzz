import random
import copy

from stringfuzz.smt import *
from stringfuzz.ast import *
from stringfuzz.util import coin_toss, random_string
from stringfuzz.ast_walker import ASTWalker

__all__ = [
    'clever',
    "STRING",
    "INT",
    "BOOL",
    "VARIABLE_SORTS"
]

STRING         = 's'
INT            = 'i'
BOOL           = 'b'
VARIABLE_SORTS = [STRING, INT, BOOL]

_operators = {
    STRING : [
        ContainsNode,
        AtNode,
        LengthNode,
        IndexOf2Node,
        PrefixOfNode,
        SuffixOfNode,
        StringReplaceNode,
        SubstringNode,
        ConcatNode,
    ],
    INT : [
        GtNode,
        LtNode,
        GteNode,
        LteNode,
        PlusNode,
        MulNode,
    ],
    BOOL : [
        NotNode,
        AndNode,
        OrNode,
        EqualNode
    ]
}

_tree_nonterminal  = IfThenElseNode
_expr_nontermianls = _operators[BOOL]
_var_sorts         = []

# global config
_max_str_lit_length  = 0
_max_int_lit         = 0
_literal_probability = 0.0

class VarReplacer(ASTWalker):
    def __init__(self, ast, variables):
        super().__init__(ast)
        self.variables = variables

    def walk_expression(self, expression, parent):

        self.enter_expression(expression, parent)

        for i in range(len(expression.body)):
            sub_expression = expression.body[i]

            if isinstance(sub_expression, ExpressionNode):
                self.walk_expression(sub_expression, expression)

            if isinstance(sub_expression, IdentifierNode):
                if sub_expression in self.variables:
                    expression.body[i] = self.variables[sub_expression]
                self.walk_identifier(sub_expression, expression)

            if isinstance(sub_expression, LiteralNode):
                self.walk_literal(sub_expression, expression)

        self.exit_expression(expression, parent)


class LibInserter(ASTWalker):
    def __init__(self, ast, sort):
        super().__init__(ast)
        self.sort           = sort
        self.candidates     = {}

    def walk_expression(self, expression, parent, depth=0, pos_in_parent=-1):
        if expression.returns(self.sort) and pos_in_parent > -1:
            if not depth in self.candidates:
                self.candidates[depth] = []
            self.candidates[depth].append((parent, pos_in_parent))

        for i in sorted(range(len(expression.body)), key=lambda k: random.random()):
            sub_expression = expression.body[i]
            if isinstance(sub_expression, ExpressionNode):
                self.walk_expression(sub_expression, expression, depth+1, i)

    def insert_lib_calls(self, name, sig, variables, num_lib_calls):
        min_depth = -1
        for _ in range(num_lib_calls):
            depth = random.choice(list(self.candidates.keys()))
            c = random.choice(list(range(len(self.candidates[depth]))))
            parent, pos = self.candidates[depth][c]
            del self.candidates[depth][c]

            if self.candidates[depth] == []:
                del self.candidates[depth]

            if depth < min_depth or min_depth == -1:
                min_depth = depth

            parent.body[pos] = call_func(name, sig, variables)

        return min_depth


class LibRenamer(ASTWalker):
    def __init__(self, ast, old_name, new_name):
        super().__init__(ast)
        self.old_name = old_name
        self.new_name = new_name

    def enter_identifier(self, identifier, parent):
        if identifier.name == self.old_name:
            identifier.name = self.new_name

    def enter_expression(self, expression, parent):
        if expression._symbol.name == self.old_name:
            expression._symbol.name = self.new_name

class Slicer(ASTWalker):
    def __init__(self, ast, name):
        super().__init__(ast)
        self.name      = name
        self.conds     = []
        self.new_body  = None

    def walk_expression(self, expression, parent, pos_polarity=True):
        if isinstance(expression, IfThenElseNode):
            if self.name in str(expression.body[0]):
                #assert THEN and ELSE Branch are different
                self.conds.append(NotNode(EqualNode(expression.body[1], expression.body[2])))
                self.walk_expression(expression.body[0], expression, pos_polarity)
            elif self.name in str(expression.body[1]):
                self.conds.append(expression.body[0])
                self.walk_expression(expression.body[1], expression, pos_polarity)
            elif self.name in str(expression.body[2]):
                self.conds.append(NotNode(expression.body[0]))
                self.walk_expression(expression.body[2], expression, pos_polarity)
        elif isinstance(expression, NotNode):
            self.walk_expression(expression.body[0], expression, not(pos_polarity))
        elif isinstance(expression, AndNode):
            #we want ensure the other part of AND is True.
            index = 0
            for i in range(len(expression.body)):
                if self.name not in str(expression.body[i]):
                    self.conds.append(expression.body[i])
                else:
                    index = i
            self.walk_expression(expression.body[index], expression, pos_polarity)
        elif isinstance(expression, OrNode):
            #we want to ensure the other part of OR is False
            index = 0
            for i in range(len(expression.body)):
                if self.name not in str(expression.body[i]):
                    self.conds.append(NotNode(expression.body[i]))
                else:
                    index = i
            self.walk_expression(expression.body[index], expression, pos_polarity)
        else:
            if (pos_polarity):
                self.new_body = expression
            else:
                self.new_body = NotNode(expression)


def call_func(name, signature, variables):
    if isinstance(variables, dict):
        return GenericExpressionNode(name, *[random.choice(variables[s]) for s in signature])
    return GenericExpressionNode(name, *variables)

def get_all_returning_a(sort, nodes):
    return list(filter(lambda node: node.returns(sort), nodes))

def make_random_literal(sort):
    if sort == STRING_SORT:
        return StringLitNode(random_string(_max_str_lit_length))

    if sort == INT_SORT:
        return IntLitNode(random.randint(0, _max_int_lit))

    if sort == BOOL_SORT:
        return BoolLitNode(coin_toss())

    raise ValueError('unknown sort {}'.format(sort))

def should_choose_literal():
    global _literal_probability
    return random.random() < _literal_probability

def make_random_terminal(variables, sort):
    # randomly choose between a variable or a literal
    if should_choose_literal() or sort not in variables:
        return make_random_literal(sort)

    return random.choice(variables[sort])

def make_random_expression(variables, sort, depth):
    # at depth 0, make a terminal
    if depth < 1:
        return make_random_terminal(variables, sort)

    # randomly shrink the depth
    shrunken_depth = random.randint(0, depth - 1)

    # get random expression generator
    candidate_nodes = get_all_returning_a(sort, _expr_nontermianls)
    expression_node = random.choice(candidate_nodes)
    signature       = expression_node.get_signature()
    num_args        = len(signature)

    # if the expression takes any sort, pick one
    if expression_node.accepts(ANY_SORT):
        collapsed_sort = random.choice(_var_sorts)
        signature      = [collapsed_sort for i in range(num_args)]

    # generate random arguments
    random_args = [make_random_expression(variables, arg_sort, shrunken_depth) for arg_sort in signature]

    # build expression
    expression = expression_node(*random_args)

    return expression

def make_random_tree(variables, sort, tree_depth, expr_depth):
    # at depth 0, make a terminal
    if tree_depth < 1:
        return make_random_expression(variables, sort, expr_depth)

    # randomly shrink the depth
    shrunken_depth = random.randint(0, tree_depth - 1)

    # build expression
    signature   = [sort, sort]
    random_args = [make_random_tree(variables, arg_sort, shrunken_depth, expr_depth) for arg_sort in signature]
    random_args = [make_random_expression(variables, BOOL_SORT, expr_depth)] + random_args
    expression  = _tree_nonterminal(*random_args)

    return expression

def get_sort(expression, lib_sort):
    if isinstance(expression, ExpressionNode):
        sort = expression.get_sort()
        if isinstance(expression, GenericExpressionNode) and sort == UNIT_SORT:
            #hard code the library sort for now since library is the only function allowed
            return lib_sort
        else:
            return sort
    else:
        return _var_sorts[0]

def make_clever(max_client_depth, num_client_vars, max_lib_depth, num_lib_vars, num_lib_calls, max_expr_depth, max_str_lit_length, max_int_lit, literal_probability, sorts, sliced, client_name="client", old_lib_name="old_lib", new_lib_name="new_lib"):

    # check args
    if max_client_depth < 1:
        raise ValueError('the maximum client depth must be at least 1')

    if max_expr_depth < 1:
        raise ValueError('the maximum expr depth must be at least 1')

    if num_lib_calls < 1:
        raise ValueError('the number of library calls must be at least 1')

    if max_lib_depth < 1:
        raise ValueError('the maximum library depth must be at least 1')

    if len(sorts) < 1 or any(map(lambda x: x not in VARIABLE_SORTS, sorts)):
        raise ValueError('invalid sorts: {!r}'.format(sorts))

    global _max_str_lit_length
    global _max_int_lit
    global _literal_probability
    global _var_sorts
    global _expr_nontermianls

    # set global config
    _max_str_lit_length  = max_str_lit_length
    _max_int_lit         = max_int_lit
    _literal_probability = literal_probability

    _var_sorts = []
    for s in sorts:
        if s == STRING:
            _expr_nontermianls.extend(_operators[STRING])
            _var_sorts.append(STRING_SORT)
        if s == INT:
            _expr_nontermianls.extend(_operators[INT])
            _var_sorts.append(INT_SORT)
        if s == BOOL:
            _var_sorts.append(BOOL_SORT)

    # create function definitions
    lib_sort    = random.choice(_var_sorts)
    lib_args    = [random.choice(_var_sorts) for s in range(num_lib_vars)]
    client_sort = random.choice(_var_sorts)
    client_args = [random.choice(_var_sorts) for s in range(num_client_vars)]

    # create variables
    arg_var_map = []

    client_vars = {s: [] for s in set(client_args)}
    client_decls = []
    for s in client_args:
        v = smt_new_arg()
        client_vars[s].append(v)
        client_decls.append((v,s))
        arg_var_map.append(v)
    # create variable declarations
    client_decls = smt_declare_args(client_decls)

    variables = []
    decls = []
    for s in client_args:
        v = smt_new_var()
        variables.append(v)
        decls.append(smt_declare_var(v, sort=s))

    lib_vars = {s: [] for s in set(lib_args)}
    lib_decls = []
    for s in lib_args:
        v = smt_new_arg()
        lib_vars[s].append(v)
        lib_decls.append((v,s))
    # create variable declarations
    lib_decls = smt_declare_args(lib_decls)

    # Generate client and libs
    old_lib_body = make_random_tree(lib_vars, lib_sort, max_lib_depth, max_expr_depth)
    new_lib_body = make_random_tree(lib_vars, lib_sort, max_lib_depth, max_expr_depth)

    decls.append(smt_define_func(old_lib_name, lib_decls, lib_sort, old_lib_body))
    decls.append(smt_define_func(new_lib_name, lib_decls, lib_sort, new_lib_body))

    client_body = make_random_tree(client_vars, client_sort, max_client_depth, max_expr_depth)
    inserter = LibInserter([client_body], lib_sort)
    old_client_body = inserter.walk()[0]
    random_args = [make_random_expression(client_vars, arg_sort, max_expr_depth) for arg_sort in lib_args]
    lib_call_depth = inserter.insert_lib_calls(old_lib_name, lib_args, random_args, num_lib_calls)
    new_client_body = LibRenamer([copy.deepcopy(old_client_body)], old_lib_name, new_lib_name).walk()[0]

    print(";BEGIN STRINGFUZZ STATS")
    print("; max_client_depth", max_client_depth)
    print("; num_client_vars", num_client_vars)
    print("; max_lib_depth", max_lib_depth)
    print("; num_lib_vars", num_lib_vars)
    print("; num_lib_calls", num_lib_calls)
    print("; max_expr_depth", max_expr_depth)
    print("; lowest_lib_call_depth", lib_call_depth)
    print("; sliced", 1 if sliced else 0)
    print(";END STRINGFUZZ STATS")

    # assert that the client calling the old library is not equal to the client calling the new library
    asserts = [AssertNode(NotNode(EqualNode(call_func(client_name+"_old", client_args, variables), call_func(client_name+"_new", client_args, variables))))]

    # get slice asserts and slice
    if sliced:
        asserts=[]
        slicer = Slicer([old_client_body], old_lib_name)
        slicer.walk()
        old_client_body = slicer.new_body
        new_client_body = LibRenamer([copy.deepcopy(old_client_body)], old_lib_name, new_lib_name).walk()[0]
        #construct counter example query
        queryNode = NotNode(EqualNode(old_client_body , new_client_body ))
        var_dict = dict(list(zip(arg_var_map, variables)))
        conds = VarReplacer(slicer.conds +[queryNode], var_dict).walk()
        conds = [AssertNode(c) for c in conds]
        asserts.extend(conds)

    if not sliced:
        decls.append(smt_define_func(client_name+"_old", client_decls, client_sort, old_client_body))
        decls.append(smt_define_func(client_name+"_new", client_decls, client_sort, new_client_body))

    # add check-sat
    expressions = asserts + [CheckSatNode()]

    return decls + expressions

# public API
def clever(*args, **kwargs):
    smt_reset_counters()
    return make_clever(*args, **kwargs)