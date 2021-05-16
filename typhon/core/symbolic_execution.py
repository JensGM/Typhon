from .futil import function_ast
from .futil import lambda_ast
from collections import OrderedDict
from collections import namedtuple
from functools import partial
from functools import reduce
from itertools import count
import ast
import z3


class StrictVisitor(ast.NodeVisitor):
    def visit(self, node):
        node_type_name = node.__class__.__name__
        method = 'visit_' + node_type_name
        try:
            visitor = getattr(self, method)
        except AttributeError:
            raise NotImplementedError(f'{node_type_name} are not supported')
        return visitor(node)


class AxiomFinder(ast.NodeVisitor):
    def __init__(self, scope):
        self.scope = scope
        self.axioms = set()

    def visit_BinOp(self, node):
        self.generic_visit(node)

        # Disallow division by zero, in z3 divisions by zero are allowed as
        # the expressions are purely symbolic and not connected to a
        # specific value
        if isinstance(node.op, (ast.Div, ast.FloorDiv)):
            expr = eval_expr(node.right, self.scope)
            self.axioms.add(expr != 0)


def infere_axioms(tree, scope):
    axiom_finder = AxiomFinder(scope)
    axiom_finder.visit(tree)
    return axiom_finder.axioms


class ExprToSymbolic(ast.NodeTransformer):
    def visit_IfExp(self, node):
        self.generic_visit(node)

        _z3_If = ast.Name(id="_z3_If", ctx=ast.Load())
        args = [node.test, node.body, node.orelse]

        return ast.Call(_z3_If, args=args, keywords=[])

    def visit_BoolOp(self, node):
        self.generic_visit(node)

        id = '_z3_Or' if isinstance(node, ast.Or) else '_z3_And'
        name = ast.Name(id=id, ctx=ast.Load())

        return ast.Call(name, args=node.values[:],keywords=[])

    def visit_TupleOp(self, node):
        self.generic_visit(node)

        return ast.Call(
            ast.Name(id='Tuple'),
            args=[],
            keywords=[],
        )


class AssignExtendList(list):
    def __setattr__(self, name, value):
        if name == 'collect':
            self.extend(value)
        else:
            return super().__setattr__(name, value)


def execution_graph(function_body, scope, ret_val):
    Edge = namedtuple('Edge', ['constraint', 'axioms'])
    class 𝚲:
        @classmethod
        def visit(cls, node, mkedge):
            member = 'visit_' + node.__class__.__name__
            visitor = getattr(cls, member)
            return visitor(node, mkedge)

        @staticmethod
        def visit_body(body, mkedge):
            edges = AssignExtendList()
            for node in body:
                edges.collect, mkedge = 𝚲.visit(node, mkedge)
            return edges, mkedge

        @staticmethod
        def visit_Assign(node, mkedge):
            if len(node.targets) != 1:
                raise ValueError('Unpacking not supported')

            expr, infered_axioms = symbolic_result(node.value, scope)
            target = z3.Const(node.targets[0].id, expr.sort())

            constraint = target == expr
            _, edges, mkedge = mkedge(constraint, *infered_axioms)

            scope[node.targets[0].id] = expr

            return edges, mkedge

        @staticmethod
        def visit_AnnAssign(node, mkedge):
            target_sort = eval_expr(node.annotation, scope)
            target = z3.Const(node.target.id, target_sort.theory)
            expr, infered_axioms = symbolic_result(node.value, scope)

            if expr.sort() != target_sort.theory:
                target_str = str(target_sort.theory)
                expr_str = f'{expr.sort()}({expr})'
                msg = f'Type mismatch expected {target_str} got {expr_str}'
                raise TypeError(msg)

            constraint = target == expr
            _, edges, mkedge = mkedge(constraint, *infered_axioms)

            scope[node.target.id] = expr

            return edges, mkedge

        @staticmethod
        def visit_Return(node, mkedge):
            expr, infered_axioms = symbolic_result(node.value, scope)
            constraint = ret_val == expr
            _, edges, mkedge = mkedge(constraint, *infered_axioms)
            return edges, mkedge

        @staticmethod
        def visit_If(node, mkedge):
            edges = AssignExtendList()

            test, infered_axioms = symbolic_result(node.test, scope)
            not_test = z3.Not(test)
            _, edges.collect, mkedge_pos = mkedge(test, *infered_axioms)
            _, edges.collect, mkedge_neg = mkedge(not_test, *infered_axioms)

            edges.collect, mkedge_pos = 𝚲.visit_body(node.body, mkedge_pos)
            edges.collect, mkedge_neg = 𝚲.visit_body(node.orelse, mkedge_neg)

            def gather_edges(constraint, *axioms):
                E = AssignExtendList()
                out_node, E.collect, _ = mkedge_pos()
                _, E.collect, mknode = mkedge_neg(out_node=lambda: out_node)
                out_node, E.collect, mknode = mkedge(constraint, *axioms,
                                                     in_node=lambda: out_node)
                return out_node, E, mknode

            return edges, gather_edges

    scope = scope.copy()

    node_counter = count()
    def mkedge(constraint,
               *axioms,
               in_node=lambda _i=next(node_counter): _i,
               out_node=lambda: next(node_counter)):
        in_node = in_node()
        out_node = out_node()
        edges = [(in_node, out_node, Edge(constraint, axioms))]
        return out_node, edges, partial(mkedge, in_node=lambda: out_node)

    edges, _ = 𝚲.visit_body(function_body, mkedge)

    G = OrderedDict()
    for a, b, e in sorted(edges):
        G.setdefault(a, OrderedDict())[b] = e

    return G, scope


def symbolic_execution_graph(function, scope, ret_val):
    tree = function_ast(function)
    function_body = tree.body[0].body
    scope = {**function.__globals__, **scope}

    G, scope = execution_graph(function_body, scope, ret_val)

    edges = {a: {b: z3.Bool(f'E_{a}_{b}') for b in G[a]} for a in G}

    data_constraints = [
        z3.Implies(edges[a][b], G[a][b].constraint)
        for a in G
        for b in G[a]
    ]

    infered_axioms = [
        (edges[a][b], axiom)
        for a in G
        for b in G[a]
        for axiom in G[a][b].axioms
    ]

    # One of the initial branched must be true
    initial_branch = reduce(z3.Or, (edges[0][b] for b in edges[0]))
    control_flow = [initial_branch]
    for a in G:
        children = G[a]
        branching = len(children) != 1
        if branching:
            # If you we are branching, we can go down any of the branches.
            # Exclusivity is guaranteed from the data constrains on the edges.
            control_flow.append(reduce(z3.Or, (edges[a][b] for b in children)))
        for b in children:
            if b not in G:
                # If b is a leaf node, there are no constraints associated with
                # it.
                continue
            grand_children = G[b]
            for c in grand_children:
                control_flow.append(z3.Implies(edges[a][b], edges[b][c]))

    return control_flow, data_constraints, infered_axioms


def eval_expr(expr, scope):
    expr = ast.fix_missing_locations(expr)
    python_code = compile(ast.Expression(expr), '<ast>', 'eval')
    return eval(python_code, scope.copy())


def lambda_to_symbolic(λ):
    expr = lambda_ast(λ).body[0].value

    ExprToSymbolic().visit(expr)

    expr = ast.fix_missing_locations(ast.Expression(expr))
    code = compile(expr, '<ast>', 'eval')

    # Copy the globals so that the original scope isn't modified by this
    # execution
    return eval(code, λ.__globals__.copy())


def symbolic_result(expr, scope):
    return eval_expr(expr, scope), infere_axioms(expr, scope)
