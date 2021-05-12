import ast
import dis
import inspect
import io
import itertools
import string
import textwrap
import types
import z3


class CounterExample(Exception):
    def __init__(self, model):
        self.model = model
        super().__init__(repr(self.model))

    def __repr__(self):
        return f'Counter example {self.model}'


class Undecided(Exception):
    pass


class RefinementType:
    def __init__(self, name, theory, template_types=None, refinement=None):
        self._name = name
        self._theory = theory
        self.template_types = template_types
        self.refinement = refinement

    def __getitem__(self, template_types):
        return self._replace(template_types=template_types)

    def __iter__(self):
        yield self

    def __or__(self, refinement):
        refinement = lambda_to_symbolic(refinement)
        return self._replace(refinement=refinement)

    def __invert__(self):
        return self._replace(refinement=lambda v: z3.Not(self.refinement(v)))

    def _replace(self, **kwargs):
        """
        Replace the existing values of class attributes with new ones.
        Parameters
        ----------
        kwargs : dict
            keyword arguments corresponding to one or more attributes whose
            values are to be modified
        Returns
        -------
        A new CallNode with replaced attributes
        """
        attribs = {k: kwargs.pop(k, v) for k, v in vars(self).items()}
        if kwargs:
            raise ValueError(f'Got unexpected field names: {list(kwargs)!r}')
        inst = self.__class__.__new__(self.__class__)
        inst.__dict__.update(attribs)
        return inst

    @property
    def theory(self):
        if self.template_types is not None:
            return self._theory(*self.template_types)
        else:
            return self._theory()

    def name(self):
        return self._name

    def declare(self, name):
        return z3.Const(name, self.theory)

    def assert_into(self, solver, name):
        inst = self.declare(name)
        if self.refinement is not None:
            solver.add(self.refinement(inst))
        return inst

    def __repr__(self):
        r = self.name()
        if self.refinement is not None:
            r += f'| {self.refinement}'
        return r



def prove(function):

    def _prove(self):
        try:
            return self._proof
        except AttributeError:
            self._proof = verify(self)
            return self._proof
    function.solver = z3.Solver()
    function.prove = types.MethodType(_prove, function)
    return function


def function_source(func):
    """Function Source
    Get the source code of a function. Cannot be done on dynamically generated
    functions.
    Returns
    -------
    str
        Function source code
    """
    source = inspect.getsource(func)
    dedent = textwrap.dedent(source)
    return dedent


def function_ast(func):
    """Function AST
    Get an abstract syntax tree of a function
    Returns
    -------
    ast.Module
        Abstract syntax tree of the function
    """
    src = function_source(func)
    return ast.parse(src)


def lambda_ast(λ):
    """
    This is complicated.

    inspired by [1].

    .. [1] https://gist.github.com/Xion/617c1496ff45f3673a5692c3b0e3f75a
    """
    def explode(code):
        asm = io.StringIO()
        for inst in dis.get_instructions(code):
            if inst.opname == 'LOAD_CONST':
                print(inst.offset, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname == 'LOAD_FAST':
                print(inst.offset, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname == 'LOAD_GLOBAL':
                print(inst.offset, 'LOAD_GENERIC', inst.argval, file=asm)
            elif inst.opname == 'LOAD_NAME':
                print(inst.offset, 'LOAD_GENERIC', inst.argval, file=asm)
            else:
                print(inst.offset,
                      inst.opname,
                      inst.argval if inst.argval else inst.arg,
                      file=asm)
        asm.seek(0)
        return asm.read()



    source = function_source(λ)
    tree = ast.parse(source)

    Λ = [node for node in ast.walk(tree) if isinstance(node, ast.Lambda)]

    for λnode in Λ:
        λsrc = source[λnode.col_offset:]
        λsrc_body = source[λnode.body.col_offset:]

        # Sometimes python will give you the wrong col_offset if there are line
        # line breaks in lambdas.
        λsrc_body =  λsrc_body.lstrip(string.whitespace + ':')

        min_length = len('lambda:_')  # shortest possible lambda expression

        while len(λsrc) > min_length:
            try:
                code = compile(λsrc_body, '<ast>', 'eval')

                if explode(code) == explode(λ.__code__):
                    return ast.parse(λsrc)
            except SyntaxError:
                pass
            λsrc = λsrc[:-1]
            λsrc_body = λsrc_body[:-1]

    raise ValueError('Unable to extract lambda source code')


def verify(function):
    signature = inspect.signature(function)
    tree = function_ast(function)

    signature_is_refinement = all(
        isinstance(ann.annotation, RefinementType)
        for _, ann in signature.parameters.items()
    ) and isinstance(signature.return_annotation, RefinementType)

    if not signature_is_refinement:
        raise ValueError('signature_is_refinement')

    parameters = {
        name: p.annotation for name, p in signature.parameters.items()
    }

    return_type = signature.return_annotation

    solver = function.solver

    scope = {
        **{
            name: p.assert_into(solver, name) for name, p in parameters.items()
        },
        '_z3_And': z3.And,
        '_z3_If': z3.If,
    }

    if return_type.refinement is not None:
        return_type.refinement.__globals__.update(scope)
    ret_val = return_type.declare('_ret_val')

    # # Type:
    # #     divide(a : Real, b : Real) -> Maybe[Real] | (
    # #         lambda v: v == (Just(a / b) if b != 0 else Nothing[Real])
    # #     )
    # # Code:
    # #     if b != 0:
    # #         v = a / b
    # #         return Just(v)
    # #     else:
    # #         return Nothing[Real]
    # #
    # # Execution Graph:
    # #                        - [0]
    # #               b == 1  |   | b != 0
    # #                       |  [1]
    # #                       |   | v = a / b
    # #                       |  [2]
    # #                       |   | return Just(v)
    # #                      [3]  |
    # # return Nothing[Real]  |   |
    # #                        - [4]
    # #
    #
    # # Control flow
    # E_0_1, E_0_3, E_1_2, E_2_4, E_3_4 = Bools('E_0_1 E_0_3 E_1_2 E_2_4 E_3_4')
    # solver.add(Or(E_0_1, E_0_3))
    # solver.add(Implies(E_0_1, E_1_2))
    # solver.add(Implies(E_1_2, E_2_4))
    # solver.add(Implies(E_0_3, E_3_4))
    #
    # # Data constraints
    # solver.add(Implies(E_0_1, b != 0))
    # solver.add(Implies(E_0_4, b == 0))
    # solver.add(Implies(E_1_2, v == a / b))
    # solver.add(Implies(E_2_4, _ret_val == Just(v)))
    # solver.add(Implies(E_3_4, _ret_val == Nothing[Real]))
    #
    # # From the refinement type we have
    # #     _ret_val == (Just(a / b) if b != 0 else Nothing[Real])
    # # And an infered axiom that is
    # #     E_1_2 => b != 0
    # # If the solver is sat, but unsat if we add the inverse of any of these,
    # # the implementation is verified to our constraints.



    axioms = set()
    class SymbolicExecution(SymbolicExecutionTransformer):
        def __init__(self):
            self.assign_count = {}

        def symbolic_exec(self, expr):
            expr = ast.fix_missing_locations(expr)
            python_code = compile(ast.Expression(expr), '<ast>', 'eval')
            try:
                return eval(python_code, {**function.__globals__, **scope})
            except Exception:
                print('FAILED')
                print(ast.dump(expr))

                import astor
                print(astor.to_source(expr))

        def visit_Assign(self, node):
            self.generic_visit(node)

            expr = self.symbolic_exec(node.value)
            target = z3.Const(node.targets[0].id, expr.sort())

            solver.add(target == expr)
            scope[node.targets[0].id] = target

            return node

        def visit_AnnAssign(self, node):
            self.generic_visit(node)

            target_sort = self.symbolic_exec(node.annotation)
            target = z3.Const(node.target.id, target_sort.theory)
            expr = self.symbolic_exec(node.value)

            if expr.sort() != target_sort.theory:
                target_str = str(target_sort.theory)
                expr_str = f'{expr.sort()}({expr})'
                msg = f'Type mismatch expected {target_str} got {expr_str}'
                raise TypeError(msg)

            solver.add(target == expr)
            scope[node.target.id] = expr

            return node

        def visit_BinOp(self, node):
            self.generic_visit(node)

            # Disallow division by zero, in z3 divisions by zero are allowed as
            # the expressions are purely symbolic and not connected to a
            # specific value
            if isinstance(node.op, (ast.Div, ast.FloorDiv)):
                expr = self.symbolic_exec(node.right)
                axioms.add(expr != 0)

            return node

        def visit_Return(self, node):
            self.generic_visit(node)
            expr = self.symbolic_exec(node.value)
            solver.add(ret_val == expr)

            return node


    SymbolicExecution().visit(tree)

    requirements = []
    if return_type.refinement is not None:
        requirements.append(return_type.refinement(ret_val))
    requirements.extend(axioms)

    if solver.check() == z3.unsat:
        raise ValueError(z3.unsat)

    for formula in requirements:
        try:
            solver.push()

            solver.add(z3.Not(formula))

            print(formula, "::", solver.to_smt2())

            contradiction = solver.check()
            if contradiction == z3.sat:
                raise CounterExample(solver.model())
            if contradiction == z3.unsat:
                pass
            else:
                raise Undecided()
        finally:
            solver.pop()

    return True


class SymbolicExecutionTransformer(ast.NodeTransformer):
    def visit_IfExp(self, node):
        self.generic_visit(node)

        return ast.Call(
            ast.Name(id="_z3_If", ctx=ast.Load()),
            args=[
                node.test,
                node.body,
                node.orelse,
            ],
            keywords=[],
        )

    def visit_BoolOp(self, node):
        self.generic_visit(node)

        return ast.Call(
            ast.Name(id="_z3_And", ctx=ast.Load()),
            args=list(node.values),
            keywords=[],
        )

    def visit_TupleOp(self, node):
        self.generic_visit(node)

        return ast.Call(
            ast.Name(id='Tuple')
        )


def lambda_to_symbolic(λ):
    expr = lambda_ast(λ).body[0].value

    SymbolicExecutionTransformer().visit(expr)

    expr = ast.fix_missing_locations(ast.Expression(expr))
    code = compile(expr, '<ast>', 'eval')
    return eval(code, λ.__globals__.copy())
