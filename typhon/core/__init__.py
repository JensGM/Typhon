import ast
import inspect
import textwrap
import types
import z3


class RefinementType:
    def __init__(self, theory, template_types=None, refinement=None):
        self.theory = theory
        self.template_types = template_types
        self.refinement = refinement

    def __getitem__(self, template_types):
        return self._replace(template_types=template_types)

    def __iter__(self):
        yield self
        raise StopIteration

    def __or__(self, refinement):
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

    def declare(self, name):
        return self.theory(name)

    def assert_into(self, solver, name):
        inst = self.declare(name)
        if self.refinement is not None:
            solver.add(self.refinement(inst))
        return inst



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
        name: p.assert_into(solver, name) for name, p in parameters.items()
    }

    return_type.refinement.__globals__.update(scope)
    ret_val = return_type.declare('_ret_val')

    function_body = tree.body[0].body

    class SymbolicExecution(ast.NodeVisitor):
        def __init__(self):
            self.assign_count = {}

        def symbolic_exec(self, expr):
            python_code = compile(ast.Expression(expr), '<ast>', 'eval')
            return eval(python_code, scope.copy())

        def visit_Assign(self, node):
            self.generic_visit(node)

            expr = self.symbolic_exec(node.value)
            target = z3.Const(node.targets[0].id, expr.sort())

            solver.add(target == expr)

            scope[node.targets[0].id] = target

            print(scope)

        def visit_Return(self, node):
            expr = self.symbolic_exec(node.value)
            solver.add(ret_val == expr)


    SymbolicExecution().visit(tree)

    try:
        solver.push()
        solver.add((~return_type).refinement(ret_val))

        print(solver.to_smt2())

        contradiction = solver.check()
        if contradiction == z3.sat:
            raise ValueError(f'Counter example {solver.model()}')
        if contradiction == z3.unsat:
            return True
        else:
            return False
    finally:
        solver.pop()

    raise ValueError('This statmement should be removed #refactor')
