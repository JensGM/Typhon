from .symbolic_execution import lambda_to_symbolic
from .symbolic_execution import symbolic_execution_graph
from bs4 import BeautifulSoup
import inspect
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


def verify(function):
    solver = function.solver
    parameters, return_type = signature(function)

    scope = {
        **{
            name: p.assert_into(solver, name) for name, p in parameters.items()
        },
        '_z3_And': z3.And,
        '_z3_If': z3.If,
    }

    if return_type.refinement is not None:
        return_type.refinement.__globals__.update(scope) #??
    ret_val = return_type.declare('_ret_val')

    (control_flow, data_constraints, infered_axioms
    ) = symbolic_execution_graph(function, scope, ret_val)


    solver.add(*control_flow, *data_constraints)

    if solver.check() == z3.unsat:
        print(solver.to_smt2())
        raise ValueError(z3.unsat)

    tests = [(~return_type).refinement(ret_val)]
    tests.extend(
        z3.And(edge, z3.Implies(edge, z3.Not(axiom)))
        for edge, axiom in infered_axioms
    )
    for test in tests:
        z3.set_option(html_mode=True)
        print(BeautifulSoup(f'Checking {test} in \n{solver}',
                            features="html.parser"))

        contradiction = solver.check(test)
        if contradiction == z3.sat:
            raise CounterExample(solver.model())
        if contradiction == z3.unsat:
            pass
        else:
            raise Undecided()

    return True


def signature(function):
    signature = inspect.signature(function)

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

    return parameters, return_type
