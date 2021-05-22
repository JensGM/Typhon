from .. import CounterExample
from .. import prove
from ..theories.collections import Tuple
from ..theories.maybe import Just
from ..theories.maybe import Maybe
from ..theories.maybe import Nothing
from ..theories.numeric import Int
from ..theories.numeric import Real
import pytest


def test_proof_basic():
    @prove
    def add(a : Real, b : Real) -> Real | (lambda v: v == a + b):
        v = a + b
        return v

    @prove
    def add_error(a : Real, b : Real) -> Real | (lambda v: v == a + b):
        v = a - b
        return v

    assert add.prove()
    with pytest.raises(CounterExample):
        add_error.prove()


def test_proof_basic_type_comment():
    @prove
    def add(a : Real, b : Real) -> Real | (lambda v: v == a + b):
        v: Real = a + b
        return v

    @prove
    def add_error(a : Real, b : Real) -> Real | (lambda v: v == a + b):
        v: Int = a + b
        return v

    assert add.prove()
    with pytest.raises(TypeError):
        add_error.prove()


def test_maybe():
    @prove
    def divide(a : Real, b : Real) -> Maybe[Real] | (
        lambda v: v == (Just(a / b) if b != 0 else Nothing[Real])
    ):
        if b != 0:
            x = a / b
            return Just(x)
        else:
            return Nothing[Real]

    @prove
    def divide_error(a : Real, b : Real) -> Real | (lambda v: v == a / b):
        return a / b

    assert divide.prove()
    with pytest.raises(CounterExample):
        divide_error.prove()
    assert False


def test_proof_complex():
    @verify
    def planar_windspeed(
        a0 : Real, a1 : Real, a2 : Real,
        b0 : Real, b1 : Real, b2 : Real,
        Ix : Real, Iy : Real, Iz : Real,
        R0 : Real, R1 : Real
    ) -> Maybe[Tuple[Real, Real]]:
        if a0 + b0 != 0 and a0 * b1 - b0 * a1 != 0:
            y = ( a0 * R1
                - b0 * R0
                + (a0 * b2 - b0 * a2) * Iz
                + (a0 * b1 - b0 * a1) * Iy) / (a0 * b1 - b0 * a1)
            x = ((R0
                + R1
                + (a2 + b2) * Iz
                - (a1 + b1) * (y - Iy)) / (a0 + b0)
                + Ix)
            return Just((x, y))
        else:
            return Nothing[Tuple[Real, Real]]

    @prove_that
    def planar_windspeed_solves_equation():
        with planar_windspeed(a0, a1, a2,
                              b0, b1, b2,
                              Ix, Iy, Iz,
                              R0, R1) as x, y:
            if a0 + b0 != 0 and a0 * b1 - b0 * a1 != 0:
                assert R0 == a0 * (x - ix) + a1 * (y - iy) - a2 * iz
                assert R1 == b0 * (x - ix) + b1 * (y - iy) - b2 * iz
            else:
                assert v == Nothing[Tuple[Real, Real]]

    assert planar_windspeed.verify()
    assert planar_windspeed_solves_equation()
