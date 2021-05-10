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
    def add_error(a : Real, b : Real) -> Real | (lambda v: v == a - b):
        v: Int = a + b
        return v

    assert add.prove()
    with pytest.raises(CounterExample):
        add_error.prove()


def test_maybe():
    @prove
    def divide(a : Real, b : Real) -> Maybe[Real] | (
        lambda v: v == (Just(a / b) if b != 0 else Nothing[Real])
    ):
        if b != 0:
            return Just(a / b)
        else:
            return Nothing[Real]

    @prove
    def divide_error(a : Real, b : Real) -> Real | (
        lambda v: v == a / b
    ):
        return a / b

    assert divide.prove()
    with pytest.raises(CounterExample):
        divide_error.prove()


def test_proof_complex():
    @prove
    def planar_windspeed(
        a0 : Real, a1 : Real, a2 : Real,
        b0 : Real, b1 : Real, b2 : Real,
        Ix : Real, Iy : Real, Iz : Real,
        R0 : Real, R1 : Real
    ) -> Maybe[Tuple[Real, Real]] | (
        lambda v: (
                R0 == a0 * (v[0] - ix) + a1 * (v[1] - iy) - a2 * iz and
                R1 == b0 * (v[0] - ix) + b1 * (v[1] - iy) - b2 * iz
            if a0 + b0 != 0 and a0 * b1 - b0 * a1 != 0
            else
                v == Nothing
        )
    ):
        y = (a0 * R1 - b0 * R0 + (a0 * b2 - b0 * a2) * Iz +
                                 (a0 * b1 - b0 * a1) * Iy) / (a0 * b1 - b0 * a1)
        x = (R0 + R1 + (a2 + b2) * Iz - (a1 + b1) * (y - Iy)) / (a0 + b0) + Ix
        return Just((x, y)) if a0 + b0 != 0 and a0 * b1 - b0 * a1 != 0 else Nothing

    assert planar_windspeed.prove()
