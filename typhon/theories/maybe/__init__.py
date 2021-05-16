from ...core import RefinementType
import z3


def _Maybe(T, _cache={}):
    if T in _cache:
        return _cache[T]

    try:
        T = T.theory
    except AttributeError:
        pass
    Maybe = z3.Datatype(f'Maybe[{T.name()}]')
    Maybe.declare('Just', ('just', T))
    Maybe.declare('Nothing')

    _cache[T] = Maybe.create()
    return _cache[T]


Maybe = RefinementType('Maybe', _Maybe)


Just = type('Just', (), {
    '__getitem__': lambda self, T: _Maybe(T).Just,
    '__call__': lambda self, expr: _Maybe(expr.sort()).Just(expr)
})()

Nothing = type('Nothing', (), {
    '__getitem__': lambda self, T: _Maybe(T).Nothing,
})()
