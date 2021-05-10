from ...core import RefinementType
import z3


def _Tuple(*T, _cache={}):
    if T in _cache:
        return _cache[T]

    sorts = tuple(t.theory for t in T)

    print("TUPLE:", sorts)
    Tuple = z3.TupleSort(f'Tuple[{", ".join(s.name() for s in sorts)}]', sorts)
    _cache[T] = Tuple

    sort, constructor, accessors = Tuple
    return sort


Tuple = RefinementType('Tuple', _Tuple)
