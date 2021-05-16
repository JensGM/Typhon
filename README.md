# Typhon
Refinement types for python


## Example

```python
from typhon import prove
from typhon.theories.numeric import Real
from typhon.theories.maybe import Maybe, Just, Nothing

@prove
def divide(a : Real, b : Real) -> Real | (lambda v: v == a / b):
    return a / b

divide.prove() # -> CounterExample

@prove
def divide(a : Real, b : Real) -> Maybe[Real] | (
    lambda v: v == (Just(a / b) if b != 0 else Nothing[Real])
):
    if b != 0:
        v = a / b
        return Just(v)
    else:
        return Nothing[Real]

divide.prove() # -> OK
```
