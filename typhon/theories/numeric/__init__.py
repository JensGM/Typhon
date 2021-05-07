from ...core import RefinementType
import z3


Int = RefinementType('Int', z3.IntSort)
Real = RefinementType('Real', z3.RealSort)
