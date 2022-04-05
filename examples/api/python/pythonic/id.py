from cvc5.pythonic import *

if __name__ == '__main__':
    A = Set("A", SetSort(IntSort()))
    B = Set("B", SetSort(IntSort()))
    C = Set("C", SetSort(IntSort()))

    assert A.get_id() != B.get_id()
    assert C.get_id() != B.get_id()
    assert A.get_id() == A.get_id()
    assert B.get_id() == B.get_id()
    assert C.get_id() == C.get_id()
