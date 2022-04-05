from cvc5.pythonic import *

if __name__ == '__main__':
    s = Solver()
    s.set("produce-models", True)
    try:
        # invalid option
        s.set("non-existing-option", True)
    except:
        pass

    try:
        # type error
        Int("x") + BitVec("a", 5)
    except:
        pass

    s += BoolVal(False)
    s.check()
    try:
        s.model()
    except:
        pass
