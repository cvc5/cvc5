class Rule:
    def __init__(self, name, lhs, rhs):
        self.name = name
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return f"(define-rule {self.name} {self.lhs} {self.rhs})"
