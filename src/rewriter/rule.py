class Rule:
    def __init__(self, name, bvars, cond, lhs, rhs, is_fixed_point):
        self.name = name
        self.bvars = bvars
        self.cond = cond
        self.lhs = lhs
        self.rhs = rhs
        self.is_fixed_point = is_fixed_point

    def get_enum(self):
        return self.name.replace('-', '_').upper()

    def __repr__(self):
        bvars_str = ' '.join(str(bvar) for bvar in bvars)
        return f"(define-rule {self.name} ({bvars_str}) {self.lhs} {self.rhs})"
