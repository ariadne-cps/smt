from pyariadne import *



def test_smt():
    x = RealVariable("x")
    space = RealSpace([x])
    domain = FloatDPExactBox([
        {exact(-1): exact(1)},
    ])
    solver = SmtSolver(SmtSolverConfiguration(exact(0.125)))
    result = solver.solve(space, domain, RealExpression(x) > 0)
    assert result.is_epsilon_sat()


def test_transitive_cdcl_python_bindings():
    # The generated entry point registers CDCL even when SMT is the top-level
    # project. All module objects must be linked into the same extension.
    positive = BooleanLiteral(0)
    assert positive.variable() == 0
    assert positive.dimacs() == 1
    assert positive.negation().dimacs() == -1

    outcome = CdclTheoryFeedback.unknown()
    assert outcome.status() == CdclTheoryStatus.UNKNOWN
