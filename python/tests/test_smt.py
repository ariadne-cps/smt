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
