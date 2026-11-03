/***************************************************************************
 *            test_smt_neural_benchmarks.cpp
 *
 *  Copyright  2026  Luca Geretti
 *
 ****************************************************************************/

/*
 *  This file is part of Ariadne.
 *
 *  Ariadne is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Ariadne is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with Ariadne.  If not, see <https://www.gnu.org/licenses/>.
 */

/*! \file test_smt_neural_benchmarks.cpp
 *  \brief Ariadne SMT benchmark.
 */

/***************************************************************************
 *            test_smt_neural_benchmarks.cpp
 *
 *  Fast regression smoke test for the published Barr3 neural barrier.
 *  Performance and scaling measurements live in benchmark_smt_barr3_verification.
 ***************************************************************************/

#include <iostream>
#include <limits>

#include "smt/smt_solver.hpp"

#include "smt_barr3_full64.hpp"

#include "ariadne-testing.hpp"

using namespace Ariadne;

class TestSmtNeuralBenchmarks : public Ariadne::Testing::ContextFixture {
  public:
    using ContextFixture::ContextFixture;

  public:
    Void test_barr3_full64_smoke() {
        ARIADNE_TESTING_NOTE("=== SMT neural regression: published Barr3 2-64-64-1 ===");

        RealVariable bx("barr3_64_x"), by("barr3_64_y");
        RealExpression ebx=bx, eby=by;
        RealSpace space({bx,by});
        RealExpression barrier=TestBarr3Full64::network(ebx,eby);

        auto barrier_function=make_function(space,barrier);
        UpperBoxType origin=ExactBoxType({
            ExactIntervalType(0.0_x,0.0_x),
            ExactIntervalType(0.0_x,0.0_x)
        });
        UpperIntervalType origin_image=apply(barrier_function,origin);
        ARIADNE_TESTING_PROVE(definitely(subset(
            origin_image,
            ExactIntervalType(3.809_pr,3.810_pr))));

        auto alternatives=normalize_smt_theory_literal(
            make_smt_theory_literal(barrier==0));
        ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
        ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);

        List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
        ExactBoxType barr3_domain({
            ExactIntervalType(-3.0_x,2.5_x),
            ExactIntervalType(-2.0_x,1.0_x)
        });
        SmtSolver solver(SmtSolverConfiguration(
            0.01_pr,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            1u,
            false,
            false,
            false,
            false,
            false,
            false));

        SmtResult solve_result=solver.solve(space,barr3_domain,literals);

        ARIADNE_TESTING_PROVE(solve_result.is_unknown());
        ARIADNE_TESTING_EXPECT_EQUAL(
            solve_result.unknown_reason(),SmtUnknownReason::RESOURCE_EXHAUSTED);
        ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(
            solve_result.statistics().fused_direct_classification_boxes,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(
            solve_result.statistics().sensitivity_guided_splits,0u);
    }

};

int main(int argc, char** argv) {
    ARIADNE_TESTING_SUITE("test_smt_neural_benchmarks");
    ARIADNE_TESTING_ADD_TEST(TestSmtNeuralBenchmarks, test_barr3_full64_smoke);
    return ARIADNE_TESTING_RUN_TESTS_WITH_ARGS(argc, argv);
}
