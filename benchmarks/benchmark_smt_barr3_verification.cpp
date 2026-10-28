/***************************************************************************
 *            benchmark_smt_barr3_verification.cpp
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

/*! \file benchmark_smt_barr3_verification.cpp
 *  \brief Ariadne SMT benchmark.
 */

/***************************************************************************
 * benchmark_smt_barr3_verification.cpp
 *
 * Standalone reproduction of the published FOSSIL/dReal Barr3 BarrierAlt
 * counterexample queries using Ariadne's epsilon-SMT solver.
 ***************************************************************************/

#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>

#include "utility/stopwatch.hpp"
#include "smt/smt_solver.hpp"
#include "smt_barr3_full64.hpp"

using namespace Ariadne;

namespace {
SizeType box_limit_from_argument(Int argc,const char* argv[]) {
    if(argc<=1) { return 1u; }
    String argument(argv[1]);
    if(argument=="full") {
        return std::numeric_limits<SizeType>::max();
    }
    char* end=nullptr;
    unsigned long long parsed=std::strtoull(argv[1],&end,10);
    if(end==argv[1] || *end!='\0' || parsed==0u) {
        throw std::runtime_error(
            "Usage: benchmark_smt_barr3_verification [positive-box-limit|full]");
    }
    return static_cast<SizeType>(parsed);
}


String query_from_argument(Int argc,const char* argv[]) {
    if(argc<=6) { return "all"; }
    String argument(argv[6]);
    if(argument=="all" || argument=="lie" || argument=="lie-only") {
        return argument;
    }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification ... [all|lie|lie-only]");
}
Bool monotone_from_argument(Int argc,const char* argv[]) {
    if(argc<=7) { return false; }
    String argument(argv[7]);
    if(argument=="monotone") { return true; }
    if(argument=="no-monotone") { return false; }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification "
        "[positive-box-limit|full] [sensitivity|geometric|lookahead] "
        "[witness|no-witness] [shaving|no-shaving] [hull|no-hull] "
        "[all|lie|lie-only] [monotone|no-monotone] [barrier-first|lie-first] [lower-first|upper-first]");
}

String lie_literal_order_from_argument(Int argc,const char* argv[]) {
    if(argc<=8) { return "barrier-first"; }
    String argument(argv[8]);
    if(argument=="barrier-first" || argument=="lie-first") { return argument; }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification "
        "[positive-box-limit|full] [sensitivity|geometric|lookahead] "
        "[witness|no-witness] [shaving|no-shaving] [hull|no-hull] "
        "[all|lie|lie-only] [monotone|no-monotone] [barrier-first|lie-first] [lower-first|upper-first]");
}

String child_order_from_argument(Int argc,const char* argv[]) {
    if(argc<=9) { return "lower-first"; }
    String argument(argv[9]);
    if(argument=="lower-first" || argument=="upper-first") { return argument; }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification "
        "[positive-box-limit|full] [sensitivity|geometric|lookahead] "
        "[witness|no-witness] [shaving|no-shaving] [hull|no-hull] "
        "[all|lie|lie-only] [monotone|no-monotone] [barrier-first|lie-first] [lower-first|upper-first]");
}

String preclassification_mode_from_argument(Int argc,const char* argv[]) {
    if(argc<=10) { return "no-preclassify"; }
    String argument(argv[10]);
    if(argument=="preclassify"
       || argument=="adaptive-preclassify"
       || argument=="no-preclassify") {
        return argument;
    }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification ... "
        "[lower-first|upper-first] "
        "[preclassify|adaptive-preclassify|no-preclassify]");
}

Bool hull_from_argument(Int argc,const char* argv[]) {
    if(argc<=5) { return true; }
    String argument(argv[5]);
    if(argument=="hull") { return true; }
    if(argument=="no-hull") { return false; }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification "
        "[positive-box-limit|full] [sensitivity|geometric|lookahead] "
        "[witness|no-witness] [shaving|no-shaving] [hull|no-hull]");
}

Bool shaving_from_argument(Int argc,const char* argv[]) {
    if(argc<=4) { return true; }
    String argument(argv[4]);
    if(argument=="shaving") { return true; }
    if(argument=="no-shaving") { return false; }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification "
        "[positive-box-limit|full] [sensitivity|geometric|lookahead] "
        "[witness|no-witness] [shaving|no-shaving]");
}

Bool witness_probing_from_argument(Int argc,const char* argv[]) {
    if(argc<=3) { return true; }
    String argument(argv[3]);
    if(argument=="witness") { return true; }
    if(argument=="no-witness") { return false; }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification "
        "[positive-box-limit|full] [sensitivity|geometric|lookahead] "
        "[witness|no-witness]");
}

String split_policy_from_argument(Int argc,const char* argv[]) {
    if(argc<=2) { return "sensitivity"; }
    String argument(argv[2]);
    if(argument=="sensitivity" || argument=="geometric" || argument=="lookahead") {
        return argument;
    }
    throw std::runtime_error(
        "Usage: benchmark_smt_barr3_verification "
        "[positive-box-limit|full] [sensitivity|geometric|lookahead]");
}

SmtTheoryPrimitiveLiteral primitive(ContinuousPredicate const& predicate) {
    auto alternatives=normalize_smt_theory_literal(
        make_smt_theory_literal(predicate));
    if(alternatives.size()!=1u || alternatives[0].size()!=1u) {
        throw std::runtime_error("Expected one primitive SMT literal");
    }
    return alternatives[0][0];
}

Void print_result(String const& name,SmtResult const& result,double seconds) {
    std::cout << "[" << name << "] status=" << result.status();
    if(result.is_unknown()) {
        std::cout << " reason=" << result.unknown_reason();
    }
    std::cout << " time=" << seconds << " s"
              << " boxes=" << result.statistics().boxes_processed
              << " pruned=" << result.statistics().boxes_pruned
              << " split=" << result.statistics().boxes_split
              << " epsilon-certified=" << result.statistics().epsilon_box_certifications
              << " fused-direct=" << result.statistics().fused_direct_classification_boxes
              << " fused-literal-evals="
              << result.statistics().fused_direct_literal_evaluations
              << " preclass-boxes="
              << result.statistics().preclassification_boxes
              << " preclass-pruned="
              << result.statistics().preclassification_pruned_boxes
              << " preclass-epsilon="
              << result.statistics().preclassification_epsilon_boxes
              << " preclass-literal-evals="
              << result.statistics().preclassification_literal_evaluations
              << " preclass-time="
              << result.statistics().preclassification_seconds
              << " adaptive-skipped="
              << result.statistics().preclassification_adaptive_skipped_boxes
              << " adaptive-suspensions="
              << result.statistics().preclassification_adaptive_suspensions
              << " adaptive-reactivations="
              << result.statistics().preclassification_adaptive_reactivations
              << " candidate-searches=" << result.statistics().candidate_witness_searches
              << " candidate-successes=" << result.statistics().candidate_witness_successes
              << " hull-rounds=" << result.statistics().hull_reduction_rounds
              << " hull-effective=" << result.statistics().hull_effective_reductions
              << " hull-procedure-builds=" << result.statistics().hull_procedure_builds
              << " hull-procedure-build-time="
              << result.statistics().hull_procedure_build_seconds
              << " hull-contract-time=" << result.statistics().hull_contraction_seconds
              << " hull-reject-time="
              << result.statistics().hull_direct_rejection_seconds
              << " hull-temp-time="
              << result.statistics().hull_temporary_allocation_seconds
              << " hull-forward-time="
              << result.statistics().hull_forward_execution_seconds
              << " hull-backward-time="
              << result.statistics().hull_backward_propagation_seconds
              << " shaving-rounds=" << result.statistics().shaving_reduction_rounds
              << " shaving-effective=" << result.statistics().shaving_effective_reductions
              << " shaving-attempts=" << result.statistics().shaving_coordinate_attempts
              << " shaving-effective-attempts="
              << result.statistics().shaving_coordinate_effective
              << " shaving-dependency-skipped="
              << result.statistics().shaving_dependency_skipped
              << " shaving-adaptive-skipped="
              << result.statistics().shaving_adaptive_skipped
              << " shaving-refresh-rounds="
              << result.statistics().shaving_refresh_rounds
              << " shaving-active-rounds="
              << result.statistics().shaving_active_rounds
              << " shaving-evals=" << result.statistics().shaving_function_evaluations
              << " shaving-time=" << result.statistics().shaving_seconds
              << " monotone-rounds=" << result.statistics().monotone_reduction_rounds
              << " monotone-effective=" << result.statistics().monotone_effective_reductions
              << " sensitivity-splits=" << result.statistics().sensitivity_guided_splits
              << " sensitivity-overrides="
              << result.statistics().sensitivity_overrides_geometric_splits
              << " compile=" << result.statistics().theory_compile_seconds
              << " reduce=" << result.statistics().reduction_seconds
              << " epsilon=" << result.statistics().epsilon_check_seconds
              << " witness=" << result.statistics().witness_probe_seconds
              << " split-phase=" << result.statistics().split_seconds
              << " sensitivity-builds=" << result.statistics().sensitivity_derivatives_built
              << " sensitivity-evals=" << result.statistics().sensitivity_derivative_evaluations
              << " sensitivity-build-time="
              << result.statistics().sensitivity_derivative_build_seconds
              << " sensitivity-eval-time="
              << result.statistics().sensitivity_derivative_evaluation_seconds
              << " lookahead-splits="
              << result.statistics().interval_lookahead_guided_splits
              << " lookahead-overrides="
              << result.statistics().interval_lookahead_overrides_geometric_splits
              << " lookahead-evals="
              << result.statistics().interval_lookahead_function_evaluations
              << " lookahead-eval-time="
              << result.statistics().interval_lookahead_evaluation_seconds
              << " candidate=" << result.statistics().candidate_search_seconds
              << std::endl;
    if(not result.statistics().preclassification_outcomes.empty()) {
        std::cout << "[" << name << "] preclass-trace=";
        for(auto const outcome:result.statistics().preclassification_outcomes) {
            switch(outcome) {
                case SmtPreclassificationOutcome::PRUNED:
                    std::cout << 'P';
                    break;
                case SmtPreclassificationOutcome::EPSILON_SAT:
                    std::cout << 'E';
                    break;
                case SmtPreclassificationOutcome::UNRESOLVED:
                    std::cout << 'U';
                    break;
                default:
                    std::cout << '?';
                    break;
            }
        }
        std::cout << " (P=pruned,E=epsilon,U=unresolved)" << std::endl;
        if(result.statistics().preclassification_adaptive_skipped_boxes==0u) {
            auto const shadow=SmtSolverTestSupport::preclassification_shadow_summary(
                result.statistics().preclassification_outcomes);
            std::cout << "[" << name << "] preclass-shadow"
                      << " initial-window=16 active-window=8 refresh-period=8"
                      << " checks=" << shadow.checks
                      << " skipped=" << shadow.skipped
                      << " observed-hits=" << shadow.observed_hits
                      << " skipped-hits=" << shadow.skipped_hits
                      << " suspensions=" << shadow.suspensions
                      << " reactivations=" << shadow.reactivations
                      << std::endl;
        }
    }
}
SmtResult timed_solve(
    String const& name,
    SmtSolver const& solver,
    RealSpace const& space,
    ExactBoxType const& domain,
    List<SmtTheoryPrimitiveLiteral> const& literals)
{
    std::cout << "[start] " << name
              << " literals=" << literals.size() << std::endl << std::flush;
    Stopwatch<Milliseconds> stopwatch;
    SmtResult result=solver.solve(space,domain,literals);
    stopwatch.click();
    print_result(name,result,stopwatch.elapsed_seconds());
    return result;
}


} // namespace

Int main(Int argc,const char* argv[]) {
    SizeType const box_limit=box_limit_from_argument(argc,argv);
    String const split_policy=split_policy_from_argument(argc,argv);
    Bool const sensitivity_enabled=split_policy=="sensitivity";
    Bool const lookahead_enabled=split_policy=="lookahead";
    Bool const witness_probing_enabled=witness_probing_from_argument(argc,argv);
    Bool const shaving_enabled=shaving_from_argument(argc,argv);
    Bool const hull_enabled=hull_from_argument(argc,argv);
    String const query=query_from_argument(argc,argv);
    Bool const monotone_enabled=monotone_from_argument(argc,argv);
    String const lie_literal_order=lie_literal_order_from_argument(argc,argv);
    String const child_order=child_order_from_argument(argc,argv);
    Bool const upper_child_first=child_order=="upper-first";
    String const preclassification_mode=
        preclassification_mode_from_argument(argc,argv);
    Bool const preclassification_enabled=
        preclassification_mode!="no-preclassify";
    Bool const adaptive_preclassification_enabled=
        preclassification_mode=="adaptive-preclassify";

    std::cout << "=== Published Barr3 2-64-64-1 verification ===" << std::endl;
    std::cout << "epsilon=1e-5 box-limit=";
    if(box_limit==std::numeric_limits<SizeType>::max()) {
        std::cout << "unlimited";
    } else {
        std::cout << box_limit;
    }
    std::cout << " split-policy=" << split_policy
              << " witness-probing="
              << (witness_probing_enabled ? "enabled" : "disabled")
              << " shaving="
              << (shaving_enabled ? "enabled" : "disabled")
              << " hull="
              << (hull_enabled ? "enabled" : "disabled")
              << " query=" << query
              << " monotone="
              << (monotone_enabled ? "enabled" : "disabled")
              << " lie-literal-order=" << lie_literal_order
              << " child-order=" << child_order
              << " preclassification=" << preclassification_mode
              << std::endl;

    RealVariable x("barr3_x"), y("barr3_y");
    RealExpression ex=x, ey=y;
    RealSpace space({x,y});
    ExactBoxType domain({
        ExactIntervalType(-3.0_x,2.5_x),
        ExactIntervalType(-2.0_x,1.0_x)
    });

    Stopwatch<Milliseconds> construction_stopwatch;
    auto network=TestBarr3Full64::network_and_lie(ex,ey);
    construction_stopwatch.click();
    std::cout << "[construction] network+Lie="
              << construction_stopwatch.elapsed_seconds() << " s" << std::endl;

    // For diagnosis and performance, use direct primitive conjunctions rather
    // than routing the unsafe union through DPLL(T). The decomposition is
    // logically exact: XU is the union of these three components, so the
    // unsafe obligation is UNSAT iff all three component queries are UNSAT.
    //
    // Rectangle membership is encoded directly in each query domain. The
    // spherical component uses its tight bounding box plus the sphere literal.
    ExactBoxType unsafe_sphere_domain({
        ExactIntervalType(-1.4_x,-0.6_x),
        ExactIntervalType(-1.4_x,-0.6_x)
    });
    ExactBoxType unsafe_rectangle_1_domain({
        ExactIntervalType(0.4_x,0.6_x),
        ExactIntervalType(0.1_x,0.5_x)
    });
    ExactBoxType unsafe_rectangle_2_domain({
        ExactIntervalType(0.4_x,0.8_x),
        ExactIntervalType(0.1_x,0.3_x)
    });

    RealExpression sphere_value=(ex+1)*(ex+1)+(ey+1)*(ey+1);
    SmtTheoryPrimitiveLiteral barrier_nonnegative=
        primitive(network.barrier>=0);
    SmtTheoryPrimitiveLiteral sphere_inside=
        primitive(sphere_value<=0.16_x);
    SmtTheoryPrimitiveLiteral lie_violation=
        primitive((network.lie+network.barrier)<0);


    // First isolate the cost of validated box processing. Candidate search and
    // derivative-assisted monotone contraction are deliberately disabled here:
    // the previous version enabled both and a nominal one-box run could spend
    // an unbounded amount of wall time inside the per-box nonlinear candidate
    // optimiser / derivative contractors before the box budget was observed.
    SmtSolver solver(SmtSolverConfiguration(
        0.00001_x,
        std::numeric_limits<SizeType>::max(),
        std::numeric_limits<SizeType>::max(),
        box_limit,
        false,
        monotone_enabled,
        sensitivity_enabled,
        witness_probing_enabled,
        shaving_enabled,
        hull_enabled,
        lookahead_enabled,
        upper_child_first,
        false,
        preclassification_enabled,
        adaptive_preclassification_enabled));

    List<SmtTheoryPrimitiveLiteral> sphere_literals({
        sphere_inside,barrier_nonnegative});
    List<SmtTheoryPrimitiveLiteral> barrier_literals({
        barrier_nonnegative});
    List<SmtTheoryPrimitiveLiteral> lie_literals;
    if(lie_literal_order=="lie-first") {
        lie_literals.append(lie_violation);
        lie_literals.append(barrier_nonnegative);
    } else {
        lie_literals.append(barrier_nonnegative);
        lie_literals.append(lie_violation);
    }

    if(query=="all") {
        timed_solve(
            "unsafe-sphere",solver,space,unsafe_sphere_domain,sphere_literals);
        timed_solve(
            "unsafe-rectangle-1",solver,space,
            unsafe_rectangle_1_domain,barrier_literals);
        timed_solve(
            "unsafe-rectangle-2",solver,space,
            unsafe_rectangle_2_domain,barrier_literals);
    }
    if(query=="lie-only") {
        List<SmtTheoryPrimitiveLiteral> lie_only_literals({lie_violation});
        timed_solve(
            "lie-only",solver,space,domain,lie_only_literals);
    } else {
        timed_solve(
            "lie",solver,space,domain,lie_literals);
    }

    return 0;
}
