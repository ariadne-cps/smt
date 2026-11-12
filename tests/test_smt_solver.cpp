/***************************************************************************
 *            test_smt_solver.cpp
 *
 *  Copyright  2026  Luca Geretti
 *
 ****************************************************************************/

/*
 *  This file is part of Ariadne SMT.
 *
 *  Ariadne SMT is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Ariadne SMT is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with Ariadne SMT.  If not, see <https://www.gnu.org/licenses/>.
 */

/** @file tests/test_smt_solver.cpp
 *  @brief Test bounded real epsilon-SMT solver results and invariants.
 */

#include <sstream>

#include "smt/smt_solver.hpp"
#include "threading/thread_manager.hpp"

#include "ariadne-testing.hpp"

using namespace Ariadne;

class ConcurrencyGuard {
  public:
    explicit ConcurrencyGuard(ThreadManager& thread_manager)
        : _thread_manager(thread_manager), _original(thread_manager.concurrency()) { }

    ~ConcurrencyGuard() { _thread_manager.set_concurrency(_original); }

  private:
    ThreadManager& _thread_manager;
    SizeType _original;
};

class TestSmtSolver : public Ariadne::Testing::ContextFixture {
  public:
    using ContextFixture::ContextFixture;

  public:
    Void test_configuration() {
        ARIADNE_TESTING_NOTE("[smt-config] positive epsilon=0.125");
        SmtSolverConfiguration configuration(0.125_x);
        ARIADNE_TESTING_EXPECT_EQUAL(configuration.epsilon(),0.125_x);
        ARIADNE_TESTING_EXPECT_EQUAL(
            configuration.theory_minimization_budget(),
            std::numeric_limits<SizeType>::max());

        ARIADNE_TESTING_NOTE("[smt-config] bounded theory minimization budget=1");
        SmtSolverConfiguration bounded_configuration(0.125_x,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(bounded_configuration.theory_minimization_budget(),1u);
        ARIADNE_TESTING_EXPECT_EQUAL(
            bounded_configuration.learned_clause_limit(),
            std::numeric_limits<SizeType>::max());

        ARIADNE_TESTING_NOTE("[smt-config] learned clause limit=1");
        SmtSolverConfiguration pruning_configuration(
            0.125_x,std::numeric_limits<SizeType>::max(),1u);
        ARIADNE_TESTING_EXPECT_EQUAL(pruning_configuration.learned_clause_limit(),1u);

        ARIADNE_TESTING_NOTE("[smt-config] box processing limit=0");
        SmtSolverConfiguration bounded_search_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            0u);
        ARIADNE_TESTING_EXPECT_EQUAL(bounded_search_configuration.box_processing_limit(),0u);
        ARIADNE_TESTING_PROVE(bounded_search_configuration.candidate_search_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] disable candidate witness search");
        SmtSolverConfiguration no_candidate_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false);
        ARIADNE_TESTING_PROVE(not no_candidate_configuration.candidate_search_enabled());
        ARIADNE_TESTING_PROVE(not configuration.monotone_reduction_enabled());
        ARIADNE_TESTING_PROVE(configuration.sensitivity_split_enabled());
        ARIADNE_TESTING_PROVE(not configuration.interval_lookahead_split_enabled());
        ARIADNE_TESTING_PROVE(not configuration.upper_child_first());
        ARIADNE_TESTING_PROVE(configuration.deterministic_witness_probing_enabled());
        ARIADNE_TESTING_PROVE(configuration.shaving_reduction_enabled());
        ARIADNE_TESTING_PROVE(configuration.hull_reduction_enabled());
        ARIADNE_TESTING_NOTE("[smt-config] enable monotone reduction");
        SmtSolverConfiguration monotone_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            true,
            true);
        ARIADNE_TESTING_PROVE(monotone_configuration.monotone_reduction_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] disable sensitivity splitting");
        SmtSolverConfiguration geometric_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            true,
            false,
            false);
        ARIADNE_TESTING_PROVE(not geometric_configuration.sensitivity_split_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] disable deterministic witness probing");
        SmtSolverConfiguration no_witness_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            true,
            false,
            true,
            false);
        ARIADNE_TESTING_PROVE(
            not no_witness_configuration.deterministic_witness_probing_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] disable shaving reduction");
        SmtSolverConfiguration no_shaving_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            true,
            false,
            true,
            true,
            false);
        ARIADNE_TESTING_PROVE(not no_shaving_configuration.shaving_reduction_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] disable hull reduction");
        SmtSolverConfiguration no_hull_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            true,
            false,
            true,
            true,
            true,
            false);
        ARIADNE_TESTING_PROVE(not no_hull_configuration.hull_reduction_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] enable interval lookahead splitting");
        SmtSolverConfiguration lookahead_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,
            false,
            false,
            false,
            false,
            false,
            true);
        ARIADNE_TESTING_PROVE(
            lookahead_configuration.interval_lookahead_split_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] enable upper child first");
        SmtSolverConfiguration upper_first_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            true);
        ARIADNE_TESTING_PROVE(upper_first_configuration.upper_child_first());

        ARIADNE_TESTING_NOTE("[smt-config] enable interval Newton reduction");
        SmtSolverConfiguration interval_newton_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            true);
        ARIADNE_TESTING_PROVE(
            interval_newton_configuration.interval_newton_reduction_enabled());
        ARIADNE_TESTING_PROVE(
            not configuration.interval_newton_reduction_enabled());
        ARIADNE_TESTING_PROVE(not configuration.preclassification_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] enable contractor preclassification");
        SmtSolverConfiguration preclassification_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,
            false,
            false,
            false,
            false,
            true,
            false,
            false,
            false,
            true);
        ARIADNE_TESTING_PROVE(
            preclassification_configuration.preclassification_enabled());
        ARIADNE_TESTING_PROVE(
            not preclassification_configuration.adaptive_preclassification_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] enable adaptive contractor preclassification");
        SmtSolverConfiguration adaptive_preclassification_configuration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,
            false,
            false,
            false,
            false,
            true,
            false,
            false,
            false,
            true,
            true);
        ARIADNE_TESTING_PROVE(
            adaptive_preclassification_configuration.preclassification_enabled());
        ARIADNE_TESTING_PROVE(
            adaptive_preclassification_configuration.adaptive_preclassification_enabled());

        ARIADNE_TESTING_NOTE("[smt-config] reject adaptive preclassification without preclassification");
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false,false,false,false,false,true,false,false,false,false,true));

        ARIADNE_TESTING_NOTE("[smt-config] reject zero epsilon");
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverConfiguration(0.0_x));

        ARIADNE_TESTING_NOTE("[smt-config] reject negative epsilon=-0.125");
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverConfiguration(-0.125_x));
    }

    Void test_public_preconditions() {
        ARIADNE_TESTING_NOTE("[smt-preconditions] reject invalid public inputs");

        SmtSolver solver(SmtSolverConfiguration(0.125_x));
        ExactBoxType bounded({ExactIntervalType(0,1)});
        ExactBoxType unbounded({ExactIntervalType(-inf,inf)});

        auto x1=ValidatedScalarMultivariateFunction::coordinates(1);
        auto x2=ValidatedScalarMultivariateFunction::coordinates(2);
        List<ValidatedConstraint> one_dimensional({
            ValidatedConstraint(
                ValidatedNumber(0),x1[0],ValidatedNumber(1))
        });
        List<ValidatedConstraint> two_dimensional({
            ValidatedConstraint(
                ValidatedNumber(0),x2[0],ValidatedNumber(1))
        });

        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve(unbounded,one_dimensional));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve(bounded,two_dimensional));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve_parallel(unbounded,one_dimensional));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve_parallel(bounded,two_dimensional));

        RealVariable x("precondition_x"), y("precondition_y");
        RealExpression ex=x;
        RealSpace one_space({x});
        RealSpace two_space({x,y});
        List<SmtTheoryPrimitiveLiteral> literals({
            normalize_smt_theory_literal(
                make_smt_theory_literal(ex>=0))[0][0]
        });

        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve(one_space,unbounded,literals));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve(two_space,bounded,literals));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve_parallel(one_space,unbounded,literals));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve_parallel(two_space,bounded,literals));

        SmtSolver adaptive_solver(SmtSolverConfiguration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,false,false,false,false,true,false,false,false,true,true));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, adaptive_solver.solve_parallel(bounded,one_dimensional));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, adaptive_solver.solve_parallel(one_space,bounded,literals));

        ContinuousPredicate predicate=(ex>=0);
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve(one_space,unbounded,predicate));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve(two_space,bounded,predicate));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve_parallel(one_space,unbounded,predicate));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve_parallel(two_space,bounded,predicate));
    }

    Void test_result() {
        std::ostringstream invalid_stream;
        ARIADNE_TESTING_NOTE("[smt-result] construct UNSAT result");
        SmtResult unsat=SmtResult::unsat();
        ARIADNE_TESTING_PROVE(unsat.is_unsat());
        ARIADNE_TESTING_PROVE(not unsat.is_epsilon_sat());
        ARIADNE_TESTING_PROVE(not unsat.has_witness());
        ARIADNE_TESTING_PROVE(not unsat.is_unknown());

        ARIADNE_TESTING_NOTE("[smt-result] reject witness access for UNSAT");
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, unsat.witness());

        UpperBoxType witness=ExactBoxType({ExactIntervalType(-1,1),ExactIntervalType(2,3)});
        ARIADNE_TESTING_NOTE("[smt-result] construct EPSILON_SAT result witness=" << witness);
        SmtResult epsilon_sat=SmtResult::epsilon_sat(witness);
        ARIADNE_TESTING_PROVE(not epsilon_sat.is_unsat());
        ARIADNE_TESTING_PROVE(epsilon_sat.is_epsilon_sat());
        ARIADNE_TESTING_PROVE(epsilon_sat.has_witness());

        ARIADNE_TESTING_NOTE("[smt-result] verify witness dimension=" << witness.dimension());
        ARIADNE_TESTING_EXPECT_EQUAL(epsilon_sat.witness().dimension(),witness.dimension());
        for(SizeType i=0; i!=witness.dimension(); ++i) {
            ARIADNE_TESTING_NOTE("[smt-result] verify witness coordinate=" << i
                      << " expected=" << witness[i]
                      << " actual=" << epsilon_sat.witness()[i]);
            ARIADNE_TESTING_EXPECT_EQUAL(epsilon_sat.witness()[i].lower_bound().raw(),witness[i].lower_bound().raw());
            ARIADNE_TESTING_EXPECT_EQUAL(epsilon_sat.witness()[i].upper_bound().raw(),witness[i].upper_bound().raw());
        }

        ARIADNE_TESTING_NOTE("[smt-result] default search statistics are zero");
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().boxes_processed,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().boxes_pruned,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().boxes_split,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().box_budget_exhaustions,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().non_splittable_uncertified_boxes,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().non_splittable_epsilon_overlap_boxes,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(epsilon_sat.statistics().boxes_processed,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(epsilon_sat.statistics().boxes_pruned,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(epsilon_sat.statistics().boxes_split,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().hull_reduction_rounds,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().hull_effective_reductions,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().hull_procedure_builds,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().hull_procedure_build_seconds,0.0);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().hull_contraction_seconds,0.0);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().hull_direct_rejection_seconds,0.0);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().shaving_reduction_rounds,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().shaving_effective_reductions,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().shaving_function_evaluations,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().sensitivity_guided_splits,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().sensitivity_derivatives_built,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().sensitivity_derivative_evaluations,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().sensitivity_overrides_geometric_splits,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().epsilon_box_certifications,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().candidate_witness_searches,0u);
        ARIADNE_TESTING_EXPECT_EQUAL(unsat.statistics().candidate_witness_successes,0u);

        ARIADNE_TESTING_NOTE("[smt-result] construct UNKNOWN result with explicit reason");
        SmtResult unknown=SmtResult::unknown(SmtUnknownReason::RESOURCE_EXHAUSTED);
        ARIADNE_TESTING_PROVE(unknown.is_unknown());
        ARIADNE_TESTING_PROVE(not unknown.is_unsat());
        ARIADNE_TESTING_PROVE(not unknown.is_epsilon_sat());
        ARIADNE_TESTING_PROVE(not unknown.has_witness());
        ARIADNE_TESTING_PROVE(
            unknown.unknown_reason()==SmtUnknownReason::RESOURCE_EXHAUSTED);
        ARIADNE_TESTING_PROVE(
            unsat.unknown_reason()==SmtUnknownReason::NONE);
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtResult::unknown(SmtUnknownReason::NONE));

        ARIADNE_TESTING_NOTE("[smt-result] stream statuses");
        std::ostringstream oss;
        oss << unsat.status() << " " << epsilon_sat.status() << " " << unknown.status();
        ARIADNE_TESTING_EXPECT_EQUAL(oss.str(),String("UNSAT EPSILON_SAT UNKNOWN"));

        std::ostringstream reason_stream;
        reason_stream
            << SmtUnknownReason::NONE << " "
            << SmtUnknownReason::RESOURCE_EXHAUSTED << " "
            << SmtUnknownReason::DP_RESOLUTION_EXHAUSTED << " "
            << SmtUnknownReason::MIXED;
        ARIADNE_TESTING_EXPECT_EQUAL(
            reason_stream.str(),
            String("NONE RESOURCE_EXHAUSTED DP_RESOLUTION_EXHAUSTED MIXED"));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, static_cast<Void>(
                static_cast<OutputStream&>(invalid_stream)
                << static_cast<SmtUnknownReason>(999)));

        ARIADNE_TESTING_NOTE("[smt-result] reject invalid status");
        auto invalid_status=static_cast<SmtResultStatus>(999);
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, static_cast<Void>(
                static_cast<OutputStream&>(invalid_stream) << invalid_status));
    }

    Void test_learned_clause_pruning_policy() {
        ARIADNE_TESTING_NOTE("[smt-dpll] deterministic learned clause pruning policy");
        using Entry=SmtSolverTestSupport::LearnedClausePruningEntry;
        std::vector<Entry> entries({
            {false,false,false,false,false,false,false,1u,5u},
            {true,true,false,false,false,false,false,1u,5u},
            {true,false,true,false,false,false,false,1u,5u},
            {true,false,false,true,false,false,false,1u,2u},
            {true,false,false,false,true,false,false,2u,5u},
            {true,false,false,false,false,true,false,1u,5u},
            {true,false,false,false,false,false,true,1u,5u},
            {true,false,false,false,false,false,false,2u,7u},
            {true,false,false,false,false,false,false,1u,4u},
            {true,false,false,false,false,false,false,1u,6u}
        });
        std::vector<SizeType> candidates=
            SmtSolverTestSupport::learned_clause_pruning_candidates(entries);
        ARIADNE_TESTING_EXPECT_EQUAL(candidates.size(),3u);
        ARIADNE_TESTING_EXPECT_EQUAL(candidates[0],9u);
        ARIADNE_TESTING_EXPECT_EQUAL(candidates[1],8u);
        ARIADNE_TESTING_EXPECT_EQUAL(candidates[2],7u);

        SizeType pruned=SmtSolverTestSupport::apply_learned_clause_pruning(
            candidates,3u,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(pruned,0u);

        SizeType none=SmtSolverTestSupport::apply_learned_clause_pruning(
            candidates,1u,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(none,0u);
    }

    Void test_statistics_aggregation() {
        ARIADNE_TESTING_NOTE("[smt-stats] deterministic aggregation semantics");

        SmtSearchStatistics target;
        target.last_learned_clause_literals=11u;
        target.last_learned_current_level_literals=7u;
        target.last_backjump_level=5u;

        SmtSearchStatistics no_conflict;
        no_conflict.boxes_processed=3u;
        no_conflict.monotone_reduction_rounds=4u;
        no_conflict.monotone_effective_reductions=2u;
        no_conflict.hull_procedure_builds=5u;
        no_conflict.hull_procedure_build_seconds=0.125;
        no_conflict.hull_contraction_seconds=0.25;
        no_conflict.hull_direct_rejection_seconds=0.5;
        no_conflict.shaving_function_evaluations=17u;
        no_conflict.sensitivity_derivatives_built=3u;
        no_conflict.sensitivity_derivative_evaluations=3u;
        no_conflict.sensitivity_derivative_build_seconds=0.25;
        no_conflict.sensitivity_derivative_evaluation_seconds=0.5;
        no_conflict.fused_direct_classification_boxes=6u;
        no_conflict.fused_direct_literal_evaluations=13u;
        no_conflict.preclassification_boxes=8u;
        no_conflict.preclassification_pruned_boxes=3u;
        no_conflict.preclassification_epsilon_boxes=2u;
        no_conflict.preclassification_literal_evaluations=15u;
        no_conflict.preclassification_outcomes={
            SmtPreclassificationOutcome::UNRESOLVED,
            SmtPreclassificationOutcome::PRUNED};
        no_conflict.preclassification_adaptive_skipped_boxes=12u;
        no_conflict.preclassification_adaptive_suspensions=2u;
        no_conflict.preclassification_adaptive_reactivations=1u;
        no_conflict.preclassification_seconds=0.375;
        no_conflict.interval_lookahead_guided_splits=4u;
        no_conflict.interval_lookahead_overrides_geometric_splits=3u;
        no_conflict.interval_lookahead_function_evaluations=12u;
        no_conflict.interval_lookahead_evaluation_seconds=0.75;
        no_conflict.last_learned_clause_literals=99u;
        no_conflict.last_learned_current_level_literals=99u;
        no_conflict.last_backjump_level=99u;
        SmtSolverTestSupport::accumulate_statistics(target,no_conflict);
        ARIADNE_TESTING_EXPECT_EQUAL(target.boxes_processed,3u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.monotone_reduction_rounds,4u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.monotone_effective_reductions,2u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.hull_procedure_builds,5u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.hull_procedure_build_seconds,0.125);
        ARIADNE_TESTING_EXPECT_EQUAL(target.hull_contraction_seconds,0.25);
        ARIADNE_TESTING_EXPECT_EQUAL(target.hull_direct_rejection_seconds,0.5);
        ARIADNE_TESTING_EXPECT_EQUAL(target.shaving_function_evaluations,17u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.sensitivity_derivatives_built,3u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.sensitivity_derivative_evaluations,3u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.sensitivity_derivative_build_seconds,0.25);
        ARIADNE_TESTING_EXPECT_EQUAL(target.sensitivity_derivative_evaluation_seconds,0.5);
        ARIADNE_TESTING_EXPECT_EQUAL(target.fused_direct_classification_boxes,6u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.fused_direct_literal_evaluations,13u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_boxes,8u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_pruned_boxes,3u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_epsilon_boxes,2u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_literal_evaluations,15u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_outcomes.size(),2u);
        ARIADNE_TESTING_PROVE(
            target.preclassification_outcomes[0]
            ==SmtPreclassificationOutcome::UNRESOLVED);
        ARIADNE_TESTING_PROVE(
            target.preclassification_outcomes[1]
            ==SmtPreclassificationOutcome::PRUNED);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_adaptive_skipped_boxes,12u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_adaptive_suspensions,2u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_adaptive_reactivations,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.preclassification_seconds,0.375);
        ARIADNE_TESTING_EXPECT_EQUAL(target.interval_lookahead_guided_splits,4u);
        ARIADNE_TESTING_EXPECT_EQUAL(
            target.interval_lookahead_overrides_geometric_splits,3u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.interval_lookahead_function_evaluations,12u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.interval_lookahead_evaluation_seconds,0.75);
        ARIADNE_TESTING_EXPECT_EQUAL(target.last_learned_clause_literals,11u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.last_learned_current_level_literals,7u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.last_backjump_level,5u);

        {
            ARIADNE_TESTING_NOTE("[smt-preclassify] adaptive shadow scheduler");
            std::vector<SmtPreclassificationOutcome> all_unresolved(
                64u,SmtPreclassificationOutcome::UNRESOLVED);
            auto negative=SmtSolverTestSupport::preclassification_shadow_summary(
                all_unresolved);
            ARIADNE_TESTING_EXPECT_EQUAL(negative.checks,22u);
            ARIADNE_TESTING_EXPECT_EQUAL(negative.skipped,42u);
            ARIADNE_TESTING_EXPECT_EQUAL(negative.observed_hits,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(negative.skipped_hits,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(negative.suspensions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(negative.reactivations,0u);

            std::vector<SmtPreclassificationOutcome> delayed_positive(
                64u,SmtPreclassificationOutcome::UNRESOLVED);
            delayed_positive[13]=SmtPreclassificationOutcome::PRUNED;
            for(SizeType i=16u;i<64u;i+=8u) {
                delayed_positive[i]=SmtPreclassificationOutcome::PRUNED;
            }
            auto positive=SmtSolverTestSupport::preclassification_shadow_summary(
                delayed_positive);
            ARIADNE_TESTING_EXPECT_EQUAL(positive.checks,64u);
            ARIADNE_TESTING_EXPECT_EQUAL(positive.skipped,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(positive.skipped_hits,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(positive.suspensions,0u);

            std::vector<SmtPreclassificationOutcome> reactivation(
                32u,SmtPreclassificationOutcome::UNRESOLVED);
            reactivation[23]=SmtPreclassificationOutcome::PRUNED;
            auto refreshed=SmtSolverTestSupport::preclassification_shadow_summary(
                reactivation);
            ARIADNE_TESTING_EXPECT_EQUAL(refreshed.checks,25u);
            ARIADNE_TESTING_EXPECT_EQUAL(refreshed.skipped,7u);
            ARIADNE_TESTING_EXPECT_EQUAL(refreshed.observed_hits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(refreshed.suspensions,2u);
            ARIADNE_TESTING_EXPECT_EQUAL(refreshed.reactivations,1u);

            std::vector<SmtPreclassificationOutcome> skipped_positive(
                17u,SmtPreclassificationOutcome::UNRESOLVED);
            skipped_positive[16]=SmtPreclassificationOutcome::PRUNED;
            auto skipped_hit=SmtSolverTestSupport::preclassification_shadow_summary(
                skipped_positive);
            ARIADNE_TESTING_EXPECT_EQUAL(skipped_hit.checks,16u);
            ARIADNE_TESTING_EXPECT_EQUAL(skipped_hit.skipped,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(skipped_hit.skipped_hits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(skipped_hit.suspensions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(skipped_hit.reactivations,0u);

            ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverTestSupport::preclassification_shadow_summary(
                    std::vector<SmtPreclassificationOutcome>{},0u,8u,8u));
            ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverTestSupport::preclassification_shadow_summary(
                    std::vector<SmtPreclassificationOutcome>{},16u,0u,8u));
            ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverTestSupport::preclassification_shadow_summary(
                    std::vector<SmtPreclassificationOutcome>{},16u,8u,0u));
        }

        SmtSearchStatistics empty_target;
        SmtSearchStatistics empty_source;
        SmtSolverTestSupport::accumulate_statistics(empty_target,empty_source);
        ARIADNE_TESTING_EXPECT_EQUAL(empty_target.first_minimization_candidate_trail_rank,0u);

        SmtSearchStatistics first_rank;
        SmtSolverTestSupport::record_first_minimization_candidate_trail_rank(
            first_rank,7u);
        SmtSolverTestSupport::record_first_minimization_candidate_trail_rank(
            first_rank,11u);
        ARIADNE_TESTING_EXPECT_EQUAL(
            first_rank.first_minimization_candidate_trail_rank,7u);

        SmtSearchStatistics conflict;
        conflict.boolean_conflicts_analyzed=1u;
        conflict.last_learned_clause_literals=4u;
        conflict.last_learned_current_level_literals=1u;
        conflict.last_backjump_level=2u;
        conflict.first_minimization_candidate_trail_rank=9u;
        SmtSolverTestSupport::accumulate_statistics(target,conflict);
        ARIADNE_TESTING_EXPECT_EQUAL(target.last_learned_clause_literals,4u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.last_learned_current_level_literals,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.last_backjump_level,2u);
        ARIADNE_TESTING_EXPECT_EQUAL(target.first_minimization_candidate_trail_rank,9u);

        SmtSearchStatistics later;
        later.first_minimization_candidate_trail_rank=13u;
        SmtSolverTestSupport::accumulate_statistics(target,later);
        ARIADNE_TESTING_EXPECT_EQUAL(target.first_minimization_candidate_trail_rank,9u);
    }

    Void test_parallel_state_transitions() {
        {
            UpperBoxType box(ExactBoxType({ExactIntervalType(-1,1)}));
            auto children=box.split();
            auto lower_first=SmtSolverTestSupport::sequential_children_to_push(
                false,children);
            auto upper_first=SmtSolverTestSupport::sequential_children_to_push(
                true,children);
            ARIADNE_TESTING_EXPECT_EQUAL(
                lower_first.back()[0].upper_bound().raw(),
                children.first[0].upper_bound().raw());
            ARIADNE_TESTING_EXPECT_EQUAL(
                upper_first.back()[0].lower_bound().raw(),
                children.second[0].lower_bound().raw());
        }
        ARIADNE_TESTING_NOTE("[smt-parallel] deterministic shared-state transitions");
        ARIADNE_TESTING_PROVE(not SmtSolverTestSupport::parallel_stop_condition(false,false));
        ARIADNE_TESTING_PROVE(SmtSolverTestSupport::parallel_stop_condition(true,false));
        ARIADNE_TESTING_PROVE(SmtSolverTestSupport::parallel_stop_condition(false,true));
        ARIADNE_TESTING_PROVE(SmtSolverTestSupport::parallel_stop_condition(true,true));

        UpperBoxType left({UpperIntervalType(ExactIntervalType(-1,0))});
        UpperBoxType right({UpperIntervalType(ExactIntervalType(0,1))});
        Pair<UpperBoxType,UpperBoxType> children(left,right);
        auto append_children=
            SmtSolverTestSupport::parallel_children_to_append(false,children);
        ARIADNE_TESTING_EXPECT_EQUAL(append_children.size(),2u);
        auto stopped_children=
            SmtSolverTestSupport::parallel_children_to_append(true,children);
        ARIADNE_TESTING_PROVE(stopped_children.empty());

        auto claims=SmtSolverTestSupport::parallel_witness_claim_sequence();
        ARIADNE_TESTING_PROVE(claims.first);
        ARIADNE_TESTING_PROVE(not claims.second);
    }

    Void test_epsilon_witness_candidate_limits() {
        ARIADNE_TESTING_NOTE("[smt-candidate] deterministic corner candidate limits");

        UpperIntervalType unit(ExactIntervalType(0,1));
        UpperBoxType six_dimensions(6u,unit);
        UpperBoxType seven_dimensions(7u,unit);
        UpperBoxType sixty_four_dimensions(64u,unit);

        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::epsilon_witness_candidate_count(six_dimensions),
            79u);
        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::epsilon_witness_candidate_count(seven_dimensions),
            17u);
        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::epsilon_witness_candidate_count(sixty_four_dimensions),
            131u);
    }

    Void test_theory_derivative_compilation_policy() {
        RealVariable x("compile_derivative_x"), y("compile_derivative_y");
        RealSpace space({x,y});
        RealExpression expression=x*x+y;
        List<SmtTheoryPrimitiveLiteral> literals({
            normalize_smt_theory_literal(
                make_smt_theory_literal(expression>=0))[0][0]
        });

        SmtSolver without_derivative_users(SmtSolverConfiguration(
            0.01_pr,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,
            false,
            false));
        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::compiled_theory_derivative_count(
                without_derivative_users,space,literals),
            0u);

        SmtSolver with_monotone(SmtSolverConfiguration(
            0.01_pr,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,
            true,
            false));
        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::compiled_theory_derivative_count(
                with_monotone,space,literals),
            space.dimension());

        SmtSolver with_sensitivity(SmtSolverConfiguration(
            0.01_pr,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,
            false,
            true));
        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::compiled_theory_derivative_count(
                with_sensitivity,space,literals),
            space.dimension());

        SmtSolver candidate_solver(SmtSolverConfiguration(
            0.01_pr,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            false,false,false,false,false,false,false,false,true));

        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::interval_newton_subsystem_candidate_count(
                candidate_solver,RealSpace({}),List<SmtTheoryPrimitiveLiteral>()),
            0u);

        List<SmtTheoryPrimitiveLiteral> insufficient_equalities({
            SmtTheoryPrimitiveLiteral(
                RealExpression(x),SmtTheoryPrimitiveRelation::EQ_ZERO),
            SmtTheoryPrimitiveLiteral(
                RealExpression(y),SmtTheoryPrimitiveRelation::GEQ_ZERO),
            SmtTheoryPrimitiveLiteral(
                RealExpression(x)+RealExpression(y),
                SmtTheoryPrimitiveRelation::GT_ZERO)
        });
        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::interval_newton_subsystem_candidate_count(
                candidate_solver,space,insufficient_equalities),
            0u);

        List<SmtTheoryPrimitiveLiteral> many_equalities({
            SmtTheoryPrimitiveLiteral(
                RealExpression(x),SmtTheoryPrimitiveRelation::EQ_ZERO),
            SmtTheoryPrimitiveLiteral(
                RealExpression(y),SmtTheoryPrimitiveRelation::EQ_ZERO),
            SmtTheoryPrimitiveLiteral(
                RealExpression(x)+RealExpression(y),
                SmtTheoryPrimitiveRelation::EQ_ZERO),
            SmtTheoryPrimitiveLiteral(
                RealExpression(x)-RealExpression(y),
                SmtTheoryPrimitiveRelation::EQ_ZERO),
            SmtTheoryPrimitiveLiteral(
                2*RealExpression(x)+RealExpression(y),
                SmtTheoryPrimitiveRelation::EQ_ZERO)
        });
        ARIADNE_TESTING_EXPECT_EQUAL(
            SmtSolverTestSupport::interval_newton_subsystem_candidate_count(
                candidate_solver,space,many_equalities),
            8u);
    }

    Void test_candidate_witness_outcome() {
        ARIADNE_TESTING_NOTE("[smt-candidate] deterministic candidate outcome");
        UpperBoxType witness({
            UpperIntervalType(ExactIntervalType(1,1))
        });

        auto disabled=SmtSolverTestSupport::candidate_witness_outcome(
            false,std::nullopt);
        ARIADNE_TESTING_PROVE(not disabled.attempted);
        ARIADNE_TESTING_PROVE(not disabled.certified);
        ARIADNE_TESTING_PROVE(not disabled.witness.has_value());

        auto failed=SmtSolverTestSupport::candidate_witness_outcome(
            true,std::nullopt);
        ARIADNE_TESTING_PROVE(failed.attempted);
        ARIADNE_TESTING_PROVE(not failed.certified);
        ARIADNE_TESTING_PROVE(not failed.witness.has_value());

        auto success=SmtSolverTestSupport::candidate_witness_outcome(
            true,witness);
        ARIADNE_TESTING_PROVE(success.attempted);
        ARIADNE_TESTING_PROVE(success.certified);
        ARIADNE_TESTING_PROVE(success.witness.has_value());
        ARIADNE_TESTING_EXPECT_EQUAL(success.witness->dimension(),1u);
    }

    Void test_sensitivity_split_selection() {
        ARIADNE_TESTING_NOTE("[smt-split] deterministic sensitivity selection");
        auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
        UpperBoxType domain({
            UpperIntervalType(ExactIntervalType(0,1)),
            UpperIntervalType(ExactIntervalType(0,4))
        });

        {
            std::vector<ValidatedScalarMultivariateFunction> functions({
                sqr(xy[0])
            });
            auto selection=SmtSolverTestSupport::sensitivity_split_selection(
                domain,functions);
            ARIADNE_TESTING_PROVE(selection.guided);
            ARIADNE_TESTING_EXPECT_EQUAL(selection.coordinate,0u);
            ARIADNE_TESTING_PROVE(selection.overrode_geometric);
        }

        {
            std::vector<ValidatedScalarMultivariateFunction> functions({
                ValidatedScalarMultivariateFunction::zero(2u)
            });
            auto selection=SmtSolverTestSupport::sensitivity_split_selection(
                domain,functions);
            ARIADNE_TESTING_PROVE(not selection.guided);
            ARIADNE_TESTING_EXPECT_EQUAL(selection.coordinate,1u);
            ARIADNE_TESTING_PROVE(not selection.overrode_geometric);
        }

        {
            std::vector<ValidatedScalarMultivariateFunction> functions({
                xy[0]+2*xy[1]
            });
            auto selection=SmtSolverTestSupport::sensitivity_split_selection(
                domain,functions);
            ARIADNE_TESTING_PROVE(selection.guided);
            ARIADNE_TESTING_EXPECT_EQUAL(selection.coordinate,1u);
            ARIADNE_TESTING_PROVE(not selection.overrode_geometric);
        }

        {
            UpperBoxType wide_first({
                UpperIntervalType(ExactIntervalType(0,4)),
                UpperIntervalType(ExactIntervalType(0,1))
            });
            std::vector<ValidatedScalarMultivariateFunction> functions({
                2*xy[0]+xy[1]
            });
            auto selection=SmtSolverTestSupport::sensitivity_split_selection(
                wide_first,functions);
            ARIADNE_TESTING_PROVE(selection.guided);
            ARIADNE_TESTING_EXPECT_EQUAL(selection.coordinate,0u);
            ARIADNE_TESTING_PROVE(not selection.overrode_geometric);
        }
    }

    Void test_monotone_coordinate_gating() {
        ARIADNE_TESTING_NOTE("[smt-icp] validated monotone coordinate gating");
        auto x=ValidatedScalarMultivariateFunction::coordinates(1);
        UpperBoxType positive_domain({UpperIntervalType(ExactIntervalType(0,2))});
        UpperBoxType monotone_sine_domain({UpperIntervalType(ExactIntervalType(3,4))});
        UpperBoxType nonmonotone_sine_domain({UpperIntervalType(ExactIntervalType(0,4))});

        RealVariable sx("smooth_gate_x");
        RealExpression smooth_expression=exp(RealExpression(sx))+RealExpression(sx);
        RealSpace smooth_space({sx});
        ValidatedScalarMultivariateFunction smooth_function(
            make_function(smooth_space,smooth_expression));
        auto positive_derivative=SmtSolverTestSupport::optional_derivative(
            smooth_expression,smooth_function,0u);
        ARIADNE_TESTING_PROVE(positive_derivative.has_value());
        RealExpression nonsmooth_expression=max(
            RealExpression(sx),RealExpression(0));
        ValidatedScalarMultivariateFunction nonsmooth_function(
            make_function(smooth_space,nonsmooth_expression));
        auto nonsmooth_derivative=SmtSolverTestSupport::optional_derivative(
            nonsmooth_expression,nonsmooth_function,0u);
        ARIADNE_TESTING_PROVE(not nonsmooth_derivative.has_value());
        ARIADNE_TESTING_PROVE(
            not SmtSolverTestSupport::expression_is_differentiable(
                abs(nonsmooth_expression)));
        ARIADNE_TESTING_PROVE(
            not SmtSolverTestSupport::expression_is_differentiable(
                RealExpression(sx)+max(RealExpression(sx),RealExpression(0))));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverTestSupport::validate_differentiable_expression_kind(
                static_cast<OperatorKind>(255)));
        auto negative_derivative=(-exp(x[0])-x[0]).derivative(0u);
        ARIADNE_TESTING_PROVE(
            definitely(apply(negative_derivative,positive_domain).upper_bound()<0));

        auto sine_derivative=sin(x[0]).derivative(0u);
        ARIADNE_TESTING_PROVE(
            definitely(apply(sine_derivative,monotone_sine_domain).upper_bound()<0));
        UpperIntervalType nonmonotone_image=
            apply(sine_derivative,nonmonotone_sine_domain);
        ARIADNE_TESTING_PROVE(
            not definitely(nonmonotone_image.lower_bound()>0));
        ARIADNE_TESTING_PROVE(
            not definitely(nonmonotone_image.upper_bound()<0));
    }

    Void test_search_outcome() {
        ARIADNE_TESTING_NOTE("[smt-dpll] deterministic search outcome classification");
        using Outcome=SmtSolverTestSupport::SearchOutcome;

        Outcome exhausted=Outcome::exhausted();
        ARIADNE_TESTING_PROVE(not exhausted.witness.has_value());
        ARIADNE_TESTING_PROVE(not exhausted.backjump_level.has_value());

        Outcome backjump=Outcome::backjump(3u);
        ARIADNE_TESTING_PROVE(not backjump.witness.has_value());
        ARIADNE_TESTING_PROVE(backjump.backjump_level.has_value());
        ARIADNE_TESTING_EXPECT_EQUAL(*backjump.backjump_level,3u);

        UpperBoxType witness({
            UpperIntervalType(ExactIntervalType(0,0))
        });
        Outcome found=Outcome::found(witness);
        ARIADNE_TESTING_PROVE(found.witness.has_value());
        ARIADNE_TESTING_PROVE(not found.backjump_level.has_value());

        SmtSearchStatistics statistics;
        SmtResult sat=SmtSolverTestSupport::finalize_search_outcome(
            found,SmtUnknownReason::NONE,statistics);
        ARIADNE_TESTING_PROVE(sat.is_epsilon_sat());
        ARIADNE_TESTING_PROVE(sat.has_witness());

        SmtResult unknown=SmtSolverTestSupport::finalize_search_outcome(
            exhausted,SmtUnknownReason::DP_RESOLUTION_EXHAUSTED,statistics);
        ARIADNE_TESTING_PROVE(unknown.is_unknown());
        ARIADNE_TESTING_PROVE(
            unknown.unknown_reason()==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
        ARIADNE_TESTING_PROVE(
            SmtSolverTestSupport::combine_unknown_reasons(
                SmtUnknownReason::NONE,SmtUnknownReason::RESOURCE_EXHAUSTED)
            ==SmtUnknownReason::RESOURCE_EXHAUSTED);
        ARIADNE_TESTING_PROVE(
            SmtSolverTestSupport::combine_unknown_reasons(
                SmtUnknownReason::DP_RESOLUTION_EXHAUSTED,SmtUnknownReason::NONE)
            ==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
        ARIADNE_TESTING_PROVE(
            SmtSolverTestSupport::combine_unknown_reasons(
                SmtUnknownReason::RESOURCE_EXHAUSTED,SmtUnknownReason::RESOURCE_EXHAUSTED)
            ==SmtUnknownReason::RESOURCE_EXHAUSTED);
        ARIADNE_TESTING_PROVE(
            SmtSolverTestSupport::combine_unknown_reasons(
                SmtUnknownReason::RESOURCE_EXHAUSTED,SmtUnknownReason::DP_RESOLUTION_EXHAUSTED)
            ==SmtUnknownReason::MIXED);

        SmtResult unsat=SmtSolverTestSupport::finalize_search_outcome(
            exhausted,SmtUnknownReason::NONE,statistics);
        ARIADNE_TESTING_PROVE(unsat.is_unsat());
    }

    Void test_cdcl_helpers() {
        ARIADNE_TESTING_NOTE("[smt-cdcl] deterministic clause resolution and nogood ordering");

        auto lit=[](Int signed_literal) {
            return BooleanLiteral::from_dimacs(signed_literal);
        };
        std::vector<BooleanLiteral> resolved=
            SmtSolverTestSupport::resolve_clause_on_variable(
                std::vector<BooleanLiteral>({lit(1),lit(2),lit(3),lit(3)}),
                std::vector<BooleanLiteral>({lit(-1),lit(3),lit(4),lit(4)}),
                0u);
        ARIADNE_TESTING_EXPECT_EQUAL(resolved.size(),3u);
        ARIADNE_TESTING_EXPECT_EQUAL(resolved[0].dimacs(),2);
        ARIADNE_TESTING_EXPECT_EQUAL(resolved[1].dimacs(),3);
        ARIADNE_TESTING_EXPECT_EQUAL(resolved[2].dimacs(),4);

        std::vector<BooleanLiteral> clause({lit(1),lit(-2),lit(3),lit(-4)});
        std::vector<SizeType> decision_levels({1u,2u,2u,1u});
        std::vector<SizeType> trail_rank({1u,2u,4u,3u});
        SmtSolverTestSupport::order_theory_nogood(
            clause,decision_levels,trail_rank);
        ARIADNE_TESTING_EXPECT_EQUAL(clause[0].dimacs(),3);
        ARIADNE_TESTING_EXPECT_EQUAL(clause[1].dimacs(),-2);
        ARIADNE_TESTING_EXPECT_EQUAL(clause[2].dimacs(),-4);
        ARIADNE_TESTING_EXPECT_EQUAL(clause[3].dimacs(),1);

        {
            ARIADNE_TESTING_NOTE("[smt-theory-propagation] validated atom classification");
            RealVariable tx("classify_x");
            RealExpression etx=tx;
            RealSpace tspace({tx});
            ExactBoxType zero({ExactIntervalType(0,0)});
            ExactBoxType positive({ExactIntervalType(1,2)});
            ExactBoxType negative({ExactIntervalType(-2,-1)});
            ExactBoxType crossing({ExactIntervalType(-1,1)});
            using Truth=SmtSolverTestSupport::TheoryAtomTruth;

            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,zero,(etx==0))==Truth::TRUE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,positive,(etx==0))==Truth::FALSE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,crossing,(etx==0))==Truth::UNKNOWN);

            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,positive,(etx!=0))==Truth::TRUE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,zero,(etx!=0))==Truth::FALSE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,crossing,(etx!=0))==Truth::UNKNOWN);

            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,positive,(etx>=0))==Truth::TRUE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,negative,(etx>=0))==Truth::FALSE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,crossing,(etx>=0))==Truth::UNKNOWN);

            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,negative,(etx<=0))==Truth::TRUE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,positive,(etx<=0))==Truth::FALSE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,crossing,(etx<=0))==Truth::UNKNOWN);

            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,positive,(etx>0))==Truth::TRUE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,zero,(etx>0))==Truth::FALSE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,crossing,(etx>0))==Truth::UNKNOWN);

            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,negative,(etx<0))==Truth::TRUE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,zero,(etx<0))==Truth::FALSE_VALUE);
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::classify_theory_atom(
                    tspace,crossing,(etx<0))==Truth::UNKNOWN);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-propagation] epsilon-safe domain implications");
            RealVariable ix("implication_x");
            RealExpression eix=ix;
            RealSpace ispace({ix});
            ExactBoxType domain({ExactIntervalType(0,1)});
            SmtSolver implication_solver(SmtSolverConfiguration(0.125_x));

            auto false_implication=SmtSolverTestSupport::domain_theory_implication(
                implication_solver,ispace,domain,(eix>2));
            ARIADNE_TESTING_PROVE(not false_implication.force_true);
            ARIADNE_TESTING_PROVE(false_implication.force_false);

            auto true_implication=SmtSolverTestSupport::domain_theory_implication(
                implication_solver,ispace,domain,(eix>=-2));
            ARIADNE_TESTING_PROVE(true_implication.force_true);
            ARIADNE_TESTING_PROVE(not true_implication.force_false);

            auto relaxed_strict=SmtSolverTestSupport::domain_theory_implication(
                implication_solver,
                ispace,
                ExactBoxType({ExactIntervalType(0,0)}),
                (eix>0));
            ARIADNE_TESTING_PROVE(not relaxed_strict.force_true);
            ARIADNE_TESTING_PROVE(not relaxed_strict.force_false);

            auto undecided=SmtSolverTestSupport::domain_theory_implication(
                implication_solver,ispace,domain,(eix==0.5_x));
            ARIADNE_TESTING_PROVE(not undecided.force_true);
            ARIADNE_TESTING_PROVE(not undecided.force_false);
        }

        std::vector<Bool> theory_flags({false,true});
        ARIADNE_TESTING_PROVE(not SmtSolverTestSupport::clause_is_learned(1u,2u));
        ARIADNE_TESTING_PROVE(SmtSolverTestSupport::clause_is_learned(2u,2u));
        ARIADNE_TESTING_PROVE(not SmtSolverTestSupport::learned_clause_is_theory(
            1u,2u,theory_flags));
        ARIADNE_TESTING_PROVE(not SmtSolverTestSupport::learned_clause_is_theory(
            2u,2u,theory_flags));
        ARIADNE_TESTING_PROVE(SmtSolverTestSupport::learned_clause_is_theory(
            3u,2u,theory_flags));
        ARIADNE_TESTING_PROVE(SmtSolverTestSupport::assignment_locks_clause(
            1,std::optional<SizeType>(7u),7u));
        ARIADNE_TESTING_PROVE(not SmtSolverTestSupport::assignment_locks_clause(
            -1,std::optional<SizeType>(7u),7u));
        ARIADNE_TESTING_PROVE(not SmtSolverTestSupport::assignment_locks_clause(
            1,std::nullopt,7u));
        ARIADNE_TESTING_PROVE(not SmtSolverTestSupport::assignment_locks_clause(
            1,std::optional<SizeType>(6u),7u));

        UpperBoxType witness({
            UpperIntervalType(ExactIntervalType(0,0))
        });
        auto sat=SmtSolverTestSupport::interpret_theory_result(
            SmtResult::epsilon_sat(witness));
        ARIADNE_TESTING_PROVE(sat.consistent);
        ARIADNE_TESTING_PROVE(sat.unknown_reason==SmtUnknownReason::NONE);
        ARIADNE_TESTING_PROVE(sat.witness.has_value());

        auto unknown=SmtSolverTestSupport::interpret_theory_result(
            SmtResult::unknown(SmtUnknownReason::RESOURCE_EXHAUSTED));
        ARIADNE_TESTING_PROVE(unknown.consistent);
        ARIADNE_TESTING_PROVE(unknown.unknown_reason!=SmtUnknownReason::NONE);
        ARIADNE_TESTING_PROVE(not unknown.witness.has_value());

        auto unsat=SmtSolverTestSupport::interpret_theory_result(
            SmtResult::unsat());
        ARIADNE_TESTING_PROVE(not unsat.consistent);
        ARIADNE_TESTING_PROVE(unsat.unknown_reason==SmtUnknownReason::NONE);
        ARIADNE_TESTING_PROVE(not unsat.witness.has_value());
    }

    Void test_invalid_internal_relations() {
        ARIADNE_TESTING_NOTE("[smt-internal] reject invalid primitive relation");
        SmtSolver solver(SmtSolverConfiguration(0.125_x));
        auto invalid=static_cast<SmtTheoryPrimitiveRelation>(999);
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverTestSupport::original_bounds(solver,invalid));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverTestSupport::epsilon_primitive_image_infeasible(
                invalid,
                UpperIntervalType(ExactIntervalType(0,0)),
                FloatDP(0.125_x,dp)));

        UpperBoxType endpoint_candidate({
            UpperIntervalType(ExactIntervalType(1,1))
        });

        SmtTheoryRelation invalid_theory_relation=
            static_cast<SmtTheoryRelation>(999);
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverTestSupport::classify_theory_relation(
                invalid_theory_relation,
                UpperIntervalType(ExactIntervalType(0,0))));
    }

    Void test_epsilon_predicates() {
        ARIADNE_TESTING_NOTE("[smt-epsilon] deterministic satisfaction");
        SmtSolver solver(SmtSolverConfiguration(0.125_x));
        auto x=ValidatedScalarMultivariateFunction::coordinates(1);
        UpperBoxType point({
            UpperIntervalType(ExactIntervalType(0,0))
        });

        List<ValidatedConstraint> outside({
            ValidatedConstraint(
                ValidatedNumber(1),
                x[0],
                ValidatedNumber(1))
        });
        ARIADNE_TESTING_PROVE(
            not SmtSolverTestSupport::epsilon_satisfied(
                solver,point,outside));

        List<ValidatedConstraint> inside({
            ValidatedConstraint(
                ValidatedNumber(0),
                x[0],
                ValidatedNumber(0))
        });
        ARIADNE_TESTING_PROVE(
            SmtSolverTestSupport::epsilon_satisfied(
                solver,point,inside));

        UpperBoxType narrow_box({
            UpperIntervalType(ExactIntervalType(0,0.0625_x))
        });
        ARIADNE_TESTING_PROVE(
            SmtSolverTestSupport::epsilon_satisfied(
                solver,narrow_box,inside));

        UpperBoxType wide_box({
            UpperIntervalType(ExactIntervalType(-0.25_x,0.25_x))
        });
        ARIADNE_TESTING_PROVE(
            not SmtSolverTestSupport::epsilon_satisfied(
                solver,wide_box,inside));

    }

    Void test_fused_direct_classification() {
        ARIADNE_TESTING_NOTE("[smt-fast-path] fused rejection and epsilon classification");
        RealVariable sx("fast_path_x");
        RealExpression ex=sx;
        RealSpace space({sx});

        SmtSolver solver(SmtSolverConfiguration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            1u,
            false,
            false,
            false,
            false,
            false,
            false));

        {
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex-2,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().fused_direct_classification_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().epsilon_box_certifications,0u);
        }

        {
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,0.0625_x)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().fused_direct_classification_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().epsilon_box_certifications,1u);
        }

        {
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(-0.25_x,0.25_x)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().fused_direct_classification_boxes,1u);
        }

        {
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GT_ZERO)
            });
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,0)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().fused_direct_classification_boxes,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-fast-path] strict epsilon relaxation certifies near-zero box");
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GT_ZERO)
            });
            SmtResult solve_result=solver.solve(
                space,
                ExactBoxType({ExactIntervalType(-0.0625_x,0.0625_x)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().epsilon_box_certifications,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().fused_direct_classification_boxes,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-fast-path] direct compiled pruning");
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex-2,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            auto observation=SmtSolverTestSupport::process_compiled_box(
                solver,space,
                UpperBoxType(ExactBoxType({ExactIntervalType(0,1)})),
                literals);
            ARIADNE_TESTING_PROVE(
                observation.status==
                    SmtSolverTestSupport::BoxProcessingStatus::PRUNED);
            ARIADNE_TESTING_PROVE(observation.fused_direct_classification);
            ARIADNE_TESTING_PROVE(not observation.epsilon_box_certification);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-fast-path] direct compiled epsilon certification");
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GT_ZERO)
            });
            auto observation=SmtSolverTestSupport::process_compiled_box(
                solver,space,
                UpperBoxType(ExactBoxType({
                    ExactIntervalType(-0.0625_x,0.0625_x)})),
                literals);
            ARIADNE_TESTING_PROVE(
                observation.status==
                    SmtSolverTestSupport::BoxProcessingStatus::EPSILON_SAT);
            ARIADNE_TESTING_PROVE(observation.fused_direct_classification);
            ARIADNE_TESTING_PROVE(observation.epsilon_box_certification);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-fast-path] direct compiled geometric split");
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            auto observation=SmtSolverTestSupport::process_compiled_box(
                solver,space,
                UpperBoxType(ExactBoxType({
                    ExactIntervalType(-0.25_x,0.25_x)})),
                literals);
            ARIADNE_TESTING_PROVE(
                observation.status==
                    SmtSolverTestSupport::BoxProcessingStatus::SPLIT);
            ARIADNE_TESTING_PROVE(observation.fused_direct_classification);
            ARIADNE_TESTING_PROVE(not observation.epsilon_box_certification);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-fast-path] equality upper epsilon bound remains unresolved");
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::EQ_ZERO)
            });
            auto observation=SmtSolverTestSupport::process_compiled_box(
                solver,space,
                UpperBoxType(ExactBoxType({
                    ExactIntervalType(0,0.25_x)})),
                literals);
            ARIADNE_TESTING_PROVE(
                observation.status==
                    SmtSolverTestSupport::BoxProcessingStatus::SPLIT);
            ARIADNE_TESTING_PROVE(observation.fused_direct_classification);
            ARIADNE_TESTING_PROVE(not observation.epsilon_box_certification);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-fast-path] direct literal evaluation accounting");
            List<SmtTheoryPrimitiveLiteral> early_rejection({
                SmtTheoryPrimitiveLiteral(
                    ex-2,SmtTheoryPrimitiveRelation::GEQ_ZERO),
                SmtTheoryPrimitiveLiteral(
                    ex+2,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult rejected=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),early_rejection);
            ARIADNE_TESTING_PROVE(rejected.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(
                rejected.statistics().fused_direct_literal_evaluations,1u);

            List<SmtTheoryPrimitiveLiteral> unresolved({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO),
                SmtTheoryPrimitiveLiteral(
                    -ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult split=solver.solve(
                space,ExactBoxType({ExactIntervalType(-0.25_x,0.25_x)}),unresolved);
            ARIADNE_TESTING_PROVE(split.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(
                split.statistics().fused_direct_literal_evaluations,2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-lookahead] interval lookahead overrides geometric split");
            RealVariable sy("lookahead_y");
            RealSpace lookahead_space({sx,sy});
            RealExpression ey=sy;
            SmtSolver lookahead_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,
                false,
                false,
                false,
                false,
                false,
                true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ey,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=lookahead_solver.solve(
                lookahead_space,
                ExactBoxType({
                    ExactIntervalType(-2,2),
                    ExactIntervalType(-1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_guided_splits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_overrides_geometric_splits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_function_evaluations,4u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-lookahead] interval lookahead keeps geometric split");
            RealVariable sy("lookahead_geometric_y");
            RealSpace lookahead_space({sx,sy});
            SmtSolver lookahead_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,false,false,false,false,false,true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=lookahead_solver.solve(
                lookahead_space,
                ExactBoxType({
                    ExactIntervalType(-2,2),
                    ExactIntervalType(-1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_guided_splits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_overrides_geometric_splits,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_function_evaluations,4u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-lookahead] singleton coordinate is skipped");
            RealVariable sy("lookahead_singleton_y");
            RealSpace lookahead_space({sx,sy});
            RealExpression ey=sy;
            SmtSolver lookahead_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,false,false,false,false,false,true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ey,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=lookahead_solver.solve(
                lookahead_space,
                ExactBoxType({
                    ExactIntervalType(0,0),
                    ExactIntervalType(-2,2)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_guided_splits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_overrides_geometric_splits,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_lookahead_function_evaluations,2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-fast-path] interval Newton enabled without equality subsystem");
            SmtSolver no_newton_candidate_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,false,false,false,false,false,false,false,true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            auto observation=SmtSolverTestSupport::process_compiled_box(
                no_newton_candidate_solver,space,
                UpperBoxType(ExactBoxType({
                    ExactIntervalType(-0.25_x,0.25_x)})),
                literals);
            ARIADNE_TESTING_PROVE(observation.fused_direct_classification);
        }

        {
            SmtSolver contractor_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,
                false,
                false,
                false,
                false,
                true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=contractor_solver.solve(
                space,ExactBoxType({ExactIntervalType(-0.25_x,0.25_x)}),literals);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().fused_direct_classification_boxes,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-preclassify] prune before hull");
            SmtSolver preclassification_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,
                false,
                false,
                false,
                false,
                true,
                false,
                false,
                false,
                true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex-2,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=preclassification_solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_pruned_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_literal_evaluations,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_outcomes.size(),1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().preclassification_outcomes[0]
                ==SmtPreclassificationOutcome::PRUNED);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().hull_reduction_rounds,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().fused_direct_classification_boxes,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-preclassify] unresolved box continues to hull");
            SmtSolver preclassification_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,
                false,
                false,
                false,
                false,
                true,
                false,
                false,
                false,
                true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=preclassification_solver.solve(
                space,ExactBoxType({ExactIntervalType(-0.25_x,0.25_x)}),literals);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_pruned_boxes,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_epsilon_boxes,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_outcomes.size(),1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().preclassification_outcomes[0]
                ==SmtPreclassificationOutcome::UNRESOLVED);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().hull_reduction_rounds>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-preclassify] epsilon-satisfied box is recorded");
            SmtSolver preclassification_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,false,false,false,false,true,false,false,false,true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=preclassification_solver.solve(
                space,ExactBoxType({ExactIntervalType(0,0.0625_x)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_epsilon_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_outcomes.size(),1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().preclassification_outcomes[0]
                ==SmtPreclassificationOutcome::EPSILON_SAT);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-preclassify] adaptive scheduler suspends zero-hit prechecks");
            RealVariable sy("adaptive_preclass_y");
            RealSpace adaptive_space({sx,sy});
            SmtSolver adaptive_solver(SmtSolverConfiguration(
                0.00001_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                24u,
                false,
                false,
                false,
                false,
                false,
                true,
                false,
                false,
                false,
                true,
                true));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    sin(1000*ex)-0.3_pr,SmtTheoryPrimitiveRelation::EQ_ZERO)
            });
            SmtResult solve_result=adaptive_solver.solve(
                adaptive_space,
                ExactBoxType({
                    ExactIntervalType(-1,1),
                    ExactIntervalType(-1000000000,1000000000)
                }),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::RESOURCE_EXHAUSTED);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,24u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_boxes,17u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_adaptive_suspensions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_adaptive_skipped_boxes,7u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().preclassification_adaptive_reactivations,0u);
        }
    }

    Void test_box_processing_statistics() {
        ARIADNE_TESTING_NOTE("[smt-stats] box processing status accounting");
        using Status=SmtSolverTestSupport::BoxProcessingStatus;
        using Input=SmtSolverTestSupport::BoxProcessingStatisticsInput;

        SmtSearchStatistics statistics;
        SmtSolverTestSupport::accumulate_box_processing_statistics(
            statistics,Input{Status::PRUNED,1u,1u,2u,1u,3u,1u,true,true,true,false,true,true});
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.boxes_pruned,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.hull_reduction_rounds,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.hull_effective_reductions,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.shaving_reduction_rounds,2u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.shaving_effective_reductions,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.monotone_reduction_rounds,3u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.monotone_effective_reductions,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.sensitivity_guided_splits,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.sensitivity_overrides_geometric_splits,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.epsilon_box_certifications,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.candidate_witness_searches,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.candidate_witness_successes,1u);

        SmtSolverTestSupport::accumulate_box_processing_statistics(
            statistics,Input{Status::SPLIT});
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.boxes_split,1u);

        SmtSolverTestSupport::accumulate_box_processing_statistics(
            statistics,Input{Status::UNKNOWN,0u,0u,0u,0u,0u,0u,false,false,false,true});
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.boxes_unknown,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.dp_resolution_exhaustions,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.non_splittable_uncertified_boxes,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(statistics.non_splittable_epsilon_overlap_boxes,1u);

        SmtSolverTestSupport::accumulate_box_processing_statistics(
            statistics,Input{Status::EPSILON_SAT});

        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtSolverTestSupport::accumulate_box_processing_statistics(
                statistics,Input{static_cast<Status>(999)}));
    }


    Void test_solve() {
        auto x=ValidatedScalarMultivariateFunction::coordinates(1);
        SmtSolver solver(SmtSolverConfiguration(0.125_x));

        {
            ARIADNE_TESTING_NOTE("[smt-preclassify] adaptive mode on validated constraints bypasses theory preclassification");
            SmtSolver adaptive_constraint_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                8u,
                false,false,false,false,false,true,false,false,false,true,true));
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(2),x[0],ValidatedNumber(2))
            });
            SmtResult solve_result=adaptive_constraint_solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().preclassification_boxes,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] linear UNSAT: x in [0,1], x=2");
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(2),x[0],ValidatedNumber(2))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-stats] linear UNSAT processed="
                      << solve_result.statistics().boxes_processed
                      << " pruned=" << solve_result.statistics().boxes_pruned
                      << " split=" << solve_result.statistics().boxes_split);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_processed>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_pruned>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] linear EPSILON_SAT: x in [0,1], 2*x=1");
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(1),2*x[0],ValidatedNumber(1))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] transcendental EPSILON_SAT: x in [3,4], sin(x)=0");
            ExactBoxType domain({ExactIntervalType(3,4)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),sin(x[0]),ValidatedNumber(0))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] zero box budget returns UNKNOWN");
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0.5_x),x[0],ValidatedNumber(0.5_x))
            });
            SmtResult solve_result=bounded_solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::RESOURCE_EXHAUSTED);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().non_splittable_uncertified_boxes,0u);
        }


        {
            ARIADNE_TESTING_NOTE("[smt-solve] classify non-splittable DP resolution exhaustion");
            auto tiny_x=ValidatedScalarMultivariateFunction::coordinates(1);
            SmtSolver tiny_epsilon_solver(SmtSolverConfiguration(
                1e-30_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false));
            ExactBoxType domain({ExactIntervalType(1,1)});
            ValidatedScalarMultivariateFunction residual=sin(tiny_x[0])-sin(tiny_x[0]);
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),residual,ValidatedNumber(0))
            });
            SmtResult solve_result=tiny_epsilon_solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
            ARIADNE_TESTING_PROVE(not solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().dp_resolution_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().non_splittable_uncertified_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().non_splittable_epsilon_overlap_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] constant function UNSAT after direct range check");
            ExactBoxType domain({ExactIntervalType(0,1)});
            ValidatedScalarMultivariateFunction constant=
                ValidatedScalarMultivariateFunction::constant(
                    1u,ValidatedNumber(2));
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(
                    ValidatedNumber(0),
                    constant,
                    ValidatedNumber(0))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] transcendental UNSAT: x in [3,4], sin(x)=2");
            ExactBoxType domain({ExactIntervalType(3,4)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(2),sin(x[0]),ValidatedNumber(2))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] even power EPSILON_SAT: x in [-2,0], x^2=1");
            ExactBoxType domain({ExactIntervalType(-2,0)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(1),sqr(x[0]),ValidatedNumber(1))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] endpoint witness avoids split for x^2=4 on [-2,2]");
            ExactBoxType domain({ExactIntervalType(-2,2)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(4),sqr(x[0]),ValidatedNumber(4))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.witness()[0].lower_bound().raw(),
                UpperIntervalType(ExactIntervalType(-2,-2)).lower_bound().raw());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] mixed-corner witness avoids split for x*y=-1");
            auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
            ExactBoxType domain({
                ExactIntervalType(-1,1),
                ExactIntervalType(-1,1)
            });
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(
                    ValidatedNumber(-1),
                    xy[0]*xy[1],
                    ValidatedNumber(-1))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_PROVE(
                solve_result.witness()[0].lower_bound().raw()
                != solve_result.witness()[1].lower_bound().raw());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] conjunction EPSILON_SAT: x in [0,1], x>=0.25 and x<=0.75");
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0.25_x),x[0],ValidatedNumber(+infty)),
                ValidatedConstraint(ValidatedNumber(-infty),x[0],ValidatedNumber(0.75_x))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] conjunction UNSAT: x in [0,1], x<=0.25 and x>=0.75");
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(-infty),x[0],ValidatedNumber(0.25_x)),
                ValidatedConstraint(ValidatedNumber(0.75_x),x[0],ValidatedNumber(+infty))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] contractor fixpoint closes chained UNSAT at root");
            auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
            ExactBoxType domain({
                ExactIntervalType(0,1),
                ExactIntervalType(0,1)
            });
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),xy[0]-xy[1],ValidatedNumber(0)),
                ValidatedConstraint(ValidatedNumber(0),xy[1],ValidatedNumber(0)),
                ValidatedConstraint(ValidatedNumber(1),xy[0],ValidatedNumber(1))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] inequality EPSILON_SAT: x in [0,1], x<=0.25");
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(-infty),x[0],ValidatedNumber(0.25_x))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] inequality EPSILON_SAT: x in [0,1], x>=0.75");
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0.75_x),x[0],ValidatedNumber(+infty))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] whole-box epsilon certification");
            ExactBoxType domain({ExactIntervalType(0,0.0625_x)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),x[0],ValidatedNumber(0))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().epsilon_box_certifications,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] epsilon boundary EPSILON_SAT: x in [0,1], x=1.125 with epsilon=0.125");
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(1.125_x),x[0],ValidatedNumber(1.125_x))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat() || solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
            if(solve_result.is_epsilon_sat()) {
                ARIADNE_TESTING_PROVE(solve_result.has_witness());
            }
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] two-dimensional EPSILON_SAT: x+y=1, x-y=0");
            auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
            ExactBoxType domain({ExactIntervalType(0,1),ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(1),xy[0]+xy[1],ValidatedNumber(1)),
                ValidatedConstraint(ValidatedNumber(0),xy[0]-xy[1],ValidatedNumber(0))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.witness().dimension(),2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] two-dimensional UNSAT: x+y=3 on [0,1]^2");
            auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
            ExactBoxType domain({ExactIntervalType(0,1),ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(3),xy[0]+xy[1],ValidatedNumber(3))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] multiple transcendental branches EPSILON_SAT: sin(x)=0 on [0,7]");
            ExactBoxType domain({ExactIntervalType(0,7)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),sin(x[0]),ValidatedNumber(0))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_NOTE("[smt-stats] multiple branches processed="
                      << solve_result.statistics().boxes_processed
                      << " pruned=" << solve_result.statistics().boxes_pruned
                      << " split=" << solve_result.statistics().boxes_split);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_processed>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] shaving contractor handles repeated nonlinear occurrence");
            ExactBoxType domain({ExactIntervalType(-2,2)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(
                    ValidatedNumber(0.75_x),
                    sqr(x[0])+x[0],
                    ValidatedNumber(0.75_x))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_PROVE(solve_result.statistics().hull_reduction_rounds>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().shaving_reduction_rounds>=1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().hull_effective_reductions
                <= solve_result.statistics().hull_reduction_rounds);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().shaving_effective_reductions
                <= solve_result.statistics().shaving_reduction_rounds);
            ARIADNE_TESTING_NOTE("[smt-icp-stats] hull="
                      << solve_result.statistics().hull_effective_reductions
                      << "/" << solve_result.statistics().hull_reduction_rounds
                      << " shaving="
                      << solve_result.statistics().shaving_effective_reductions
                      << "/" << solve_result.statistics().shaving_reduction_rounds);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] monotone contractor on smooth composed constraint");
            RealVariable mx("monotone_x");
            RealExpression emx=mx;
            RealSpace mspace({mx});
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal((exp(emx)+emx==3)));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> mliterals;
            mliterals.append(alternatives[0][0]);
            SmtSolver monotone_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                true,
                true));
            SmtResult monotone_result=monotone_solver.solve(
                mspace,ExactBoxType({ExactIntervalType(0,2)}),mliterals);
            ARIADNE_TESTING_PROVE(not monotone_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(
                monotone_result.statistics().monotone_reduction_rounds,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                monotone_result.statistics().monotone_effective_reductions,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] monotone opt-in preserves non-smooth max theory literal");
            RealVariable nx("nonsmooth_x");
            RealExpression enx=nx;
            RealSpace nspace({nx});
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(max(enx,RealExpression(0))==0));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals;
            literals.append(alternatives[0][0]);
            SmtSolver monotone_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                true,
                true));
            SmtResult solve_result=monotone_solver.solve(
                nspace,ExactBoxType({ExactIntervalType(-1,-1)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] monotone contractor skips nonmonotone theory coordinate");
            RealVariable mx("nonmonotone_theory_x");
            RealExpression emx=mx;
            RealSpace mspace({mx});
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(sin(emx)==0));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> mliterals;
            mliterals.append(alternatives[0][0]);
            SmtSolver monotone_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false,
                true));
            SmtResult solve_result=monotone_solver.solve(
                mspace,ExactBoxType({ExactIntervalType(0,4)}),mliterals);
            ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().monotone_reduction_rounds,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().monotone_effective_reductions,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] epsilon-active theory split ignores certified wide literal");
            RealVariable ax("active_split_x");
            RealVariable ay("active_split_y");
            RealExpression eax=ax;
            RealExpression eay=ay;
            RealSpace aspace({ax,ay});

            auto inactive_alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(eay>=-1000));
            auto active_alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(sin(10*eax)==0.3_pr));
            ARIADNE_TESTING_EXPECT_EQUAL(inactive_alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(inactive_alternatives[0].size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(active_alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(active_alternatives[0].size(),1u);

            List<SmtTheoryPrimitiveLiteral> literals;
            literals.append(inactive_alternatives[0][0]);
            literals.append(active_alternatives[0][0]);

            SmtSolver active_split_solver(SmtSolverConfiguration(
                0.01_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false));
            ExactBoxType domain({
                ExactIntervalType(-1,1),
                ExactIntervalType(-100,100)
            });
            SmtResult solve_result=active_split_solver.solve(
                aspace,domain,literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().sensitivity_guided_splits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().sensitivity_overrides_geometric_splits,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] forced splitting UNSAT: sin(x)=0 and cos(x)=0 on [0,7]");
            ExactBoxType domain({ExactIntervalType(0,7)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),sin(x[0]),ValidatedNumber(0)),
                ValidatedConstraint(ValidatedNumber(0),cos(x[0]),ValidatedNumber(0))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-stats] forced splitting processed="
                      << solve_result.statistics().boxes_processed
                      << " pruned=" << solve_result.statistics().boxes_pruned
                      << " split=" << solve_result.statistics().boxes_split);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_pruned>0u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().hull_reduction_rounds>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().shaving_reduction_rounds>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] split ignores wider inactive coordinate");
            auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.01_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false));
            ExactBoxType domain({
                ExactIntervalType(-1,1),
                ExactIntervalType(-10000,10000)
            });
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(
                    ValidatedNumber(0.3_pr),
                    sin(10*xy[0]),
                    ValidatedNumber(0.3_pr))
            });
            SmtResult solve_result=bounded_solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(not solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().dp_resolution_exhaustions,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().sensitivity_guided_splits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().sensitivity_overrides_geometric_splits,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] epsilon-active split ignores already certified wide constraint");
            auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
            SmtSolver active_split_solver(SmtSolverConfiguration(
                0.01_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false));
            ExactBoxType domain({
                ExactIntervalType(-1,1),
                ExactIntervalType(-100,100)
            });
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(
                    ValidatedNumber(-100.0_x),
                    xy[1],
                    ValidatedNumber(100.0_x)),
                ValidatedConstraint(
                    ValidatedNumber(0.3_pr),
                    sin(10*xy[0]),
                    ValidatedNumber(0.3_pr))
            });
            SmtResult solve_result=active_split_solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().sensitivity_guided_splits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().sensitivity_overrides_geometric_splits,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] sensitivity-guided split is exercised");
            auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
            SmtSolver split_solver(SmtSolverConfiguration(
                0.01_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false));
            ExactBoxType domain({
                ExactIntervalType(-1,1),
                ExactIntervalType(-10000,10000)
            });
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(
                    ValidatedNumber(0.3_pr),
                    sin(10*xy[0])+0.000001_pr*xy[1],
                    ValidatedNumber(0.3_pr))
            });
            SmtResult solve_result=split_solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().sensitivity_guided_splits,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] interior-point candidate search on 7D epsilon-SAT");
            auto coordinates=ValidatedScalarMultivariateFunction::coordinates(7);
            ValidatedScalarMultivariateFunction sum=coordinates[0];
            for(SizeType i=1u; i!=7u; ++i) {
                sum=sum+coordinates[i];
            }
            ExactBoxType domain({
                ExactIntervalType(0,1),ExactIntervalType(0,1),
                ExactIntervalType(0,1),ExactIntervalType(0,1),
                ExactIntervalType(0,1),ExactIntervalType(0,1),
                ExactIntervalType(0,1)
            });
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(1.3_pr),sum,ValidatedNumber(1.3_pr))
            });
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_successes,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] empty constraint list ignores zero box budget");
            SmtSolver zero_budget_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            ExactBoxType domain({ExactIntervalType(-1,1)});
            List<ValidatedConstraint> constraints;
            SmtResult solve_result=zero_budget_solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] empty constraint list: bounded nonempty domain is EPSILON_SAT");
            ExactBoxType domain({ExactIntervalType(-1,1)});
            List<ValidatedConstraint> constraints;
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] empty domain is UNSAT");
            ExactBoxType domain({ExactIntervalType::empty_interval()});
            List<ValidatedConstraint> constraints;
            SmtResult solve_result=solver.solve(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] non-splittable uncertified singleton returns precision UNKNOWN");
            auto sx=ValidatedScalarMultivariateFunction::coordinates(1);
            SmtSolver tiny_epsilon_solver(SmtSolverConfiguration(
                1e-30_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false));
            ValidatedScalarMultivariateFunction residual=
                sqr(sin(sx[0]))+sqr(cos(sx[0]))-1;
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),residual,ValidatedNumber(0))
            });
            SmtResult solve_result=tiny_epsilon_solver.solve(
                ExactBoxType({ExactIntervalType(1,1)}),constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
            ARIADNE_TESTING_PROVE(not solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().dp_resolution_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().non_splittable_uncertified_boxes,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] terminal box skips interior-point candidate search");
            auto sx=ValidatedScalarMultivariateFunction::coordinates(1);
            SmtSolver tiny_epsilon_solver(SmtSolverConfiguration(1e-30_pr));
            ValidatedScalarMultivariateFunction residual=
                sqr(sin(sx[0]))+sqr(cos(sx[0]))-1;
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),residual,ValidatedNumber(0))
            });
            SmtResult solve_result=tiny_epsilon_solver.solve(
                ExactBoxType({ExactIntervalType(1,1)}),constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
            ARIADNE_TESTING_PROVE(not solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().dp_resolution_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_successes,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().non_splittable_uncertified_boxes,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] reject constraint dimension mismatch");
            auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),xy[0],ValidatedNumber(1))
            });
            ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve(domain,constraints));
        }

        {
            ARIADNE_TESTING_NOTE("[smt-solve] reject unbounded domain");
            ExactBoxType domain({ExactIntervalType(-infty,+infty)});
            List<ValidatedConstraint> constraints;
            ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, solver.solve(domain,constraints));
        }
    }

    Void test_geometric_validated_constraint_split() {
        ARIADNE_TESTING_NOTE("[smt-geometric] validated constraint uses geometric split");
        RealVariable gx("geometric_constraint_x");
        RealSpace space({gx});
        List<ValidatedScalarMultivariateFunction> coordinates=
            ValidatedScalarMultivariateFunction::coordinates(1u);
        ValidatedScalarMultivariateFunction function=coordinates[0];
        List<ValidatedConstraint> constraints({
            ValidatedConstraint(
                ExactNumber(-0.0625_x),
                function,
                ExactNumber(0.0625_x))
        });
        SmtSolver solver(SmtSolverConfiguration(
            0.125_x,
            std::numeric_limits<SizeType>::max(),
            std::numeric_limits<SizeType>::max(),
            1u,
            false,
            false,
            false,
            false,
            false,
            false));
        SmtResult solve_result=solver.solve(
            ExactBoxType({ExactIntervalType(-0.25_x,0.25_x)}),
            constraints);
        ARIADNE_TESTING_PROVE(solve_result.is_unknown());
        ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
        ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().sensitivity_guided_splits,0u);
    }

    Void test_theory_solve() {
        RealVariable x("x");
        RealExpression ex=x;
        RealSpace space({x});
        SmtSolver solver(SmtSolverConfiguration(0.125_x));

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] empty domain is UNSAT");
            List<SmtTheoryPrimitiveLiteral> literals;
            SmtResult solve_result=solver.solve(
                space,
                ExactBoxType({ExactIntervalType::empty_interval()}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        auto primitive = [&](ContinuousPredicate const& predicate) {
            auto alternatives=normalize_smt_theory_literal(make_smt_theory_literal(predicate));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            return alternatives[0][0];
        };

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] empty primitive list ignores zero box budget");
            SmtSolver zero_budget_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            List<SmtTheoryPrimitiveLiteral> literals;
            SmtResult solve_result=zero_budget_solver.solve(
                space,
                ExactBoxType({ExactIntervalType(-1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] simplified zero primitive ignores zero box budget");
            RealVariable zero_x("zero_x");
            RealExpression zero_ex=zero_x;
            RealSpace zero_space({zero_x});
            SmtSolver zero_budget_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u,
                false));
            RealExpression residual=sin(zero_ex)-sin(zero_ex);
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(residual>0));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=zero_budget_solver.solve(
                zero_space,
                ExactBoxType({ExactIntervalType(1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] zero box budget propagates UNKNOWN");
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            List<SmtTheoryPrimitiveLiteral> literals({primitive(ex==0)});
            SmtResult solve_result=bounded_solver.solve(
                space,
                ExactBoxType({ExactIntervalType(0,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::RESOURCE_EXHAUSTED);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().non_splittable_uncertified_boxes,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] DP terminal precision limit returns precision UNKNOWN");
            SmtSolver tiny_epsilon_solver(SmtSolverConfiguration(1e-30_pr));
            RealExpression residual=sqr(sin(ex))+sqr(cos(ex))-1;
            List<SmtTheoryPrimitiveLiteral> literals({primitive(residual==0)});
            SmtResult solve_result=tiny_epsilon_solver.solve(
                space,ExactBoxType({ExactIntervalType(1,1)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
            ARIADNE_TESTING_PROVE(not solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().dp_resolution_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().non_splittable_uncertified_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().non_splittable_epsilon_overlap_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().epsilon_box_certifications,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().candidate_witness_searches,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] shaving proves dependency-hidden strict UNSAT");
            List<SmtTheoryPrimitiveLiteral> literals({
                primitive(ex*(1-ex)>0.32_pr)
            });
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().shaving_reduction_rounds>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] later hull reduction invalidates earlier strict literal");
            List<SmtTheoryPrimitiveLiteral> literals({
                primitive(sin(ex)>0),
                primitive(ex==4)
            });
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,7)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().hull_effective_reductions>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] strict epsilon predicate rejects negative point");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(ex>0)});
            ARIADNE_TESTING_PROVE(
                not SmtSolverTestSupport::epsilon_satisfied(
                    solver,
                    space,
                    UpperBoxType({UpperIntervalType(ExactIntervalType(-0.25_x,-0.25_x))}),
                    literals));
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] whole-box epsilon relation semantics");
            List<SmtTheoryPrimitiveLiteral> equality({primitive(ex==0)});
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::epsilon_satisfied(
                    solver,
                    space,
                    UpperBoxType({UpperIntervalType(ExactIntervalType(0,0.0625_x))}),
                    equality));
            ARIADNE_TESTING_PROVE(
                not SmtSolverTestSupport::epsilon_satisfied(
                    solver,
                    space,
                    UpperBoxType({UpperIntervalType(ExactIntervalType(0,0.25_x))}),
                    equality));
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::epsilon_satisfied(
                    solver,
                    space,
                    UpperBoxType({UpperIntervalType(ExactIntervalType(-0.125_x,0.125_x))}),
                    equality));

            List<SmtTheoryPrimitiveLiteral> nonstrict({primitive(ex>=0)});
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::epsilon_satisfied(
                    solver,
                    space,
                    UpperBoxType({UpperIntervalType(ExactIntervalType(-0.0625_x,1))}),
                    nonstrict));

            List<SmtTheoryPrimitiveLiteral> strict({primitive(ex>0)});
            ARIADNE_TESTING_PROVE(
                SmtSolverTestSupport::epsilon_satisfied(
                    solver,
                    space,
                    UpperBoxType({UpperIntervalType(ExactIntervalType(-0.0625_x,1))}),
                    strict));
            ARIADNE_TESTING_PROVE(
                not SmtSolverTestSupport::epsilon_satisfied(
                    solver,
                    space,
                    UpperBoxType({UpperIntervalType(ExactIntervalType(-0.125_x,1))}),
                    strict));
        }


        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] simplify repeated expression before interval solving");
            RealVariable singleton_x("singleton_x");
            RealExpression singleton_ex=singleton_x;
            RealSpace singleton_space({singleton_x});
            SmtSolver tiny_epsilon_solver(SmtSolverConfiguration(
                1e-30_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false));
            RealExpression residual=sin(singleton_ex)-sin(singleton_ex);
            ARIADNE_TESTING_PROVE(identical(simplify(residual),RealExpression(0)));
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(residual==0));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=tiny_epsilon_solver.solve(
                singleton_space,
                ExactBoxType({ExactIntervalType(1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] EQ at epsilon boundary: x=0 weakened on x=0.125");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(ex==0)});
            SmtResult solve_result=solver.solve(space,ExactBoxType({ExactIntervalType(0.125_x,0.125_x)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat() || solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] EQ outside epsilon: x=0 weakened on x=0.25");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(ex==0)});
            SmtResult solve_result=solver.solve(space,ExactBoxType({ExactIntervalType(0.25_x,0.25_x)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] GEQ at epsilon boundary: x>=0 weakened on x=-0.125");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(ex>=0)});
            SmtResult solve_result=solver.solve(space,ExactBoxType({ExactIntervalType(-0.125_x,-0.125_x)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat() || solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] GT rejects epsilon boundary: x>0 weakened on x=-0.125");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(ex>0)});
            SmtResult solve_result=solver.solve(space,ExactBoxType({ExactIntervalType(-0.125_x,-0.125_x)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] GT accepts strict interior: x>0 weakened on x=-0.0625");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(ex>0)});
            SmtResult solve_result=solver.solve(space,ExactBoxType({ExactIntervalType(-0.0625_x,-0.0625_x)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat() || solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] whole-box epsilon certification");
            RealVariable box_x("box_x");
            RealSpace box_space({box_x});
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(RealExpression(box_x)==0));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=solver.solve(
                box_space,
                ExactBoxType({ExactIntervalType(0,0.0625_x)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().epsilon_box_certifications,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] contractor fixpoint closes chained UNSAT at root");
            RealVariable y("y");
            RealExpression ey=y;
            RealSpace xy_space({x,y});
            auto xy_primitive = [&](ContinuousPredicate const& predicate) {
                auto alternatives=normalize_smt_theory_literal(make_smt_theory_literal(predicate));
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
                return alternatives[0][0];
            };
            List<SmtTheoryPrimitiveLiteral> literals({
                xy_primitive(ex-ey==0),
                xy_primitive(ey==0),
                xy_primitive(ex==1)
            });
            SmtResult solve_result=solver.solve(
                xy_space,
                ExactBoxType({ExactIntervalType(0,1),ExactIntervalType(0,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] shaving contractor handles repeated nonlinear occurrence");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(sqr(ex)+ex==0.75_x)});
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(-2,2)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_PROVE(solve_result.statistics().hull_reduction_rounds>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().shaving_reduction_rounds>=1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().hull_effective_reductions
                <= solve_result.statistics().hull_reduction_rounds);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().shaving_effective_reductions
                <= solve_result.statistics().shaving_reduction_rounds);
            ARIADNE_TESTING_NOTE("[smt-icp-stats] hull="
                      << solve_result.statistics().hull_effective_reductions
                      << "/" << solve_result.statistics().hull_reduction_rounds
                      << " shaving="
                      << solve_result.statistics().shaving_effective_reductions
                      << "/" << solve_result.statistics().shaving_reduction_rounds);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] transcendental GT: sin(x)>0 on [3,4]");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(sin(ex)>0)});
            SmtResult solve_result=solver.solve(space,ExactBoxType({ExactIntervalType(3,4)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] strict GT rejects zero-only image");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(sqr(ex)>0)});
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,0)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_pruned,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] endpoint witness avoids split for x^2=4 on [-2,2]");
            List<SmtTheoryPrimitiveLiteral> literals({primitive(sqr(ex)==4)});
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(-2,2)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] mixed-corner witness avoids split for x*y=-1");
            RealVariable y("y");
            RealExpression ey=y;
            RealSpace xy_space({x,y});
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(ex*ey==-1));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=solver.solve(
                xy_space,
                ExactBoxType({ExactIntervalType(-1,1),ExactIntervalType(-1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] cover supported RealExpression operations");

            auto expect_status = [&](String const& label,
                                     ExactIntervalType const& interval,
                                     ContinuousPredicate const& predicate,
                                     SmtResultStatus expected) {
                ARIADNE_TESTING_NOTE("[smt-real-op] " << label);
                List<SmtTheoryPrimitiveLiteral> literals({primitive(predicate)});
                SmtResult solve_result=solver.solve(space,ExactBoxType({interval}),literals);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.status(),expected);
            };

            expect_status("neg SAT",ExactIntervalType(1,1),neg(ex)==-1,SmtResultStatus::EPSILON_SAT);
            expect_status("neg UNSAT",ExactIntervalType(1,1),neg(ex)==1,SmtResultStatus::UNSAT);

            expect_status("sqr SAT",ExactIntervalType(2,2),sqr(ex)==4,SmtResultStatus::EPSILON_SAT);
            expect_status("sqr UNSAT",ExactIntervalType(2,2),sqr(ex)==5,SmtResultStatus::UNSAT);
            {
                ARIADNE_TESTING_NOTE("[smt-real-op] sqr epsilon-overlap delta-decision");
                auto alternatives=normalize_smt_theory_literal(
                    make_smt_theory_literal(sqr(ex)==4.0625_x));
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
                List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
                SmtResult solve_result=solver.solve(
                    space,ExactBoxType({ExactIntervalType(2,2)}),literals);
                ARIADNE_TESTING_PROVE(solve_result.is_unsat() || solve_result.is_epsilon_sat());
                ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
            }

            expect_status("pow SAT",ExactIntervalType(2,2),pow(ex,3)==8,SmtResultStatus::EPSILON_SAT);
            expect_status("pow UNSAT",ExactIntervalType(2,2),pow(ex,3)==9,SmtResultStatus::UNSAT);

            expect_status("rec SAT",ExactIntervalType(2,2),rec(ex)==0.5_x,SmtResultStatus::EPSILON_SAT);
            expect_status("rec UNSAT",ExactIntervalType(2,2),rec(ex)==1,SmtResultStatus::UNSAT);

            expect_status("sqrt SAT",ExactIntervalType(4,4),sqrt(ex)==2,SmtResultStatus::EPSILON_SAT);
            expect_status("sqrt UNSAT",ExactIntervalType(4,4),sqrt(ex)==3,SmtResultStatus::UNSAT);

            expect_status("exp SAT",ExactIntervalType(0,0),exp(ex)==1,SmtResultStatus::EPSILON_SAT);
            expect_status("exp UNSAT",ExactIntervalType(0,0),exp(ex)==2,SmtResultStatus::UNSAT);

            expect_status("log SAT",ExactIntervalType(1,1),log(ex)==0,SmtResultStatus::EPSILON_SAT);
            expect_status("log UNSAT",ExactIntervalType(1,1),log(ex)==1,SmtResultStatus::UNSAT);

            expect_status("sin SAT",ExactIntervalType(0,0),sin(ex)==0,SmtResultStatus::EPSILON_SAT);
            expect_status("sin UNSAT",ExactIntervalType(0,0),sin(ex)==1,SmtResultStatus::UNSAT);

            expect_status("cos SAT",ExactIntervalType(0,0),cos(ex)==1,SmtResultStatus::EPSILON_SAT);
            expect_status("cos UNSAT",ExactIntervalType(0,0),cos(ex)==0,SmtResultStatus::UNSAT);

            expect_status("tan SAT",ExactIntervalType(0,0),tan(ex)==0,SmtResultStatus::EPSILON_SAT);
            expect_status("tan UNSAT",ExactIntervalType(0,0),tan(ex)==1,SmtResultStatus::UNSAT);

            expect_status("asin SAT",ExactIntervalType(0,0),asin(ex)==0,SmtResultStatus::EPSILON_SAT);
            expect_status("asin UNSAT",ExactIntervalType(0,0),asin(ex)==1,SmtResultStatus::UNSAT);

            expect_status("acos SAT",ExactIntervalType(1,1),acos(ex)==0,SmtResultStatus::EPSILON_SAT);
            expect_status("acos UNSAT",ExactIntervalType(1,1),acos(ex)==1,SmtResultStatus::UNSAT);

            expect_status("atan SAT",ExactIntervalType(0,0),atan(ex)==0,SmtResultStatus::EPSILON_SAT);
            expect_status("atan UNSAT",ExactIntervalType(0,0),atan(ex)==1,SmtResultStatus::UNSAT);

            expect_status("max SAT",ExactIntervalType(-1,-1),max(ex,RealExpression(0))==0,SmtResultStatus::EPSILON_SAT);
            expect_status("max UNSAT",ExactIntervalType(-1,-1),max(ex,RealExpression(0))==1,SmtResultStatus::UNSAT);

            expect_status("min SAT",ExactIntervalType(1,1),min(ex,RealExpression(0))==0,SmtResultStatus::EPSILON_SAT);
            expect_status("min UNSAT",ExactIntervalType(1,1),min(ex,RealExpression(0))==1,SmtResultStatus::UNSAT);

            expect_status("abs SAT",ExactIntervalType(-1,-1),abs(ex)==1,SmtResultStatus::EPSILON_SAT);
            expect_status("abs UNSAT",ExactIntervalType(-1,-1),abs(ex)==0,SmtResultStatus::UNSAT);

            expect_status("nul SAT",ExactIntervalType(2,2),nul(ex)==0,SmtResultStatus::EPSILON_SAT);
            expect_status("nul UNSAT",ExactIntervalType(2,2),nul(ex)==1,SmtResultStatus::UNSAT);

            expect_status("pos SAT",ExactIntervalType(2,2),pos(ex)==2,SmtResultStatus::EPSILON_SAT);
            expect_status("pos UNSAT",ExactIntervalType(2,2),pos(ex)==3,SmtResultStatus::UNSAT);

            expect_status("hlf SAT",ExactIntervalType(2,2),hlf(ex)==1,SmtResultStatus::EPSILON_SAT);
            expect_status("hlf UNSAT",ExactIntervalType(2,2),hlf(ex)==2,SmtResultStatus::UNSAT);

            expect_status("add SAT",ExactIntervalType(2,2),add(ex,RealExpression(3))==5,SmtResultStatus::EPSILON_SAT);
            expect_status("add UNSAT",ExactIntervalType(2,2),add(ex,RealExpression(3))==6,SmtResultStatus::UNSAT);

            expect_status("sub SAT",ExactIntervalType(2,2),sub(ex,RealExpression(3))==-1,SmtResultStatus::EPSILON_SAT);
            expect_status("sub UNSAT",ExactIntervalType(2,2),sub(ex,RealExpression(3))==0,SmtResultStatus::UNSAT);

            expect_status("mul SAT",ExactIntervalType(2,2),mul(ex,RealExpression(3))==6,SmtResultStatus::EPSILON_SAT);
            expect_status("mul UNSAT",ExactIntervalType(2,2),mul(ex,RealExpression(3))==7,SmtResultStatus::UNSAT);

            expect_status("div SAT",ExactIntervalType(6,6),div(ex,RealExpression(3))==2,SmtResultStatus::EPSILON_SAT);
            expect_status("div UNSAT",ExactIntervalType(6,6),div(ex,RealExpression(3))==3,SmtResultStatus::UNSAT);

            expect_status("operator add SAT",ExactIntervalType(2,2),(ex+RealExpression(3))==5,SmtResultStatus::EPSILON_SAT);
            expect_status("operator sub SAT",ExactIntervalType(2,2),(ex-RealExpression(3))==-1,SmtResultStatus::EPSILON_SAT);
            expect_status("operator mul SAT",ExactIntervalType(2,2),(ex*RealExpression(3))==6,SmtResultStatus::EPSILON_SAT);
            expect_status("operator div SAT",ExactIntervalType(6,6),(ex/RealExpression(3))==2,SmtResultStatus::EPSILON_SAT);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] cover binary RealExpression operations");
            RealVariable y("y");
            RealExpression ey=y;
            RealSpace xy_space({x,y});

            auto xy_primitive = [&](ContinuousPredicate const& predicate) {
                auto alternatives=normalize_smt_theory_literal(make_smt_theory_literal(predicate));
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
                return alternatives[0][0];
            };

            auto expect_xy_status = [&](String const& label,
                                        ExactIntervalType const& x_interval,
                                        ExactIntervalType const& y_interval,
                                        ContinuousPredicate const& predicate,
                                        SmtResultStatus expected) {
                ARIADNE_TESTING_NOTE("[smt-real-binary-op] " << label);
                List<SmtTheoryPrimitiveLiteral> literals({xy_primitive(predicate)});
                SmtResult solve_result=solver.solve(
                    xy_space,ExactBoxType({x_interval,y_interval}),literals);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.status(),expected);
            };

            expect_xy_status("add SAT",ExactIntervalType(2,2),ExactIntervalType(3,3),ex+ey==5,SmtResultStatus::EPSILON_SAT);
            expect_xy_status("add UNSAT",ExactIntervalType(2,2),ExactIntervalType(3,3),ex+ey==6,SmtResultStatus::UNSAT);

            expect_xy_status("sub SAT",ExactIntervalType(2,2),ExactIntervalType(3,3),ex-ey==-1,SmtResultStatus::EPSILON_SAT);
            expect_xy_status("sub UNSAT",ExactIntervalType(2,2),ExactIntervalType(3,3),ex-ey==0,SmtResultStatus::UNSAT);

            expect_xy_status("mul SAT",ExactIntervalType(2,2),ExactIntervalType(3,3),ex*ey==6,SmtResultStatus::EPSILON_SAT);
            expect_xy_status("mul UNSAT",ExactIntervalType(2,2),ExactIntervalType(3,3),ex*ey==7,SmtResultStatus::UNSAT);

            expect_xy_status("div SAT",ExactIntervalType(6,6),ExactIntervalType(3,3),ex/ey==2,SmtResultStatus::EPSILON_SAT);
            expect_xy_status("div UNSAT",ExactIntervalType(6,6),ExactIntervalType(3,3),ex/ey==3,SmtResultStatus::UNSAT);

            expect_xy_status("max left SAT",ExactIntervalType(3,3),ExactIntervalType(2,2),max(ex,ey)==3,SmtResultStatus::EPSILON_SAT);
            expect_xy_status("max right SAT",ExactIntervalType(2,2),ExactIntervalType(3,3),max(ex,ey)==3,SmtResultStatus::EPSILON_SAT);
            expect_xy_status("max UNSAT",ExactIntervalType(2,2),ExactIntervalType(3,3),max(ex,ey)==2,SmtResultStatus::UNSAT);

            expect_xy_status("min left SAT",ExactIntervalType(2,2),ExactIntervalType(3,3),min(ex,ey)==2,SmtResultStatus::EPSILON_SAT);
            expect_xy_status("min right SAT",ExactIntervalType(3,3),ExactIntervalType(2,2),min(ex,ey)==2,SmtResultStatus::EPSILON_SAT);
            expect_xy_status("min UNSAT",ExactIntervalType(2,2),ExactIntervalType(3,3),min(ex,ey)==3,SmtResultStatus::UNSAT);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] cover RealExpression domain edge cases");

            auto expect_edge_status = [&](String const& label,
                                          ExactIntervalType const& interval,
                                          ContinuousPredicate const& predicate,
                                          SmtResultStatus expected) {
                ARIADNE_TESTING_NOTE("[smt-real-domain] " << label);
                List<SmtTheoryPrimitiveLiteral> literals({primitive(predicate)});
                SmtResult solve_result=solver.solve(space,ExactBoxType({interval}),literals);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.status(),expected);
            };

            expect_edge_status("sqrt negative domain",ExactIntervalType(-1,-1),sqrt(ex)==0,SmtResultStatus::UNSAT);
            expect_edge_status("sqrt zero boundary",ExactIntervalType(0,0),sqrt(ex)==0,SmtResultStatus::EPSILON_SAT);

            expect_edge_status("log negative domain",ExactIntervalType(-1,-1),log(ex)==0,SmtResultStatus::UNSAT);
            expect_edge_status("log zero domain",ExactIntervalType(0,0),log(ex)==0,SmtResultStatus::UNSAT);

            expect_edge_status("asin below domain",ExactIntervalType(-2,-2),asin(ex)==0,SmtResultStatus::UNSAT);
            expect_edge_status("asin above domain",ExactIntervalType(2,2),asin(ex)==0,SmtResultStatus::UNSAT);
            expect_edge_status("acos below domain",ExactIntervalType(-2,-2),acos(ex)==0,SmtResultStatus::UNSAT);
            expect_edge_status("acos above domain",ExactIntervalType(2,2),acos(ex)==0,SmtResultStatus::UNSAT);

            expect_edge_status("rec positive near zero",ExactIntervalType(0.5_x,0.5_x),rec(ex)==2,SmtResultStatus::EPSILON_SAT);
            expect_edge_status("rec negative",ExactIntervalType(-1,-1),rec(ex)==-1,SmtResultStatus::EPSILON_SAT);
            expect_edge_status("rec singleton zero undefined",ExactIntervalType(0,0),rec(ex)==0,SmtResultStatus::UNSAT);

            expect_edge_status("tan regular branch",ExactIntervalType(0,0),tan(ex)==0,SmtResultStatus::EPSILON_SAT);

            RealVariable y("y");
            RealExpression ey=y;
            RealSpace xy_space({x,y});
            auto xy_primitive = [&](ContinuousPredicate const& predicate) {
                auto alternatives=normalize_smt_theory_literal(make_smt_theory_literal(predicate));
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
                return alternatives[0][0];
            };
            {
                ARIADNE_TESTING_NOTE("[smt-real-domain] division singleton zero denominator");
                List<SmtTheoryPrimitiveLiteral> literals({xy_primitive(ex/ey==1)});
                SmtResult solve_result=solver.solve(
                    xy_space,
                    ExactBoxType({ExactIntervalType(1,1),ExactIntervalType(0,0)}),
                    literals);
                ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            }
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] split ignores wider inactive coordinate");
            RealVariable y("y");
            RealSpace xy_space({x,y});
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.01_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false));
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(sin(10*ex)==0.3_pr));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=bounded_solver.solve(
                xy_space,
                ExactBoxType({ExactIntervalType(-1,1),ExactIntervalType(-10000,10000)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().sensitivity_guided_splits,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().sensitivity_overrides_geometric_splits,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] sensitivity-guided split is exercised");
            RealVariable y("y");
            RealExpression ey=y;
            RealSpace xy_space({x,y});
            SmtSolver split_solver(SmtSolverConfiguration(
                0.01_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false));
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(sin(10*ex)+0.000001_pr*ey==0.3_pr));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=split_solver.solve(
                xy_space,
                ExactBoxType({ExactIntervalType(-1,1),ExactIntervalType(-10000,10000)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().sensitivity_guided_splits,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] non-differentiable sensitivity falls back to geometry");
            SmtSolver split_solver(SmtSolverConfiguration(
                0.01_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,false,true,false,false,false));
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    abs(ex)-0.3_pr,SmtTheoryPrimitiveRelation::EQ_ZERO)
            });
            SmtResult solve_result=split_solver.solve(
                space,
                ExactBoxType({ExactIntervalType(-1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().sensitivity_guided_splits,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] interior-point candidate search on 7D epsilon-SAT");
            RealVariable x0("x0"); RealVariable x1("x1"); RealVariable x2("x2");
            RealVariable x3("x3"); RealVariable x4("x4"); RealVariable x5("x5");
            RealVariable x6("x6");
            RealSpace seven_space({x0,x1,x2,x3,x4,x5,x6});
            RealExpression sum=
                RealExpression(x0)+RealExpression(x1)+RealExpression(x2)
                +RealExpression(x3)+RealExpression(x4)+RealExpression(x5)
                +RealExpression(x6);
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(sum==1.3_pr));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=solver.solve(
                seven_space,
                ExactBoxType({
                    ExactIntervalType(0,1),ExactIntervalType(0,1),
                    ExactIntervalType(0,1),ExactIntervalType(0,1),
                    ExactIntervalType(0,1),ExactIntervalType(0,1),
                    ExactIntervalType(0,1)
                }),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_successes,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-theory-solve] parallel/sequential agreement for strict primitive");
            auto& thread_manager=ThreadManager::instance();
            ConcurrencyGuard concurrency_guard(thread_manager);
            SizeType parallel_concurrency=thread_manager.maximum_concurrency()>=2u ? 2u : thread_manager.maximum_concurrency();
            if(parallel_concurrency>0u) {
                List<SmtTheoryPrimitiveLiteral> literals({primitive(sin(ex)>0)});
                ExactBoxType domain({ExactIntervalType(3,4)});
                thread_manager.set_concurrency(0);
                SmtResult sequential=solver.solve(space,domain,literals);
                thread_manager.set_concurrency(parallel_concurrency);
                SmtResult parallel=solver.solve_parallel(space,domain,literals);
                ARIADNE_TESTING_EXPECT_EQUAL(sequential.status(),parallel.status());
                ARIADNE_TESTING_PROVE(sequential.has_witness()==parallel.has_witness());
            }
        }
    }

    Void test_interval_newton_adaptive_retry() {
        auto make_solver=[](SizeType box_limit) {
            return SmtSolver(SmtSolverConfiguration(
                1e-5_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                box_limit,
                false,
                false,
                false,
                false,
                true,
                true,
                false,
                false,
                true));
        };

        {
            ARIADNE_TESTING_NOTE("[smt-newton] eager effective Newton does not stage");
            RealVariable x0("newton_retry_3d_x0");
            RealVariable x1("newton_retry_3d_x1");
            RealVariable x2("newton_retry_3d_x2");
            RealExpression e0=x0, e1=x1, e2=x2;
            RealSpace space({x0,x1,x2});
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    e0*e1-0.12_pr,
                    SmtTheoryPrimitiveRelation::EQ_ZERO),
                SmtTheoryPrimitiveLiteral(
                    e1*e2-0.15_pr,
                    SmtTheoryPrimitiveRelation::EQ_ZERO),
                SmtTheoryPrimitiveLiteral(
                    e0+e1+e2-1.2_pr,
                    SmtTheoryPrimitiveRelation::EQ_ZERO)
            });

            SmtResult solve_result=make_solver(16384u).solve(
                space,
                ExactBoxType({
                    ExactIntervalType(0.25_x,0.55_pr),
                    ExactIntervalType(0.2_pr,0.4_pr),
                    ExactIntervalType(0.4_pr,0.6_pr)
                }),
                literals);

            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_attempts,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_effective_reductions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_infeasible,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_singular,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-newton] inconsistent Newton image proves infeasibility");
            RealVariable x0("newton_infeasible_x");
            RealExpression e0=x0;
            RealSpace space({x0});
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    e0-2,SmtTheoryPrimitiveRelation::EQ_ZERO)
            });
            SmtResult solve_result=make_solver(16u).solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_infeasible,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-newton] singular Newton subsystem falls back to contractors");
            RealVariable x0("newton_singular_x");
            RealExpression e0=x0;
            RealSpace space({x0});
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    sqr(e0),SmtTheoryPrimitiveRelation::EQ_ZERO)
            });
            SmtResult solve_result=make_solver(16u).solve(
                space,ExactBoxType({ExactIntervalType(-1,1)}),literals);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().interval_newton_singular>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-newton] staged hull sweep can prove infeasibility");
            RealVariable x0("newton_hull_infeasible_x");
            RealExpression e0=x0;
            RealSpace space({x0});
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    e0,SmtTheoryPrimitiveRelation::EQ_ZERO),
                SmtTheoryPrimitiveLiteral(
                    e0-1,SmtTheoryPrimitiveRelation::GEQ_ZERO)
            });
            SmtResult solve_result=make_solver(16u).solve(
                space,ExactBoxType({ExactIntervalType(0,0)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_attempts,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_effective_reductions,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_infeasible,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-newton] ineffective eager Newton stages one hull sweep and retries");
            RealVariable x0("newton_retry_2d_x0");
            RealVariable x1("newton_retry_2d_x1");
            RealExpression e0=x0, e1=x1;
            RealSpace space({x0,x1});
            List<SmtTheoryPrimitiveLiteral> literals({
                SmtTheoryPrimitiveLiteral(
                    e0*e1-0.12_pr,
                    SmtTheoryPrimitiveRelation::EQ_ZERO),
                SmtTheoryPrimitiveLiteral(
                    e0+e1-0.7_pr,
                    SmtTheoryPrimitiveRelation::EQ_ZERO)
            });

            SmtResult solve_result=make_solver(4096u).solve(
                space,
                ExactBoxType({
                    ExactIntervalType(0.36_pr,0.8_pr),
                    ExactIntervalType(0.15_pr,0.34_pr)
                }),
                literals);

            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_attempts,2u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_effective_reductions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_infeasible,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_singular,0u);
        }
    }

    Void test_boolean_theory_solve() {
        RealVariable x("x");
        RealExpression ex=x;
        RealSpace space({x});
        SmtSolver solver(SmtSolverConfiguration(0.125_x));

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] symbolic simplification removes dependency before theory solving");
            RealExpression residual=sin(ex)-sin(ex);
            SmtResult solve_result=solver.solve(
                space,
                ExactBoxType({ExactIntervalType(1,1)}),
                residual==0);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] simplified zero theory atom ignores zero box budget");
            SmtSolver zero_budget_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u,
                false));
            RealExpression residual=sin(ex)-sin(ex);
            SmtResult solve_result=zero_budget_solver.solve(
                space,
                ExactBoxType({ExactIntervalType(1,1)}),
                residual>0);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_checks,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] Boolean theory solve preserves disabled candidate search");
            SmtSolver no_candidate_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false));
            ContinuousPredicate formula=(sqr(ex)==0.75_x);
            SmtResult solve_result=no_candidate_solver.solve(
                space,ExactBoxType({ExactIntervalType(-2,2)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_successes,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] Boolean theory solve preserves interval Newton");
            RealVariable y("newton_boolean_y");
            RealExpression ey=y;
            RealSpace newton_space({x,y});
            SmtSolver newton_solver(SmtSolverConfiguration(
                1e-5_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                true));
            ContinuousPredicate formula=
                ((sqr(ex)+sqr(ey)-1)==0) && ((ex-ey)==0);
            SmtResult solve_result=newton_solver.solve(
                newton_space,
                ExactBoxType({
                    ExactIntervalType(0.5_x,1.0_x),
                    ExactIntervalType(0.5_x,1.0_x)
                }),
                formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()
                ==SmtUnknownReason::RESOURCE_EXHAUSTED);
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_checks>=1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_attempts,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_effective_reductions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_infeasible,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().interval_newton_singular,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] unit propagation on single atom");
            ContinuousPredicate formula=(ex>=0);
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] decisions="
                      << solve_result.statistics().boolean_decisions
                      << " propagations=" << solve_result.statistics().boolean_propagations
                      << " reasoned=" << solve_result.statistics().boolean_reasoned_propagations
                      << " conflicts=" << solve_result.statistics().boolean_conflicts
                      << " theory_checks=" << solve_result.statistics().theory_checks
                      << " theory_conflicts=" << solve_result.statistics().theory_conflicts);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boolean_decisions,0u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boolean_propagations>=1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().boolean_reasoned_propagations,
                solve_result.statistics().boolean_propagations);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_checks,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] zero theory box budget still permits Boolean UNSAT");
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            ContinuousPredicate atom=(ex>=0);
            SmtResult solve_result=bounded_solver.solve(
                space,
                ExactBoxType({ExactIntervalType(-1,1)}),
                atom&&!atom);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_checks,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,0u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boolean_conflicts>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] zero global box budget stops before theory");
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            ContinuousPredicate formula=(ex>=0);
            SmtResult solve_result=bounded_solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_checks,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_conflicts,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_learned_clauses,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().non_splittable_uncertified_boxes,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] zero box budget propagates partial theory UNKNOWN");
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            // The required atom is assigned by unit propagation; the other
            // two atoms remain unassigned during the partial theory check.
            ContinuousPredicate forced_atom=(ex>=0);
            ContinuousPredicate free_branch=(ex>=-1)||(ex<=2);
            SmtResult solve_result=bounded_solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),
                forced_atom&&free_branch);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::RESOURCE_EXHAUSTED);
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_checks>=2u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().box_budget_exhaustions>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] one-box global budget permits one theory check");
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                1u));
            ContinuousPredicate formula=(ex>=0);
            SmtResult solve_result=bounded_solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(
                solve_result.is_epsilon_sat() || solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_checks>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_processed<=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] Boolean contradiction pruned before theory");
            ContinuousPredicate atom=(ex>=0);
            ContinuousPredicate formula=atom&&(!atom);
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] contradiction decisions="
                      << solve_result.statistics().boolean_decisions
                      << " propagations=" << solve_result.statistics().boolean_propagations
                      << " conflicts=" << solve_result.statistics().boolean_conflicts
                      << " theory_checks=" << solve_result.statistics().theory_checks);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boolean_conflicts>=1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_checks,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] partial theory conflict before free Boolean branch");
            ContinuousPredicate forced_conflict=(ex>=1)&&(ex<=0);
            ContinuousPredicate free_branch=(ex>=-1)||(ex<=2);
            ContinuousPredicate formula=forced_conflict&&free_branch;
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] partial conflict decisions="
                      << solve_result.statistics().boolean_decisions
                      << " propagations=" << solve_result.statistics().boolean_propagations
                      << " theory_checks=" << solve_result.statistics().theory_checks
                      << " theory_conflicts=" << solve_result.statistics().theory_conflicts
                      << " theory_learned=" << solve_result.statistics().theory_learned_clauses
                      << " theory_learned_literals="
                      << solve_result.statistics().theory_learned_clause_literals
                      << " minimization_checks="
                      << solve_result.statistics().theory_minimization_checks
                      << " raw_nogood_literals="
                      << solve_result.statistics().theory_nogood_raw_literals
                      << " minimized_nogood_literals="
                      << solve_result.statistics().theory_nogood_minimized_literals);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boolean_decisions,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_checks,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_conflicts,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_learned_clauses,1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_learned_clause_literals>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] minimize theory conflict nogood");
            ContinuousPredicate conflict=(ex>=1)&&(ex<=0);
            ContinuousPredicate irrelevant=(ex>=-100);
            ContinuousPredicate free_branch=(ex>=-2)||(ex<=2);
            ContinuousPredicate formula=conflict&&irrelevant&&free_branch;
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] minimization_checks="
                      << solve_result.statistics().theory_minimization_checks
                      << " raw=" << solve_result.statistics().theory_nogood_raw_literals
                      << " minimized="
                      << solve_result.statistics().theory_nogood_minimized_literals
                      << " removed="
                      << solve_result.statistics().theory_nogood_literals_removed);
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_minimization_checks>=1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().theory_nogood_raw_literals
                > solve_result.statistics().theory_nogood_minimized_literals);
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_nogood_literals_removed>=1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().theory_nogood_raw_literals
                    - solve_result.statistics().theory_nogood_minimized_literals,
                solve_result.statistics().theory_nogood_literals_removed);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] minimize theory conflict nogood with multiple irrelevant literals");
            ContinuousPredicate conflict=(ex>=1)&&(ex<=0);
            ContinuousPredicate irrelevant_lower=(ex>=-100);
            ContinuousPredicate irrelevant_upper=(ex<=100);
            ContinuousPredicate free_branch=(ex>=-2)||(ex<=2);
            ContinuousPredicate formula=
                conflict&&irrelevant_lower&&irrelevant_upper&&free_branch;
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] minimization_checks="
                      << solve_result.statistics().theory_minimization_checks
                      << " raw=" << solve_result.statistics().theory_nogood_raw_literals
                      << " minimized="
                      << solve_result.statistics().theory_nogood_minimized_literals
                      << " removed="
                      << solve_result.statistics().theory_nogood_literals_removed);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_nogood_raw_literals,4u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_nogood_minimized_literals,2u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_nogood_literals_removed,2u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_minimization_checks>=4u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] bound theory nogood minimization work");
            SmtSolver bounded_solver(SmtSolverConfiguration(0.125_x,1u));
            ContinuousPredicate conflict=(ex>=1)&&(ex<=0);
            ContinuousPredicate irrelevant_lower=(ex>=-100);
            ContinuousPredicate irrelevant_upper=(ex<=100);
            ContinuousPredicate free_branch=(ex>=-2)||(ex<=2);
            ContinuousPredicate formula=
                conflict&&irrelevant_lower&&irrelevant_upper&&free_branch;
            SmtResult solve_result=bounded_solver.solve(
                space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] budget=1 minimization_checks="
                      << solve_result.statistics().theory_minimization_checks
                      << " raw=" << solve_result.statistics().theory_nogood_raw_literals
                      << " minimized="
                      << solve_result.statistics().theory_nogood_minimized_literals
                      << " removed="
                      << solve_result.statistics().theory_nogood_literals_removed
                      << " budget_exhaustions="
                      << solve_result.statistics().theory_minimization_budget_exhaustions
                      << " first_candidate_trail_rank="
                      << solve_result.statistics().first_minimization_candidate_trail_rank);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_minimization_checks,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().theory_minimization_budget_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().theory_nogood_raw_literals,4u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().first_minimization_candidate_trail_rank>=1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().theory_nogood_minimized_literals>=2u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().theory_nogood_minimized_literals<=4u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] analyze Boolean conflict with 1-UIP");
            ContinuousPredicate a=(ex>=0);
            ContinuousPredicate b=(ex<=0);
            ContinuousPredicate formula=
                (a||b)&&(a||(!b))&&((!a)||b)&&((!a)||(!b));
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,0)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] analyzed="
                      << solve_result.statistics().boolean_conflicts_analyzed
                      << " learned_clauses=" << solve_result.statistics().learned_clauses
                      << " learned_literals_total=" << solve_result.statistics().learned_clause_literals
                      << " last_learned_literals=" << solve_result.statistics().last_learned_clause_literals
                      << " last_current_level_literals="
                      << solve_result.statistics().last_learned_current_level_literals
                      << " learned_propagations="
                      << solve_result.statistics().learned_clause_propagations
                      << " backjump_level=" << solve_result.statistics().last_backjump_level
                      << " nonchronological_backjumps="
                      << solve_result.statistics().nonchronological_backjumps
                      << " max_level=" << solve_result.statistics().max_decision_level);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boolean_conflicts_analyzed>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().learned_clauses>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().last_learned_clause_literals>=1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().last_learned_current_level_literals,1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().learned_clause_propagations>=1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().last_backjump_level
                < solve_result.statistics().max_decision_level);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] learned clause propagation after backjump");
            ContinuousPredicate a=(ex>=-2);
            ContinuousPredicate b=(ex>=-1);
            ContinuousPredicate c=(ex>=0);
            ContinuousPredicate formula=
                (a||b)&&(a||(!b))&&((!a)||c)&&((!a)||(!c));
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,0)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] learned="
                      << solve_result.statistics().learned_clauses
                      << " learned_propagations="
                      << solve_result.statistics().learned_clause_propagations
                      << " backtracks=" << solve_result.statistics().boolean_backtracks
                      << " max_level=" << solve_result.statistics().max_decision_level);
            ARIADNE_TESTING_PROVE(solve_result.statistics().learned_clauses>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().learned_clause_propagations>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] bounded learned database remains stable");
            SmtSolver pruning_solver(SmtSolverConfiguration(
                0.125_x,std::numeric_limits<SizeType>::max(),1u));
            ContinuousPredicate a=(ex>=0);
            ContinuousPredicate b=(ex<=0);
            ContinuousPredicate c=(ex==0);
            ContinuousPredicate formula=
                ( a|| b|| c)&&
                ( a|| b||(!c))&&
                ( a||(!b)|| c)&&
                ( a||(!b)||(!c))&&
                ((!a)|| b|| c)&&
                ((!a)|| b||(!c))&&
                ((!a)||(!b)|| c)&&
                ((!a)||(!b)||(!c));
            SmtResult solve_result=pruning_solver.solve(
                space,ExactBoxType({ExactIntervalType(-1,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] learned="
                      << solve_result.statistics().learned_clauses
                      << " activity_bumps="
                      << solve_result.statistics().learned_clause_activity_bumps
                      << " pruning_runs="
                      << solve_result.statistics().learned_clause_pruning_runs
                      << " pruned=" << solve_result.statistics().learned_clauses_pruned
                      << " peak_active="
                      << solve_result.statistics().peak_active_non_theory_learned_clauses);
            ARIADNE_TESTING_PROVE(solve_result.statistics().learned_clauses>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().learned_clause_activity_bumps>=1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().peak_active_non_theory_learned_clauses>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] conservative pruning preserves protected learned clauses");
            SmtSolver pruning_solver(SmtSolverConfiguration(
                0.125_x,std::numeric_limits<SizeType>::max(),1u));
            ContinuousPredicate a=(ex>=-0.75_x);
            ContinuousPredicate b=(ex>=-0.25_x);
            ContinuousPredicate c=(ex>=0.25_x);
            ContinuousPredicate d=(ex>=0.75_x);
            ContinuousPredicate formula=
                ( a|| b|| c|| d)&&
                ( a|| b|| c||(!d))&&
                ( a|| b||(!c)|| d)&&
                ( a|| b||(!c)||(!d))&&
                ( a||(!b)|| c|| d)&&
                ( a||(!b)|| c||(!d))&&
                ( a||(!b)||(!c)|| d)&&
                ( a||(!b)||(!c)||(!d))&&
                ((!a)|| b|| c|| d)&&
                ((!a)|| b|| c||(!d))&&
                ((!a)|| b||(!c)|| d)&&
                ((!a)|| b||(!c)||(!d))&&
                ((!a)||(!b)|| c|| d)&&
                ((!a)||(!b)|| c||(!d))&&
                ((!a)||(!b)||(!c)|| d)&&
                ((!a)||(!b)||(!c)||(!d));
            SmtResult solve_result=pruning_solver.solve(
                space,ExactBoxType({ExactIntervalType(-1,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] learned="
                      << solve_result.statistics().learned_clauses
                      << " activity_bumps="
                      << solve_result.statistics().learned_clause_activity_bumps
                      << " pruning_runs="
                      << solve_result.statistics().learned_clause_pruning_runs
                      << " pruned=" << solve_result.statistics().learned_clauses_pruned
                      << " peak_active="
                      << solve_result.statistics().peak_active_non_theory_learned_clauses);
            ARIADNE_TESTING_PROVE(solve_result.statistics().learned_clauses>=4u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().learned_clause_pruning_runs>=1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().learned_clauses_pruned,0u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().peak_active_non_theory_learned_clauses>=2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] semantically equivalent atoms share one Boolean variable");
            RealVariable y("y");
            RealExpression ey=y;
            RealSpace xy_space({x,y});
            ExactBoxType xy_domain({ExactIntervalType(-1,1),ExactIntervalType(-1,1)});

            SmtResult reversed_inequality=solver.solve(
                xy_space,xy_domain,(ex<=ey)&&!(ey>=ex));
            ARIADNE_TESTING_PROVE(reversed_inequality.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(reversed_inequality.statistics().theory_checks,0u);

            SmtResult sign_comparison=solver.solve(
                space,
                ExactBoxType({ExactIntervalType(-1,1)}),
                sgn(ex)&&!(ex>0));
            ARIADNE_TESTING_PROVE(sign_comparison.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(sign_comparison.statistics().theory_checks,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] structurally identical atoms share one Boolean variable");
            ContinuousPredicate first=(ex<=0);
            ContinuousPredicate second=(ex<=0);
            ARIADNE_TESTING_PROVE(first.node_raw_ptr()!=second.node_raw_ptr());

            SmtResult duplicate_atom_contradiction=solver.solve(
                space,
                ExactBoxType({ExactIntervalType(-1,1)}),
                first&&!second);
            ARIADNE_TESTING_PROVE(duplicate_atom_contradiction.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(duplicate_atom_contradiction.statistics().theory_checks,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] Boolean constant folding avoids theory work");
            ContinuousPredicate atom=(ex>=0);

            SmtResult folded_false=solver.solve(
                space,
                ExactBoxType({ExactIntervalType(-1,1)}),
                ContinuousPredicate(false)&&atom);
            ARIADNE_TESTING_PROVE(folded_false.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(folded_false.statistics().theory_checks,0u);

            SmtResult folded_true=solver.solve(
                space,
                ExactBoxType({ExactIntervalType(-1,1)}),
                ContinuousPredicate(true)||atom);
            ARIADNE_TESTING_PROVE(folded_true.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(folded_true.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(folded_true.statistics().theory_checks,0u);

            SmtResult folded_true_empty=solver.solve(
                space,
                ExactBoxType({ExactIntervalType::empty_interval()}),
                ContinuousPredicate(true)||atom);
            ARIADNE_TESTING_PROVE(folded_true_empty.is_unsat());
            ARIADNE_TESTING_EXPECT_EQUAL(folded_true_empty.statistics().theory_checks,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] Boolean constants");
            ExactBoxType domain({ExactIntervalType(-1,1)});

            SmtResult true_result=solver.solve(space,domain,ContinuousPredicate(true));
            ARIADNE_TESTING_PROVE(true_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(true_result.has_witness());

            SmtResult false_result=solver.solve(space,domain,ContinuousPredicate(false));
            ARIADNE_TESTING_PROVE(false_result.is_unsat());

            ContinuousPredicate atom=(ex>=0);
            SmtResult mixed_true=solver.solve(
                space,domain,ContinuousPredicate(true)&&atom);
            ARIADNE_TESTING_PROVE(mixed_true.is_epsilon_sat());

            SmtResult mixed_false=solver.solve(
                space,domain,ContinuousPredicate(false)&&atom);
            ARIADNE_TESTING_PROVE(mixed_false.is_unsat());

            SmtResult neutral_or=solver.solve(
                space,ExactBoxType({ExactIntervalType(-1,-0.5_x)}),
                ContinuousPredicate(false)||atom);
            ARIADNE_TESTING_PROVE(neutral_or.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] conjunction UNSAT: x>=1 and x<=0 on [0,1]");
            ContinuousPredicate formula=(ex>=1)&&(ex<=0);
            SmtResult solve_result=solver.solve(space,ExactBoxType({ExactIntervalType(0,1)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] disjunction EPSILON_SAT: x<0 or x>1 on [0,0.0625]");
            ContinuousPredicate formula=(ex<0)||(ex>1);
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0.0_x,0.0625_x)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat() || solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
            if(solve_result.is_epsilon_sat()) {
                ARIADNE_TESTING_PROVE(solve_result.has_witness());
            }
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] theory conflict clause reused by Boolean propagation");
            ContinuousPredicate left=(ex<0);
            ContinuousPredicate right=(ex>1);
            ContinuousPredicate formula=left||right;
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0.5_x,0.5_x)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] theory_learned="
                      << solve_result.statistics().theory_learned_clauses
                      << " theory_learned_literals="
                      << solve_result.statistics().theory_learned_clause_literals
                      << " theory_learned_propagations="
                      << solve_result.statistics().theory_learned_clause_propagations
                      << " learned_propagations="
                      << solve_result.statistics().learned_clause_propagations);
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_learned_clauses>=1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().theory_learned_clause_propagations>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] DP resolution UNKNOWN propagates through Boolean theory search");
            SmtSolver tiny_epsilon_solver(SmtSolverConfiguration(
                1e-30_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false));
            ContinuousPredicate uncertain=
                (sqr(sin(ex))+sqr(cos(ex))-1==0);
            SmtResult solve_result=tiny_epsilon_solver.solve(
                space,
                ExactBoxType({ExactIntervalType(1,1)}),
                uncertain||(!uncertain));
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(not solve_result.has_witness());
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().dp_resolution_exhaustions>=1u);
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] global box budget stops further Boolean search");
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                2u));
            ContinuousPredicate formula=(ex<0)||(ex>1);
            SmtResult solve_result=bounded_solver.solve(
                space,ExactBoxType({ExactIntervalType(0.5_x,0.5_x)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_checks>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_processed<=2u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_processed>=1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] trail backtracking across Boolean branches");
            ContinuousPredicate formula=(ex<0)||(ex>1);
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0.5_x,0.5_x)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            ARIADNE_TESTING_NOTE("[smt-dpll-stats] trail decisions="
                      << solve_result.statistics().boolean_decisions
                      << " propagations=" << solve_result.statistics().boolean_propagations
                      << " reasoned=" << solve_result.statistics().boolean_reasoned_propagations
                      << " backtracks=" << solve_result.statistics().boolean_backtracks
                      << " max_level=" << solve_result.statistics().max_decision_level
                      << " theory_checks=" << solve_result.statistics().theory_checks
                      << " theory_conflicts=" << solve_result.statistics().theory_conflicts);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boolean_decisions>=1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().boolean_reasoned_propagations,
                solve_result.statistics().boolean_propagations);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boolean_backtracks>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().max_decision_level>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().theory_conflicts>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().boolean_conflicts_analyzed>=1u);
            ARIADNE_TESTING_PROVE(solve_result.statistics().last_learned_clause_literals>=1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().last_learned_current_level_literals,1u);
            ARIADNE_TESTING_PROVE(
                solve_result.statistics().last_backjump_level
                < solve_result.statistics().max_decision_level);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] disjunction UNSAT: x<0 or x>1 on [0.375,0.625]");
            ContinuousPredicate formula=(ex<0)||(ex>1);
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0.375_x,0.625_x)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] negated atom preserves strict boundary: !(x<=0) at x=-epsilon");
            ContinuousPredicate formula=!(ex<=0);
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(-0.125_x,-0.125_x)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] disequality expands to theory alternatives: x!=0 at x=0");
            ContinuousPredicate formula=(ex!=0);
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(0,0)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_unsat() || solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] audit relation and negation delta-boundaries");

            auto require_epsilon_sat = [&](String const& label,
                                           ContinuousPredicate const& formula,
                                           ExactDouble value) {
                ARIADNE_TESTING_NOTE("[smt-relation] " << label << " value=" << value);
                SmtResult solve_result=solver.solve(
                    space,ExactBoxType({ExactIntervalType(value,value)}),formula);
                ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
                ARIADNE_TESTING_PROVE(solve_result.has_witness());
            };

            auto require_unsat = [&](String const& label,
                                     ContinuousPredicate const& formula,
                                     ExactDouble value) {
                ARIADNE_TESTING_NOTE("[smt-relation] " << label << " value=" << value);
                SmtResult solve_result=solver.solve(
                    space,ExactBoxType({ExactIntervalType(value,value)}),formula);
                ARIADNE_TESTING_PROVE(solve_result.is_unsat());
            };

            auto require_delta_overlap = [&](String const& label,
                                             ContinuousPredicate const& formula,
                                             ExactDouble value) {
                ARIADNE_TESTING_NOTE("[smt-relation] " << label << " value=" << value);
                SmtResult solve_result=solver.solve(
                    space,ExactBoxType({ExactIntervalType(value,value)}),formula);
                ARIADNE_TESTING_PROVE(solve_result.is_unsat() || solve_result.is_epsilon_sat());
                ARIADNE_TESTING_PROVE(not solve_result.is_unknown());
            };

            // Equality: exact models must be delta-sat; outside the epsilon band must be UNSAT.
            require_epsilon_sat("x=0 original true",ex==0,0.0_x);
            require_delta_overlap("x=0 positive epsilon boundary",ex==0,0.125_x);
            require_delta_overlap("x=0 negative epsilon boundary",ex==0,-0.125_x);
            require_unsat("x=0 outside epsilon",ex==0,0.25_x);

            // Non-strict inequalities use closed epsilon boundaries.
            require_epsilon_sat("x>=0 original true",ex>=0,0.25_x);
            require_delta_overlap("x>=0 epsilon boundary",ex>=0,-0.125_x);
            require_unsat("x>=0 outside epsilon",ex>=0,-0.25_x);

            require_epsilon_sat("x<=0 original true",ex<=0,-0.25_x);
            require_delta_overlap("x<=0 epsilon boundary",ex<=0,0.125_x);
            require_unsat("x<=0 outside epsilon",ex<=0,0.25_x);

            // Strict inequalities retain strictness after weakening.
            require_epsilon_sat("x>0 original true",ex>0,0.25_x);
            require_delta_overlap("x>0 weakened interior",ex>0,-0.0625_x);
            require_unsat("x>0 epsilon boundary excluded",ex>0,-0.125_x);

            require_epsilon_sat("x<0 original true",ex<0,-0.25_x);
            require_delta_overlap("x<0 weakened interior",ex<0,0.0625_x);
            require_unsat("x<0 epsilon boundary excluded",ex<0,0.125_x);

            // Sign predicates are strict positivity tests and use the same weakening as x>0.
            require_epsilon_sat("sgn(x) original true",sgn(ex),0.25_x);
            require_delta_overlap("sgn(x) weakened interior",sgn(ex),-0.0625_x);
            require_unsat("sgn(x) epsilon boundary excluded",sgn(ex),-0.125_x);

            // Disequality normalizes to x>0 OR -x>0. Its delta weakening is
            // therefore satisfied at equality as well.
            require_epsilon_sat("x!=0 original true positive",ex!=0,0.25_x);
            require_epsilon_sat("x!=0 original true negative",ex!=0,-0.25_x);
            require_delta_overlap("x!=0 equality delta-overlap",ex!=0,0.0_x);

            // Audit Boolean negation against the corresponding complementary relation.
            require_epsilon_sat("!(x<=0) original true",!(ex<=0),0.25_x);
            require_delta_overlap("!(x<=0) weakened interior",!(ex<=0),-0.0625_x);
            require_unsat("!(x<=0) strict epsilon boundary",!(ex<=0),-0.125_x);

            require_epsilon_sat("!(x>=0) original true",!(ex>=0),-0.25_x);
            require_delta_overlap("!(x>=0) weakened interior",!(ex>=0),0.0625_x);
            require_unsat("!(x>=0) strict epsilon boundary",!(ex>=0),0.125_x);

            require_epsilon_sat("!(x<0) original true",!(ex<0),0.25_x);
            require_delta_overlap("!(x<0) closed epsilon boundary",!(ex<0),-0.125_x);
            require_unsat("!(x<0) outside epsilon",!(ex<0),-0.25_x);

            require_epsilon_sat("!(x>0) original true",!(ex>0),-0.25_x);
            require_delta_overlap("!(x>0) closed epsilon boundary",!(ex>0),0.125_x);
            require_unsat("!(x>0) outside epsilon",!(ex>0),0.25_x);

            require_epsilon_sat("!sgn(x) original true",!sgn(ex),-0.25_x);
            require_delta_overlap("!sgn(x) closed epsilon boundary",!sgn(ex),0.125_x);
            require_unsat("!sgn(x) outside epsilon",!sgn(ex),0.25_x);

            require_epsilon_sat("!(x!=0) equality",!(ex!=0),0.0_x);
            require_delta_overlap("!(x!=0) epsilon boundary",!(ex!=0),0.125_x);
            require_unsat("!(x!=0) outside epsilon",!(ex!=0),0.25_x);

            require_delta_overlap("!(x==0) equality delta-overlap",!(ex==0),0.0_x);
            require_epsilon_sat("!(x==0) original true",!(ex==0),0.25_x);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] mixed transcendental Boolean formula");
            ContinuousPredicate formula=((sin(ex)==0)||(cos(ex)==0))&&(ex>=3);
            SmtResult solve_result=solver.solve(
                space,ExactBoxType({ExactIntervalType(3,4)}),formula);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-parallel] fused direct box processing");
            auto& thread_manager=ThreadManager::instance();
            ConcurrencyGuard concurrency_guard(thread_manager);
            SizeType parallel_concurrency=thread_manager.maximum_concurrency()>=2u
                ? 2u : thread_manager.maximum_concurrency();
            if(parallel_concurrency>0u) {
                SmtSolver cheap_solver(SmtSolverConfiguration(
                    0.125_x,
                    std::numeric_limits<SizeType>::max(),
                    std::numeric_limits<SizeType>::max(),
                    1u,
                    false,
                    false,
                    false,
                    false,
                    false,
                    false));
                List<SmtTheoryPrimitiveLiteral> literals({
                    SmtTheoryPrimitiveLiteral(
                        ex,SmtTheoryPrimitiveRelation::GEQ_ZERO)
                });
                thread_manager.set_concurrency(parallel_concurrency);
                SmtResult solve_result=cheap_solver.solve_parallel(
                    space,
                    ExactBoxType({ExactIntervalType(-0.25_x,0.25_x)}),
                    literals);
                ARIADNE_TESTING_PROVE(solve_result.is_unknown());
                ARIADNE_TESTING_EXPECT_EQUAL(
                    solve_result.statistics().fused_direct_classification_boxes,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
            }
        }

        {
            ARIADNE_TESTING_NOTE("[smt-dpll] sequential/parallel theory agreement");
            auto& thread_manager=ThreadManager::instance();
            ConcurrencyGuard concurrency_guard(thread_manager);
            SizeType parallel_concurrency=thread_manager.maximum_concurrency()>=2u
                ? 2u : thread_manager.maximum_concurrency();
            if(parallel_concurrency>0u) {
                ContinuousPredicate formula=((sin(ex)==0)||(cos(ex)==0))&&(ex>=3);
                ExactBoxType domain({ExactIntervalType(3,4)});

                thread_manager.set_concurrency(0);
                SmtResult sequential=solver.solve(space,domain,formula);

                thread_manager.set_concurrency(parallel_concurrency);
                SmtResult parallel=solver.solve_parallel(space,domain,formula);

                ARIADNE_TESTING_EXPECT_EQUAL(sequential.status(),parallel.status());
                ARIADNE_TESTING_PROVE(sequential.has_witness()==parallel.has_witness());
            }
        }
    }

    Void test_parallel_solve() {
        {
            ARIADNE_TESTING_NOTE("[smt-parallel] empty domains are UNSAT");
            ExactBoxType empty_domain({ExactIntervalType::empty_interval()});
            SmtSolver solver(SmtSolverConfiguration(0.125_x));

            List<ValidatedConstraint> constraints;
            SmtResult constraints_result=solver.solve_parallel(
                empty_domain,constraints);
            ARIADNE_TESTING_PROVE(constraints_result.is_unsat());

            RealVariable x("empty_parallel_x");
            RealSpace space({x});
            List<SmtTheoryPrimitiveLiteral> literals;
            SmtResult theory_result=solver.solve_parallel(
                space,empty_domain,literals);
            ARIADNE_TESTING_PROVE(theory_result.is_unsat());
        }

        {
            ARIADNE_TESTING_NOTE("[smt-parallel] empty conjunctions ignore zero box budget");
            SmtSolver zero_budget_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            ExactBoxType domain({ExactIntervalType(-1,1)});

            List<ValidatedConstraint> constraints;
            SmtResult constraints_result=zero_budget_solver.solve_parallel(
                domain,constraints);
            ARIADNE_TESTING_PROVE(constraints_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(constraints_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(constraints_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                constraints_result.statistics().box_budget_exhaustions,0u);

            RealVariable x("x");
            RealSpace space({x});
            List<SmtTheoryPrimitiveLiteral> literals;
            SmtResult theory_result=zero_budget_solver.solve_parallel(
                space,domain,literals);
            ARIADNE_TESTING_PROVE(theory_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(theory_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(theory_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                theory_result.statistics().box_budget_exhaustions,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-parallel] zero box budget returns UNKNOWN");
            auto x=ValidatedScalarMultivariateFunction::coordinates(1);
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            ExactBoxType domain({ExactIntervalType(0,1)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0.5_x),x[0],ValidatedNumber(0.5_x))
            });
            SmtResult solve_result=bounded_solver.solve_parallel(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::RESOURCE_EXHAUSTED);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().non_splittable_uncertified_boxes,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-parallel] non-splittable DP resolution exhaustion counted once");
            auto x=ValidatedScalarMultivariateFunction::coordinates(1);
            SmtSolver tiny_epsilon_solver(SmtSolverConfiguration(
                1e-30_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false));
            ExactBoxType domain({ExactIntervalType(1,1)});
            ValidatedScalarMultivariateFunction residual=sin(x[0])-sin(x[0]);
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(
                    ValidatedNumber(0),
                    residual,
                    ValidatedNumber(0))
            });
            SmtResult solve_result=tiny_epsilon_solver.solve_parallel(domain,constraints);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
            ARIADNE_TESTING_PROVE(not solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().dp_resolution_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().non_splittable_uncertified_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().non_splittable_epsilon_overlap_boxes,1u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-parallel] theory DP terminal precision limit returns precision UNKNOWN");
            RealVariable x("x");
            RealExpression ex=x;
            RealSpace space({x});
            SmtSolver tiny_epsilon_solver(SmtSolverConfiguration(
                1e-30_pr,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                false));
            RealExpression residual=sqr(sin(ex))+sqr(cos(ex))-1;
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(residual==0));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=tiny_epsilon_solver.solve_parallel(
                space,
                ExactBoxType({ExactIntervalType(1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::DP_RESOLUTION_EXHAUSTED);
            ARIADNE_TESTING_PROVE(not solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().dp_resolution_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().non_splittable_uncertified_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().non_splittable_epsilon_overlap_boxes,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(
                solve_result.statistics().epsilon_box_certifications,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-parallel] simplified zero primitive ignores zero box budget");
            RealVariable x("zero_parallel_x");
            RealExpression ex=x;
            RealSpace space({x});
            SmtSolver zero_budget_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u,
                false));
            RealExpression residual=sin(ex)-sin(ex);
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(residual>=0));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=zero_budget_solver.solve_parallel(
                space,
                ExactBoxType({ExactIntervalType(1,1)}),
                literals);
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,0u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-parallel] theory zero box budget returns UNKNOWN");
            RealVariable x("x");
            RealSpace space({x});
            SmtSolver bounded_solver(SmtSolverConfiguration(
                0.125_x,
                std::numeric_limits<SizeType>::max(),
                std::numeric_limits<SizeType>::max(),
                0u));
            auto alternatives=normalize_smt_theory_literal(
                make_smt_theory_literal(RealExpression(x)==0.5_x));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
            List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
            SmtResult solve_result=bounded_solver.solve_parallel(
                space,ExactBoxType({ExactIntervalType(0,1)}),literals);
            ARIADNE_TESTING_PROVE(solve_result.is_unknown());
            ARIADNE_TESTING_PROVE(
                solve_result.unknown_reason()==SmtUnknownReason::RESOURCE_EXHAUSTED);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,0u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,1u);
            ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().non_splittable_uncertified_boxes,0u);
        }

        auto x=ValidatedScalarMultivariateFunction::coordinates(1);
        SmtSolver solver(SmtSolverConfiguration(0.125_x));
        auto& thread_manager=ThreadManager::instance();
        ConcurrencyGuard concurrency_guard(thread_manager);

        ARIADNE_TESTING_NOTE("[smt-parallel] sequential Threading mode concurrency=0");
        thread_manager.set_concurrency(0);
        {
            ExactBoxType domain({ExactIntervalType(3,4)});
            List<ValidatedConstraint> constraints({
                ValidatedConstraint(ValidatedNumber(0),sin(x[0]),ValidatedNumber(0))
            });
            SmtSolverTestSupport::begin_parallel_execution_observation();
            SmtResult solve_result=solver.solve_parallel(domain,constraints);
            auto observation=SmtSolverTestSupport::end_parallel_execution_observation();
            ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
            ARIADNE_TESTING_PROVE(solve_result.has_witness());
            ARIADNE_TESTING_PROVE(observation.calling_thread_observed);
            ARIADNE_TESTING_EXPECT_EQUAL(observation.worker_thread_count,0u);
            ARIADNE_TESTING_NOTE("[smt-parallel] concurrency=0 processed="
                      << solve_result.statistics().boxes_processed
                      << " pruned=" << solve_result.statistics().boxes_pruned
                      << " split=" << solve_result.statistics().boxes_split);
        }

        SizeType parallel_concurrency=thread_manager.maximum_concurrency()>=2u ? 2u : thread_manager.maximum_concurrency();
        if(parallel_concurrency>0u) {
            ARIADNE_TESTING_NOTE("[smt-parallel] concurrent Threading mode concurrency="
                      << parallel_concurrency);
            thread_manager.set_concurrency(parallel_concurrency);

            {
                ExactBoxType domain({ExactIntervalType(3,4)});
                List<ValidatedConstraint> constraints({
                    ValidatedConstraint(ValidatedNumber(0),sin(x[0]),ValidatedNumber(0))
                });
                SmtSolverTestSupport::begin_parallel_execution_observation();
                SmtResult solve_result=solver.solve_parallel(domain,constraints);
                auto observation=SmtSolverTestSupport::end_parallel_execution_observation();
                ARIADNE_TESTING_PROVE(solve_result.is_epsilon_sat());
                ARIADNE_TESTING_PROVE(solve_result.has_witness());
                ARIADNE_TESTING_PROVE(not observation.calling_thread_observed);
                ARIADNE_TESTING_PROVE(observation.worker_thread_count>=1u);
                ARIADNE_TESTING_NOTE("[smt-parallel] EPSILON_SAT processed="
                          << solve_result.statistics().boxes_processed
                          << " pruned=" << solve_result.statistics().boxes_pruned
                          << " split=" << solve_result.statistics().boxes_split);
            }

            {
                ARIADNE_TESTING_NOTE("[smt-parallel] concurrent split with one-box budget");
                auto xy=ValidatedScalarMultivariateFunction::coordinates(2);
                SmtSolver split_solver(SmtSolverConfiguration(
                    0.01_pr,
                    std::numeric_limits<SizeType>::max(),
                    std::numeric_limits<SizeType>::max(),
                    1u,
                    false));
                ExactBoxType domain({
                    ExactIntervalType(-1,1),
                    ExactIntervalType(-10000,10000)
                });
                List<ValidatedConstraint> constraints({
                    ValidatedConstraint(
                        ValidatedNumber(0.3_pr),
                        sin(10*xy[0]),
                        ValidatedNumber(0.3_pr))
                });
                SmtResult solve_result=split_solver.solve_parallel(domain,constraints);
                ARIADNE_TESTING_PROVE(solve_result.is_unknown());
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().sensitivity_guided_splits,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(
                    solve_result.statistics().sensitivity_overrides_geometric_splits,1u);
            }

            {
                ARIADNE_TESTING_NOTE("[smt-parallel] concurrent theory split with one-box budget");
                RealVariable tx("parallel_theory_x"), ty("parallel_theory_y");
                RealExpression etx=tx;
                RealSpace theory_space({tx,ty});
                SmtSolver split_solver(SmtSolverConfiguration(
                    0.01_pr,
                    std::numeric_limits<SizeType>::max(),
                    std::numeric_limits<SizeType>::max(),
                    1u,
                    false));
                auto alternatives=normalize_smt_theory_literal(
                    make_smt_theory_literal(sin(10*etx)==0.3_pr));
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(),1u);
                ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(),1u);
                List<SmtTheoryPrimitiveLiteral> literals({alternatives[0][0]});
                SmtResult solve_result=split_solver.solve_parallel(
                    theory_space,
                    ExactBoxType({
                        ExactIntervalType(-1,1),
                        ExactIntervalType(-10000,10000)
                    }),
                    literals);
                ARIADNE_TESTING_PROVE(solve_result.is_unknown());
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_processed,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().boxes_split,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().box_budget_exhaustions,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().candidate_witness_searches,0u);
                ARIADNE_TESTING_EXPECT_EQUAL(solve_result.statistics().sensitivity_guided_splits,1u);
                ARIADNE_TESTING_EXPECT_EQUAL(
                    solve_result.statistics().sensitivity_overrides_geometric_splits,1u);
            }

            {
                ARIADNE_TESTING_NOTE("[smt-parallel] concurrent forced splitting UNSAT: sin(x)=0 and cos(x)=0 on [0,7]");
                ExactBoxType domain({ExactIntervalType(0,7)});
                List<ValidatedConstraint> constraints({
                    ValidatedConstraint(ValidatedNumber(0),sin(x[0]),ValidatedNumber(0)),
                    ValidatedConstraint(ValidatedNumber(0),cos(x[0]),ValidatedNumber(0))
                });
                SmtResult solve_result=solver.solve_parallel(domain,constraints);
                ARIADNE_TESTING_PROVE(solve_result.is_unsat());
                ARIADNE_TESTING_NOTE("[smt-parallel] forced splitting processed="
                          << solve_result.statistics().boxes_processed
                          << " pruned=" << solve_result.statistics().boxes_pruned
                          << " split=" << solve_result.statistics().boxes_split);
                ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_pruned>0u);
                ARIADNE_TESTING_PROVE(solve_result.statistics().hull_reduction_rounds>=1u);
                ARIADNE_TESTING_PROVE(solve_result.statistics().shaving_reduction_rounds>=1u);
            }

            {
                ARIADNE_TESTING_NOTE("[smt-parallel] concurrent UNSAT: sin(x)=2 on [3,4]");
                ExactBoxType domain({ExactIntervalType(3,4)});
                List<ValidatedConstraint> constraints({
                    ValidatedConstraint(ValidatedNumber(2),sin(x[0]),ValidatedNumber(2))
                });
                SmtResult solve_result=solver.solve_parallel(domain,constraints);
                ARIADNE_TESTING_PROVE(solve_result.is_unsat());
                ARIADNE_TESTING_PROVE(solve_result.statistics().boxes_pruned>=1u);
            }
        } else {
            ARIADNE_TESTING_NOTE("[smt-parallel] hardware reports no worker concurrency; concurrent case skipped");
        }

        ARIADNE_TESTING_NOTE("[smt-parallel] compare sequential and parallel logical status");
        auto compare_status = [&](String const& label,
                                  ExactBoxType const& domain,
                                  List<ValidatedConstraint> const& constraints) {
            thread_manager.set_concurrency(0);
            SmtResult sequential_result=solver.solve(domain,constraints);

            if(parallel_concurrency>0u) {
                thread_manager.set_concurrency(parallel_concurrency);
                SmtResult parallel_result=solver.solve_parallel(domain,constraints);

                ARIADNE_TESTING_NOTE("[smt-parallel-compare] " << label
                          << " sequential=" << sequential_result.status()
                          << " parallel=" << parallel_result.status());

                ARIADNE_TESTING_EXPECT_EQUAL(sequential_result.status(),parallel_result.status());
                ARIADNE_TESTING_PROVE(sequential_result.has_witness()==parallel_result.has_witness());
            }
        };

        compare_status(
            "linear epsilon-sat",
            ExactBoxType({ExactIntervalType(0,1)}),
            List<ValidatedConstraint>({
                ValidatedConstraint(ValidatedNumber(1),2*x[0],ValidatedNumber(1))
            }));

        compare_status(
            "linear unsat",
            ExactBoxType({ExactIntervalType(0,1)}),
            List<ValidatedConstraint>({
                ValidatedConstraint(ValidatedNumber(2),x[0],ValidatedNumber(2))
            }));

        compare_status(
            "transcendental epsilon-sat",
            ExactBoxType({ExactIntervalType(3,4)}),
            List<ValidatedConstraint>({
                ValidatedConstraint(ValidatedNumber(0),sin(x[0]),ValidatedNumber(0))
            }));

        compare_status(
            "transcendental unsat",
            ExactBoxType({ExactIntervalType(3,4)}),
            List<ValidatedConstraint>({
                ValidatedConstraint(ValidatedNumber(2),sin(x[0]),ValidatedNumber(2))
            }));

        compare_status(
            "forced splitting transcendental unsat",
            ExactBoxType({ExactIntervalType(0,7)}),
            List<ValidatedConstraint>({
                ValidatedConstraint(ValidatedNumber(0),sin(x[0]),ValidatedNumber(0)),
                ValidatedConstraint(ValidatedNumber(0),cos(x[0]),ValidatedNumber(0))
            }));
    }
};

int main(int argc, char** argv) {
    ARIADNE_TESTING_SUITE("test_smt_solver");
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_configuration);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_public_preconditions);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_result);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_learned_clause_pruning_policy);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_statistics_aggregation);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_parallel_state_transitions);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_epsilon_witness_candidate_limits);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_theory_derivative_compilation_policy);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_candidate_witness_outcome);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_sensitivity_split_selection);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_monotone_coordinate_gating);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_search_outcome);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_cdcl_helpers);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_invalid_internal_relations);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_epsilon_predicates);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_fused_direct_classification);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_box_processing_statistics);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_solve);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_geometric_validated_constraint_split);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_theory_solve);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_interval_newton_adaptive_retry);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_boolean_theory_solve);
    ARIADNE_TESTING_ADD_TEST(TestSmtSolver, test_parallel_solve);
    return ARIADNE_TESTING_RUN_TESTS_WITH_ARGS(argc, argv);
}
