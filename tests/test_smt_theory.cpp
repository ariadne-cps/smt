/***************************************************************************
 *            test_smt_theory.cpp
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

/** @file tests/test_smt_theory.cpp
 *  @brief Test SMT theory literal normalization and evaluation.
 */

#include <sstream>

#include "numeric/numeric.hpp"
#include "smt/smt_theory.hpp"
#include "symbolic/variable.hpp"

#include "ariadne-testing.hpp"

using namespace Ariadne;

class TestSmtTheory : public Ariadne::Testing::ContextFixture {
  public:
    using ContextFixture::ContextFixture;

  public:
    Void check_relation(const ContinuousPredicate& predicate,
                        SmtTheoryRelation expected,
                        const String& label) {
        ARIADNE_TESTING_NOTE("[smt-theory] relation " << label);
        SmtTheoryLiteral literal = make_smt_theory_literal(predicate);
        ARIADNE_TESTING_EXPECT_EQUAL(literal.relation(), expected);
    }

    Void test_relations() {
        RealVariable x("x"), y("y");
        RealExpression ex = x;
        RealExpression ey = y;

        check_relation(ex == ey, SmtTheoryRelation::EQ, "x==y");
        check_relation(ex != ey, SmtTheoryRelation::NEQ, "x!=y");
        check_relation(ex <= ey, SmtTheoryRelation::LEQ, "x<=y");
        check_relation(ex >= ey, SmtTheoryRelation::GEQ, "x>=y");
        check_relation(ex < ey, SmtTheoryRelation::LT, "x<y");
        check_relation(ex > ey, SmtTheoryRelation::GT, "x>y");
        check_relation(sgn(ex), SmtTheoryRelation::GT, "sgn(x) -> x>0");
    }

    Void check_negation(const ContinuousPredicate& predicate,
                        SmtTheoryRelation expected,
                        const String& label) {
        ARIADNE_TESTING_NOTE("[smt-theory] negation " << label);
        SmtTheoryLiteral literal = make_smt_theory_literal(predicate).negated();
        ARIADNE_TESTING_EXPECT_EQUAL(literal.relation(), expected);
    }

    Void test_negations() {
        RealVariable x("x"), y("y");
        RealExpression ex = x;
        RealExpression ey = y;

        check_negation(ex == ey, SmtTheoryRelation::NEQ, "!(x==y) -> x!=y");
        check_negation(ex != ey, SmtTheoryRelation::EQ, "!(x!=y) -> x==y");
        check_negation(ex <= ey, SmtTheoryRelation::GT, "!(x<=y) -> x>y");
        check_negation(ex >= ey, SmtTheoryRelation::LT, "!(x>=y) -> x<y");
        check_negation(ex < ey, SmtTheoryRelation::GEQ, "!(x<y) -> x>=y");
        check_negation(ex > ey, SmtTheoryRelation::LEQ, "!(x>y) -> x<=y");
        check_negation(sgn(ex), SmtTheoryRelation::LEQ, "!sgn(x) -> x<=0");
    }

    Void test_normalization() {
        RealVariable x("x"), y("y");
        RealExpression ex = x;
        RealExpression ey = y;

        auto check_single = [&](const ContinuousPredicate& predicate,
                                SmtTheoryPrimitiveRelation expected_relation,
                                const RealExpression& expected_expression,
                                const String& label) {
            ARIADNE_TESTING_NOTE("[smt-theory] normalize " << label);
            auto alternatives = normalize_smt_theory_literal(make_smt_theory_literal(predicate));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0][0].relation(), expected_relation);
            ARIADNE_TESTING_EXPECT_SAME(alternatives[0][0].expression(), expected_expression);
        };

        check_single(ex == ey, SmtTheoryPrimitiveRelation::EQ_ZERO, ex - ey, "x==y -> x-y=0");
        check_single(ex >= ey, SmtTheoryPrimitiveRelation::GEQ_ZERO, ex - ey, "x>=y -> x-y>=0");
        check_single(ex > ey, SmtTheoryPrimitiveRelation::GT_ZERO, ex - ey, "x>y -> x-y>0");
        check_single(ex <= ey, SmtTheoryPrimitiveRelation::GEQ_ZERO, ey - ex, "x<=y -> y-x>=0");
        check_single(ex < ey, SmtTheoryPrimitiveRelation::GT_ZERO, ey - ex, "x<y -> y-x>0");
        check_single(
            sgn(ex),
            SmtTheoryPrimitiveRelation::GT_ZERO,
            ex - RealExpression(0),
            "sgn(x) -> x>0");

        ARIADNE_TESTING_NOTE("[smt-theory] normalize x!=y -> (x-y>0) or (y-x>0)");
        auto neq = normalize_smt_theory_literal(make_smt_theory_literal(ex != ey));
        ARIADNE_TESTING_EXPECT_EQUAL(neq.size(), 2u);
        ARIADNE_TESTING_EXPECT_EQUAL(neq[0].size(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(neq[1].size(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(neq[0][0].relation(), SmtTheoryPrimitiveRelation::GT_ZERO);
        ARIADNE_TESTING_EXPECT_EQUAL(neq[1][0].relation(), SmtTheoryPrimitiveRelation::GT_ZERO);
        ARIADNE_TESTING_EXPECT_SAME(neq[0][0].expression(), ex - ey);
        ARIADNE_TESTING_EXPECT_SAME(neq[1][0].expression(), ey - ex);
    }

    Void test_weakening() {
        RealVariable x("x"), y("y");
        RealExpression ex = x;
        RealExpression ey = y;
        ExactDouble epsilon = 0.125_x;

        auto check = [&](const ContinuousPredicate& predicate,
                         SmtTheoryWeakRelation expected,
                         const String& label) {
            ARIADNE_TESTING_NOTE("[smt-theory] weaken " << label << " epsilon=" << epsilon);
            auto alternatives = normalize_smt_theory_literal(make_smt_theory_literal(predicate));
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives.size(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(alternatives[0].size(), 1u);
            auto weakened = weaken_smt_theory_literal(alternatives[0][0], epsilon);
            ARIADNE_TESTING_EXPECT_EQUAL(weakened.relation(), expected);
            ARIADNE_TESTING_EXPECT_EQUAL(weakened.epsilon(), epsilon);
            ARIADNE_TESTING_EXPECT_SAME(
                weakened.expression(),
                alternatives[0][0].expression());
        };

        check(ex == ey, SmtTheoryWeakRelation::ABS_LEQ_EPSILON, "x==y -> |x-y|<=epsilon");
        check(ex >= ey, SmtTheoryWeakRelation::GEQ_MINUS_EPSILON, "x>=y -> x-y>=-epsilon");
        check(ex > ey, SmtTheoryWeakRelation::GT_MINUS_EPSILON, "x>y -> x-y>-epsilon");
        check(sgn(ex), SmtTheoryWeakRelation::GT_MINUS_EPSILON, "sgn(x) -> x>-epsilon");

        ARIADNE_TESTING_NOTE("[smt-theory] weakening requires positive epsilon");
        auto primitive = normalize_smt_theory_literal(make_smt_theory_literal(ex == ey))[0][0];
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, weaken_smt_theory_literal(primitive, 0.0_x));
    }

    Void test_streaming() {
        ARIADNE_TESTING_NOTE("[smt-theory] stream all theory relation kinds");

        std::ostringstream relation_stream;
        relation_stream
            << SmtTheoryRelation::EQ << " "
            << SmtTheoryRelation::NEQ << " "
            << SmtTheoryRelation::LEQ << " "
            << SmtTheoryRelation::GEQ << " "
            << SmtTheoryRelation::LT << " "
            << SmtTheoryRelation::GT;
        ARIADNE_TESTING_EXPECT_EQUAL(
            relation_stream.str(),
            String("= != <= >= < >"));

        std::ostringstream primitive_stream;
        primitive_stream
            << SmtTheoryPrimitiveRelation::EQ_ZERO << " "
            << SmtTheoryPrimitiveRelation::GEQ_ZERO << " "
            << SmtTheoryPrimitiveRelation::GT_ZERO;
        ARIADNE_TESTING_EXPECT_EQUAL(
            primitive_stream.str(),
            String("=0 >=0 >0"));

        std::ostringstream weak_stream;
        weak_stream
            << SmtTheoryWeakRelation::ABS_LEQ_EPSILON << " "
            << SmtTheoryWeakRelation::GEQ_MINUS_EPSILON << " "
            << SmtTheoryWeakRelation::GT_MINUS_EPSILON;
        ARIADNE_TESTING_EXPECT_EQUAL(
            weak_stream.str(),
            String("abs<=epsilon >=-epsilon >-epsilon"));
    }

    Void test_invalid_relations() {
        std::ostringstream invalid_stream;
        ARIADNE_TESTING_NOTE("[smt-theory] reject invalid enum values");
        RealVariable x("x");
        RealExpression ex = x;

        auto invalid_relation = static_cast<SmtTheoryRelation>(999);
        SmtTheoryLiteral invalid_literal(ex, invalid_relation, RealExpression(0));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, invalid_literal.negated());
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, normalize_smt_theory_literal(invalid_literal));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, static_cast<Void>(
                                                              static_cast<OutputStream&>(invalid_stream) << invalid_relation));

        auto invalid_primitive = static_cast<SmtTheoryPrimitiveRelation>(999);
        SmtTheoryPrimitiveLiteral invalid_primitive_literal(ex, invalid_primitive);
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, weaken_smt_theory_literal(invalid_primitive_literal, 0.125_x));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, static_cast<Void>(
                                                              static_cast<OutputStream&>(invalid_stream) << invalid_primitive));

        auto invalid_weak = static_cast<SmtTheoryWeakRelation>(999);
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, static_cast<Void>(
                                                              static_cast<OutputStream&>(invalid_stream) << invalid_weak));
    }

    Void test_reject_non_atom() {
        RealVariable x("x"), y("y");
        RealExpression ex = x;
        RealExpression ey = y;
        ContinuousPredicate formula = (ex <= 0) && (ey >= 1);

        ARIADNE_TESTING_NOTE("[smt-theory] reject non-atomic conjunction");
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, make_smt_theory_literal(formula));
    }
};

int main(int argc, char** argv) {
    ARIADNE_TESTING_SUITE("test_smt_theory");
    ARIADNE_TESTING_ADD_TEST(TestSmtTheory, test_relations);
    ARIADNE_TESTING_ADD_TEST(TestSmtTheory, test_negations);
    ARIADNE_TESTING_ADD_TEST(TestSmtTheory, test_normalization);
    ARIADNE_TESTING_ADD_TEST(TestSmtTheory, test_weakening);
    ARIADNE_TESTING_ADD_TEST(TestSmtTheory, test_streaming);
    ARIADNE_TESTING_ADD_TEST(TestSmtTheory, test_invalid_relations);
    ARIADNE_TESTING_ADD_TEST(TestSmtTheory, test_reject_non_atom);
    return ARIADNE_TESTING_RUN_TESTS_WITH_ARGS(argc, argv);
}
