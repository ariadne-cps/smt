/***************************************************************************
 *            test_smt_boolean.cpp
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

/** @file tests/test_smt_boolean.cpp
 *  @brief Test Boolean encoding and Tseitin clauses.
 */

#include <limits>

#include "numeric/numeric.hpp"
#include "smt/smt_boolean.hpp"
#include "symbolic/variable.hpp"

#include "ariadne-testing.hpp"

using namespace Ariadne;

class TestSmtBoolean : public Ariadne::Testing::ContextFixture {
  public:
    using ContextFixture::ContextFixture;

  public:
    Void test_boolean_literal() {
        BooleanLiteral positive(0u);
        BooleanLiteral negative(0u, false);
        ARIADNE_TESTING_EXPECT_EQUAL(positive.variable(), 0u);
        ARIADNE_TESTING_EXPECT_EQUAL(positive.dimacs(), 1);
        ARIADNE_TESTING_PROVE(positive.positive());
        ARIADNE_TESTING_EXPECT_EQUAL(negative.variable(), 0u);
        ARIADNE_TESTING_EXPECT_EQUAL(negative.dimacs(), -1);
        ARIADNE_TESTING_PROVE(not negative.positive());
        ARIADNE_TESTING_PROVE(-positive == negative);
        ARIADNE_TESTING_PROVE(-negative == positive);
        ARIADNE_TESTING_EXPECT_EQUAL(BooleanLiteral::from_dimacs(2).variable(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(BooleanLiteral::from_dimacs(-2).variable(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(BooleanLiteral::from_dimacs(-2).dimacs(), -2);
        ARIADNE_TESTING_EXPECT_THROWS(std::out_of_range, BooleanLiteral::from_dimacs(0));
        ARIADNE_TESTING_EXPECT_THROWS(std::out_of_range, BooleanLiteral::from_dimacs(std::numeric_limits<Int>::min()));
        ARIADNE_TESTING_EXPECT_THROWS(std::out_of_range, BooleanLiteral(static_cast<SizeType>(std::numeric_limits<Int>::max())));
        ARIADNE_TESTING_EXPECT_EQUAL(
            BooleanLiteral(static_cast<SizeType>(std::numeric_limits<Int>::max()) - 1u).dimacs(),
            std::numeric_limits<Int>::max());
    }

    Void test_atom() {
        RealVariable x("x");
        ContinuousPredicate predicate = (x <= 0);

        ARIADNE_TESTING_NOTE("[smt-boolean] atom x<=0");
        SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(predicate);

        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0].size(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0][0].dimacs(), 1);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_variable(0), 0u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom(0).code(), OperatorCode::LEQ);
    }

    Void test_constants() {
        {
            ARIADNE_TESTING_NOTE("[smt-boolean] constant true");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(ContinuousPredicate(true));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 0u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0].size(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0][0].dimacs(), 1);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[1][0].dimacs(), 1);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] constant false");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(ContinuousPredicate(false));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 0u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0].size(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0][0].dimacs(), -1);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[1][0].dimacs(), 1);
        }

        {
            RealVariable x("x");
            ContinuousPredicate atom = (x <= 0);
            ARIADNE_TESTING_NOTE("[smt-boolean] constants composed with atom");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(
                (ContinuousPredicate(true) && atom) || ContinuousPredicate(false));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0][0].dimacs(), 1);
        }

        {
            RealVariable x("x");
            ContinuousPredicate atom = (x <= 0);

            ARIADNE_TESTING_NOTE("[smt-boolean] fold false&&atom");
            SmtBooleanEncoding and_false = SmtBooleanEncoder().encode(
                ContinuousPredicate(false) && atom);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false.atom_count(), 0u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false.clauses().size(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false.clauses()[0][0].dimacs(), -1);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false.clauses()[1][0].dimacs(), 1);

            ARIADNE_TESTING_NOTE("[smt-boolean] fold true||atom");
            SmtBooleanEncoding or_true = SmtBooleanEncoder().encode(
                ContinuousPredicate(true) || atom);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true.atom_count(), 0u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true.clauses().size(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true.clauses()[0][0].dimacs(), 1);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true.clauses()[1][0].dimacs(), 1);

            ARIADNE_TESTING_NOTE("[smt-boolean] fold atom&&true");
            SmtBooleanEncoding and_true_rhs = SmtBooleanEncoder().encode(
                atom && ContinuousPredicate(true));
            ARIADNE_TESTING_EXPECT_EQUAL(and_true_rhs.atom_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_true_rhs.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_true_rhs.clauses().size(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_true_rhs.clauses()[0][0].dimacs(), 1);

            ARIADNE_TESTING_NOTE("[smt-boolean] fold atom&&false");
            SmtBooleanEncoding and_false_rhs = SmtBooleanEncoder().encode(
                atom && ContinuousPredicate(false));
            ARIADNE_TESTING_EXPECT_EQUAL(and_false_rhs.atom_count(), 0u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false_rhs.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false_rhs.clauses().size(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false_rhs.clauses()[0][0].dimacs(), -1);
            ARIADNE_TESTING_EXPECT_EQUAL(and_false_rhs.clauses()[1][0].dimacs(), 1);

            ARIADNE_TESTING_NOTE("[smt-boolean] fold atom||true");
            SmtBooleanEncoding or_true_rhs = SmtBooleanEncoder().encode(
                atom || ContinuousPredicate(true));
            ARIADNE_TESTING_EXPECT_EQUAL(or_true_rhs.atom_count(), 0u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true_rhs.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true_rhs.clauses().size(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true_rhs.clauses()[0][0].dimacs(), 1);
            ARIADNE_TESTING_EXPECT_EQUAL(or_true_rhs.clauses()[1][0].dimacs(), 1);

            ARIADNE_TESTING_NOTE("[smt-boolean] fold atom||false");
            SmtBooleanEncoding or_false_rhs = SmtBooleanEncoder().encode(
                atom || ContinuousPredicate(false));
            ARIADNE_TESTING_EXPECT_EQUAL(or_false_rhs.atom_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_false_rhs.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_false_rhs.clauses().size(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(or_false_rhs.clauses()[0][0].dimacs(), 1);

            ARIADNE_TESTING_NOTE("[smt-boolean] fold negated constant");
            SmtBooleanEncoding negated = SmtBooleanEncoder().encode(
                !ContinuousPredicate(false));
            ARIADNE_TESTING_EXPECT_EQUAL(negated.atom_count(), 0u);
            ARIADNE_TESTING_EXPECT_EQUAL(negated.variable_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(negated.clauses().size(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(negated.clauses()[0][0].dimacs(), 1);
            ARIADNE_TESTING_EXPECT_EQUAL(negated.clauses()[1][0].dimacs(), 1);
        }
    }

    Void test_invalid_inputs() {
        ARIADNE_TESTING_NOTE("[smt-boolean] reject indeterminate constants");
        ContinuousPredicate indeterminate_constant{Kleenean(indeterminate)};
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtBooleanEncoder().encode(indeterminate_constant));

        RealVariable x("x");
        ContinuousPredicate atom = (x <= 0);
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtBooleanEncoder().encode(indeterminate_constant && atom));

        ARIADNE_TESTING_NOTE("[smt-boolean] reject invalid relation/operator enums");
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtBooleanTestSupport::canonical_relation(
                                                              static_cast<SmtTheoryRelation>(999)));
        ARIADNE_TESTING_EXPECT_THROWS(std::runtime_error, SmtBooleanTestSupport::supported_operator(
                                                              static_cast<OperatorCode>(999)));
    }

    Void test_sign_atom() {
        RealVariable x("x");
        RealExpression ex = x;
        ContinuousPredicate predicate = sgn(ex);

        ARIADNE_TESTING_NOTE("[smt-boolean] sign atom sgn(x)");
        SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(predicate);

        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0].size(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0][0].dimacs(), 1);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_variable(0), 0u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom(0).code(), OperatorCode::SGN);
    }

    Void test_negation() {
        RealVariable x("x");
        ContinuousPredicate atom = (x <= 0);

        ARIADNE_TESTING_NOTE("[smt-boolean] negation !(x<=0)");
        SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(!atom);

        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses()[0][0].dimacs(), -1);
    }

    Void test_conjunction() {
        RealVariable x("x"), y("y");
        ContinuousPredicate lhs = (x <= 0);
        ContinuousPredicate rhs = (y >= 1);

        ARIADNE_TESTING_NOTE("[smt-boolean] conjunction (x<=0)&&(y>=1)");
        SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(lhs && rhs);

        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 2u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 3u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 4u);

        ARIADNE_TESTING_NOTE("[smt-boolean] conjunction variables=" << encoding.variable_count()
                                                                    << " clauses=" << encoding.clauses().size());
    }

    Void test_disjunction() {
        RealVariable x("x"), y("y");
        ContinuousPredicate lhs = (x <= 0);
        ContinuousPredicate rhs = (y >= 1);

        ARIADNE_TESTING_NOTE("[smt-boolean] disjunction (x<=0)||(y>=1)");
        SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(lhs || rhs);

        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 2u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 3u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 4u);
    }

    Void test_shared_atom() {
        RealVariable x("x");
        ContinuousPredicate atom = (x <= 0);

        ARIADNE_TESTING_NOTE("[smt-boolean] shared atom (x<=0)||!(x<=0)");
        SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(atom || !atom);

        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 2u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 4u);
    }

    Void test_structurally_shared_atom() {
        RealVariable x("x");
        RealExpression ex = x;
        ContinuousPredicate first = (ex <= 0);
        ContinuousPredicate second = (ex <= 0);

        ARIADNE_TESTING_PROVE(first.node_raw_ptr() != second.node_raw_ptr());
        ARIADNE_TESTING_NOTE("[smt-boolean] structurally shared atoms built as distinct nodes");
        SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(first && !second);

        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 2u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 4u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_variable(0), 0u);
    }

    Void test_semantically_shared_atom() {
        RealVariable x("x"), y("y");
        RealExpression ex = x;
        RealExpression ey = y;

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] x<=y and y>=x share an atom");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode((ex <= ey) && !(ey >= ex));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] x<y and y>x share an atom");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode((ex < ey) && !(ey > ex));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] symmetric equality shares an atom");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode((ex == ey) && !(ey == ex));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] symmetric disequality shares an atom");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode((ex != ey) && !(ey != ex));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] sgn(x) and x>0 share an atom");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(sgn(ex) && !(ex > 0));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 1u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 2u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] same lhs with different rhs stays distinct");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(
                (ex >= 0) && (ex >= 1));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 3u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] different canonical relations stay distinct");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(
                (ex >= 0) && (ex == 0));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 3u);
        }

        {
            ARIADNE_TESTING_NOTE("[smt-boolean] same relation with different lhs stays distinct");
            SmtBooleanEncoding encoding = SmtBooleanEncoder().encode(
                (ex >= 0) && (ey >= 0));
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 2u);
            ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 3u);
        }
    }

    Void test_nested_formula() {
        RealVariable x("x"), y("y"), z("z");
        ContinuousPredicate a = (x <= 0);
        ContinuousPredicate b = (y >= 1);
        ContinuousPredicate c = (z == 2);

        ARIADNE_TESTING_NOTE("[smt-boolean] nested ((x<=0)||(y>=1))&&!(z==2)");
        SmtBooleanEncoding encoding = SmtBooleanEncoder().encode((a || b) && !c);

        ARIADNE_TESTING_EXPECT_EQUAL(encoding.atom_count(), 3u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.variable_count(), 5u);
        ARIADNE_TESTING_EXPECT_EQUAL(encoding.clauses().size(), 7u);

        ARIADNE_TESTING_NOTE("[smt-boolean] nested atoms=" << encoding.atom_count()
                                                           << " variables=" << encoding.variable_count()
                                                           << " clauses=" << encoding.clauses().size());
    }
};

int main(int argc, char** argv) {
    ARIADNE_TESTING_SUITE("test_smt_boolean");
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_boolean_literal);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_atom);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_constants);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_invalid_inputs);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_sign_atom);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_negation);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_conjunction);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_disjunction);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_shared_atom);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_structurally_shared_atom);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_semantically_shared_atom);
    ARIADNE_TESTING_ADD_TEST(TestSmtBoolean, test_nested_formula);
    return ARIADNE_TESTING_RUN_TESTS_WITH_ARGS(argc, argv);
}
