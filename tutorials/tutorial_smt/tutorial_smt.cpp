/***************************************************************************
 *            tutorial_smt.cpp
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

/*! \file tutorial_smt.cpp
 *  \brief Ariadne SMT tutorial.
 */

#include <iostream>
#include <string>

#include "ariadne-smt.hpp"

using namespace Ariadne;
using std::cout;

namespace {

void section(const std::string& title) {
    cout << "\n== " << title << " ==\n";
}

template<class T>
void show(const std::string& label, const T& value) {
    cout << label << ": " << value << "\n";
}

} // namespace

int main() {
    section("Bounded real epsilon-SMT");

    RealVariable x("x");
    RealVariable y("y");
    RealExpression ex=x;
    RealExpression ey=y;
    RealSpace space({x,y});

    ExactBoxType domain({
        {-2.0_x,2.0_x},
        {-2.0_x,2.0_x}
    });

    ContinuousPredicate formula=
        (sqr(ex)+sqr(ey)<=1)
        && (ex>=0);

    SmtSolver solver(SmtSolverConfiguration(0.125_x));
    SmtResult result=solver.solve(space,domain,formula);

    show("formula",formula);
    show("status",result.status());
    show("epsilon-satisfiable",result.is_epsilon_sat());
    if(result.has_witness()) {
        show("witness box",result.witness());
    }
    show("boxes processed",result.statistics().boxes_processed);
    show("theory checks",result.statistics().theory_checks);

    section("An unsatisfiable conjunction");

    ContinuousPredicate contradiction=(ex>=1)&&(ex<=0);
    SmtResult unsat=solver.solve(space,domain,contradiction);

    show("formula",contradiction);
    show("status",unsat.status());
    show("unsatisfiable",unsat.is_unsat());

    section("Boolean combinations");

    ContinuousPredicate disjunction=(ex<-1)||(ex>1);
    SmtResult boolean_result=solver.solve(space,domain,disjunction);

    show("formula",disjunction);
    show("status",boolean_result.status());

    return 0;
}
