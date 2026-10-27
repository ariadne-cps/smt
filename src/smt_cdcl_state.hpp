/***************************************************************************
 *            smt_cdcl_state.hpp
 *
 *  Copyright 2026 Luca Geretti
 ****************************************************************************/

/*
 *  This file is part of Ariadne SMT.
 *  SPDX-License-Identifier: GPL-3.0-or-later
 */

#ifndef ARIADNE_SMT_CDCL_STATE_HPP
#define ARIADNE_SMT_CDCL_STATE_HPP

#include <algorithm>
#include <cstdint>
#include <limits>
#include <optional>
#include <stdexcept>
#include <vector>
#include "smt/smt_solver.hpp"
#include "smt/boolean_literal.hpp"

namespace Ariadne {

//! \brief Propositional CDCL trail, clauses, unit propagation and 1-UIP analysis.
//! \details Transitional SMT-local implementation. No theory checking happens here;
//! the derived SMT search supplies theory conflicts and certified witnesses.
class SmtCdclState {
  protected:
    SmtCdclState(SmtBooleanEncoding const& encoding, SizeType learned_clause_limit)
        : _encoding(encoding),
          _learned_clause_limit(learned_clause_limit),
          _assignment(encoding.variable_count())
    {
        _trail.reserve(encoding.variable_count());
        _decision_level_markers.reserve(encoding.variable_count()+1u);
        _decision_level_markers.push_back(0u);
    }

    struct AssignmentInfo {
        int8_t value = -1;
        SizeType decision_level = 0u;
        std::optional<SizeType> reason_clause;
    };

    struct ConflictAnalysis {
        std::vector<BooleanLiteral> learned_clause;
        SizeType backjump_level = 0u;
    };

    Bool _literal_true(BooleanLiteral literal) const
    {
        SizeType variable=literal.variable();
        int8_t value=_assignment[variable].value;
        int8_t expected_value=static_cast<int8_t>(literal.positive());
        return value==expected_value;
    }

    Void _assign_literal(BooleanLiteral literal, std::optional<SizeType> reason_clause = std::nullopt)
    {
        SizeType variable=literal.variable();
        int8_t value=static_cast<int8_t>(literal.positive());
        AssignmentInfo& assignment=_assignment[variable];
        assignment.value=value;
        assignment.decision_level=this->_decision_level();
        assignment.reason_clause=reason_clause;
        _trail.push_back(variable);
    }

    SizeType _original_clause_count() const
    {
        return _encoding.clauses().size();
    }

    SizeType _clause_count() const
    {
        return this->_original_clause_count()+_learned_clauses.size();
    }

    SmtBooleanEncoding::Clause const& _clause(SizeType index) const
    {
        if(index<this->_original_clause_count()) {
            return _encoding.clauses()[index];
        }
        return _learned_clauses[index-this->_original_clause_count()];
    }

    Bool _is_learned_clause(SizeType index) const
    {
        return SmtSolverTestSupport::clause_is_learned(
            index,this->_original_clause_count());
    }

    SizeType _add_learned_clause(std::vector<BooleanLiteral> const& clause, Bool theory_clause = false)
    {
        _learned_clauses.emplace_back(clause.begin(),clause.end());
        _learned_clause_is_theory.push_back(theory_clause);
        _learned_clause_activity.push_back(1u);
        _learned_clause_generation.push_back(_statistics.learned_clauses);
        ++_statistics.learned_clauses;
        if(theory_clause) {
            ++_statistics.theory_learned_clauses;
            _statistics.theory_learned_clause_literals+=clause.size();
        } else {
            _statistics.peak_active_non_theory_learned_clauses=std::max(
                _statistics.peak_active_non_theory_learned_clauses,
                this->_active_non_theory_learned_clause_count());
        }
        return this->_original_clause_count()+_learned_clauses.size()-1u;
    }

    Bool _is_theory_learned_clause(SizeType index) const
    {
        return SmtSolverTestSupport::learned_clause_is_theory(
            index,this->_original_clause_count(),_learned_clause_is_theory);
    }

    SizeType _active_non_theory_learned_clause_count() const
    {
        SizeType count=0u;
        for(SizeType i=0u; i<_learned_clauses.size(); ++i) {
            if(not _learned_clause_is_theory[i]) {
                ++count;
            }
        }
        return count;
    }

    Bool _learned_clause_locked(SizeType index) const
    {
        for(AssignmentInfo const& assignment:_assignment) {
            if(SmtSolverTestSupport::assignment_locks_clause(
                    assignment.value,assignment.reason_clause,index)) {
                return true;
            }
        }
        return false;
    }

    Void _bump_learned_clause_activity(SizeType index)
    {
        if(not this->_is_learned_clause(index)) {
            return;
        }
        SizeType learned_index=index-this->_original_clause_count();
        ++_learned_clause_activity[learned_index];
        ++_statistics.learned_clause_activity_bumps;
    }

    Void _maybe_prune_learned_clauses(SizeType protected_clause)
    {
        SizeType const limit=_learned_clause_limit;
        SizeType active=this->_active_non_theory_learned_clause_count();
        if(active<=limit) {
            return;
        }

        ++_statistics.learned_clause_pruning_runs;
        std::vector<SmtSolverTestSupport::LearnedClausePruningEntry> entries;
        entries.reserve(_learned_clauses.size());
        for(SizeType i=0u; i<_learned_clauses.size(); ++i) {
            SizeType clause_index=this->_original_clause_count()+i;
            SizeType const current_generation=_statistics.learned_clauses;
            SizeType const clause_generation=_learned_clause_generation[i];
            entries.push_back({
                true,
                _learned_clause_is_theory[i],
                current_generation<=clause_generation+2u,
                _learned_clauses[i].size()<=2u,
                _learned_clause_activity[i]>1u,
                clause_index==protected_clause,
                this->_learned_clause_locked(clause_index),
                _learned_clause_activity[i],
                _learned_clauses[i].size()
            });
        }
        std::vector<SizeType> candidates=
            SmtSolverTestSupport::learned_clause_pruning_candidates(entries);

        _statistics.learned_clauses_pruned+=
            SmtSolverTestSupport::apply_learned_clause_pruning(
                candidates,active,limit);
    }

    Bool _unit_propagate()
    {
        _last_boolean_conflict_clause.reset();
        Bool changed=true;
        while(changed) {
            changed=false;
            for(SizeType clause_index=0u; clause_index<this->_clause_count(); ++clause_index) {
                auto const& clause=this->_clause(clause_index);
                Bool satisfied=false;
                SizeType unassigned_count=0u;
                std::optional<BooleanLiteral> unit_literal;

                for(BooleanLiteral literal:clause) {
                    SizeType variable=literal.variable();
                    int8_t value=_assignment[variable].value;
                    if(value<0) {
                        ++unassigned_count;
                        unit_literal=literal;
                    } else if(this->_literal_true(literal)) {
                        satisfied=true;
                        break;
                    }
                }

                if(satisfied) {
                    continue;
                }

                if(unassigned_count==0u) {
                    ++_statistics.boolean_conflicts;
                    this->_bump_learned_clause_activity(clause_index);
                    _last_boolean_conflict_clause=clause_index;
                    return false;
                }

                if(unassigned_count==1u) {
                    this->_assign_literal(*unit_literal,clause_index);
                    ++_statistics.boolean_propagations;
                    ++_statistics.boolean_reasoned_propagations;
                    if(this->_is_learned_clause(clause_index)) {
                        this->_bump_learned_clause_activity(clause_index);
                        ++_statistics.learned_clause_propagations;
                        if(this->_is_theory_learned_clause(clause_index)) {
                            ++_statistics.theory_learned_clause_propagations;
                        }
                    }
                    changed=true;
                }
            }
        }
        return true;
    }

    Bool _clause_contains_variable(std::vector<BooleanLiteral> const& clause, SizeType variable) const
    {
        for(BooleanLiteral literal:clause) {
            SizeType literal_variable=literal.variable();
            if(literal_variable==variable) {
                return true;
            }
        }
        return false;
    }

    SizeType _current_level_literal_count(std::vector<BooleanLiteral> const& clause) const
    {
        SizeType count=0u;
        for(BooleanLiteral literal:clause) {
            SizeType variable=literal.variable();
            if(_assignment[variable].decision_level==this->_decision_level()) {
                ++count;
            }
        }
        return count;
    }

    std::vector<BooleanLiteral> _resolve_on_variable(
        std::vector<BooleanLiteral> const& lhs,
        SmtBooleanEncoding::Clause const& rhs,
        SizeType variable) const
    {
        return SmtSolverTestSupport::resolve_clause_on_variable(lhs,rhs,variable);
    }

    ConflictAnalysis _analyze_boolean_conflict(SizeType conflict_clause_index)
    {
        this->_bump_learned_clause_activity(conflict_clause_index);
        ConflictAnalysis analysis;
        auto const& conflict_clause=this->_clause(conflict_clause_index);
        analysis.learned_clause.assign(conflict_clause.begin(),conflict_clause.end());

        while(this->_current_level_literal_count(analysis.learned_clause)>1u) {
            auto iter=_trail.rbegin();
            for(;;) {
                SizeType pivot_variable=*iter;
                AssignmentInfo const& assignment=_assignment[pivot_variable];
                Bool const current_level=
                    assignment.decision_level==this->_decision_level();
                Bool const has_reason=assignment.reason_clause.has_value();
                Bool const appears_in_clause=this->_clause_contains_variable(
                    analysis.learned_clause,pivot_variable);
                Bool const resolvable=
                    static_cast<unsigned>(current_level)
                    & static_cast<unsigned>(has_reason)
                    & static_cast<unsigned>(appears_in_clause);
                if(resolvable) {
                    SizeType reason_index=*assignment.reason_clause;
                    this->_bump_learned_clause_activity(reason_index);
                    analysis.learned_clause=this->_resolve_on_variable(
                        analysis.learned_clause,
                        this->_clause(reason_index),
                        pivot_variable);
                    break;
                }
                ++iter;
            }
        }

        SizeType current_level=this->_decision_level();
        SizeType backjump_level=0u;
        for(BooleanLiteral literal:analysis.learned_clause) {
            SizeType variable=literal.variable();
            SizeType level=_assignment[variable].decision_level;
            if(level!=current_level) {
                backjump_level=std::max(backjump_level,level);
            }
        }
        analysis.backjump_level=backjump_level;
        return analysis;
    }

    SizeType _next_unassigned_variable() const
    {
        for(SizeType variable=0u; variable<_encoding.variable_count(); ++variable) {
            if(_assignment[variable].value<0) {
                return variable;
            }
        }
        return _encoding.variable_count();
    }

    SizeType _decision_level() const
    {
        return _decision_level_markers.size()-1u;
    }

    Void _push_decision_level()
    {
        _decision_level_markers.push_back(_trail.size());
        _statistics.max_decision_level=std::max(
            _statistics.max_decision_level,this->_decision_level());
    }

    Void _backtrack_to_level(SizeType level)
    {
        SizeType marker=_decision_level_markers[level];
        while(_trail.size()>marker) {
            SizeType variable=_trail.back();
            _trail.pop_back();
            _assignment[variable]=AssignmentInfo();
        }
        _decision_level_markers.resize(level+1u);
    }


    SmtBooleanEncoding const& _encoding;
    SizeType _learned_clause_limit;
    std::vector<AssignmentInfo> _assignment;
    std::vector<SizeType> _trail;
    std::vector<SizeType> _decision_level_markers;
    std::vector<SmtBooleanEncoding::Clause> _learned_clauses;
    std::vector<Bool> _learned_clause_is_theory;
    std::vector<SizeType> _learned_clause_activity;
    std::vector<SizeType> _learned_clause_generation;
    std::optional<SizeType> _last_boolean_conflict_clause;
    SmtSearchStatistics _statistics;
};

} // namespace Ariadne

#endif // ARIADNE_SMT_CDCL_STATE_HPP
