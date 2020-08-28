// Author(s): Olav Bunte
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

#include <set>

#include "mcrl2/lts/lts_algorithm.h"
#include "mcrl2/modal_formula/action_formula.h"
#include "mcrl2/modal_formula/state_formula.h"
#include "mcrl2/modal_formula/traverser.h"
#include "mcrl2/modal_formula/regular_formula.h"
#include "mcrl2/process/untyped_multi_action.h"

using namespace mcrl2;
using namespace mcrl2::lts;
using namespace mcrl2::lts::detail;
using namespace mcrl2::state_formulas;

namespace mcrl2::distinguisher
{

/**
 * Implements the Kanellakis-Smolka and Groote-Vaandrager algorithms that
 *   returns a mu-calculus formula according to "On Automatically Explaining
 *   Bisimulation inequivalence" from 1990 by Rance Cleaveland and "Computing
 *   Distinguishing Formulas for Branching Bisimulation" from 1991 by Henri
 *   Korver
 */
template <class LTS_TYPE> class Distinguisher
{
  typedef size_t State;
  typedef std::set<State> Block;
  typedef std::set<Block> Partition;

  typedef typename LTS_TYPE::action_label_t Action;

  private:
  int freshVarCounter = 0;
  State init1, init2;
  Block allStates;
  std::map<State, std::map<Action, std::set<State>>> nextStatesMap;

  /* Used to prevent cycles for canMoveIntoBlockRec */
  std::set<State> visited;

  /* Holds the formulas assigned to blocks for the straightforward approach */
  std::map<Block, state_formula> blockFormulas;

  /* Describes a partitioning tree of blocks for the non-straightforward
   *   approach. When a block B is split in B1 and B2 using action a and block
   *   B', B1 (can do a into B') becomes the left child, B2 (cannot do a into
   *   B') the right child and the split is labelled with a and B' */
  std::map<Block, Block> leftChild;
  std::map<Block, Block> rightChild;
  std::map<Block, Action> splitByAction;
  std::map<Block, Block> splitByBlock;

  /* The regular formula that describes any number of tau steps */
  regular_formulas::regular_formula tauStar = regular_formulas::trans_or_nil(
      regular_formulas::regular_formula(action_formulas::multi_action()));

  /* traverser for a notion of the size of a state formula */
  struct size_traverser : public state_formula_traverser<size_traverser>
  {
    typedef state_formula_traverser<size_traverser> super;
    using super::apply;
    using super::enter;
    using super::leave;

    std::size_t result;

    size_traverser() : result(0)
    {
    }

    void enter(const state_formula&)
    {
      result++;
    }
  };

#ifndef NDEBUG
  /**
   * @brief blockToString Creates a string representation of a block for
   *   debugging purposes
   * @param b The block for which to create a string representation
   * @return The string representation of the given block
   */
  std::string blockToString(Block b)
  {
    std::string s = "{";
    for (State st : b)
    {
      s += std::to_string(st) + ", ";
    }
    if (s.size() > 2)
    {
      s.pop_back();
      s.pop_back();
    }
    s += "}";
    return s;
  }

  /**
   * @brief partitionToString Creates a string representation of a partition for
   *   debugging purposes
   * @param p The partition for which to create a string representation
   * @return The string representation of the given partition
   */
  std::string partitionToString(Partition p)
  {
    std::string s = "{";
    for (Block b : p)
    {
      s += blockToString(b) + ", ";
    }
    if (s.size() > 2)
    {
      s.pop_back();
      s.pop_back();
    }
    s += "}";
    return s;
  }
#endif // !NDEBUG

  /**
   * @brief nextStates Returns the set of reachable states given a source state
   *   and an action
   * @param s A source state
   * @param a An action
   * @return The set of reachable states
   */
  std::set<State> nextStates(State s, Action a)
  {
    if (nextStatesMap.count(s) > 0 && nextStatesMap[s].count(a) > 0)
    {
      return nextStatesMap[s][a];
    }
    else
    {
      return std::set<State>();
    }
  }

  /**
   * @brief canMoveIntoBlock Returns whether a given state has a transition
   *   (after some tau-transitions) with a given action into a given block.
   *   In case not branching: exists s' \in B' : s -a-> s'
   *   In case branching: exists s_0..s_n \in B, s' \in B' :
   *                      s = s_0 -tau-> .. -tau-> s_n -a-> s'
   * @param s The state from which to move
   * @param B The block that s came from
   * @param a The action to move along
   * @param Bp The block to move into
   * @param branching Whether the equivalence is branching
   * @return Whether a given state can move with a given action into a given
   *   block
   */
  bool canMoveIntoBlock(State s, Block B, Action a, Block Bp, bool branching)
  {
    if (branching)
    {
      visited.clear();
      return canMoveIntoBlockRec(s, B, a, Bp);
    }
    else
    {
      for (State sp : Bp)
      {
        if (nextStates(s, a).count(sp) > 0)
        {
          return true;
        }
      }
      return false;
    }
  }

  /**
   * @brief canMoveIntoBlockRec Recursive part of canMoveIntoBlock in case of
   *   branching
   * @param s The state from which to move
   * @param B The block that s came from
   * @param a The action to move along
   * @param Bp The block to move into
   * @return Whether a given state can move with a given action into a given
   *   block
   */
  bool canMoveIntoBlockRec(State s, Block B, Action a, Block Bp)
  {
    visited.insert(s);
    // check if we can already directly move into Bp from s
    if (canMoveIntoBlock(s, B, a, Bp, false))
    {
      return true;
    }
    else
    {
      // do a tau transition to a state in B and try again
      for (State si : nextStates(s, Action::tau_action()))
      {
        if (B.count(si) > 0 && visited.count(si) == 0)
        {
          if (canMoveIntoBlockRec(si, B, a, Bp))
          {
            return true;
          }
        }
      }
      return false;
    }
  }

  /**
   * @brief addTauSteps Adds tau steps to the regular formula if the equivalence
   *   used is weak
   * @param aformula The regular formula of an action a
   * @param weak Whether the used equivalence is weak (or strong)
   * @return The created regular formula
   */
  regular_formulas::regular_formula
  addTauSteps(regular_formulas::regular_formula aformula, bool weak)
  {
    if (weak)
    {
      return regular_formulas::seq(tauStar,
                                   regular_formulas::seq(aformula, tauStar));
    }
    else
    {
      return aformula;
    }
  }

  /**
   * @brief createRegularFormula Creates a regular formula that represents a
   *   given action in case the compared LTSs are in the lts format
   * @param a The action for which to create a regular formula
   * @param weak Whether the used equivalence is weak (or strong)
   * @return The created regular formula
   */
  regular_formulas::regular_formula createRegularFormula(lps::multi_action a,
                                                         bool weak)
  {
    regular_formulas::regular_formula aformula =
        regular_formulas::regular_formula(
            action_formulas::multi_action(a.actions()));

    return addTauSteps(aformula, weak);
  }

  /**
   * @brief createRegularFormula Creates a regular formula that represents a
   *   given action in case the compared LTSs are in the aut or fsm format
   * @param a The action for which to create a regular formula
   * @param weak Whether the used equivalence is weak (or strong)
   * @return The created regular formula
   */
  regular_formulas::regular_formula
  createRegularFormula(lts::action_label_string a, bool weak)
  {
    regular_formulas::regular_formula aformula =
        regular_formulas::regular_formula(
            action_formulas::multi_action(process::action_list(
                {process::action(process::action_label(a, {}), {})})));

    return addTauSteps(aformula, weak);
  }

  /**
   * @brief untilFormula Creates a state formula that represents the until
   *   operator phi1<a>phi2 from HMLU, namely mu X.phi1 && (<tau>X || <a>phi2)
   * @param phi1 The first state formula in the until operator
   * @param a The action in the until operator
   * @param phi2 The second state formula in the until operator
   * @return The state formula that represents the until operator in HMLU
   */
  state_formula untilFormula(state_formula phi1, Action a, state_formula phi2)
  {
    std::string var = "X" + std::to_string(freshVarCounter++);
    return mu(var, {},
              and_(phi1, or_(may(regular_formulas::regular_formula(
                                     action_formulas::multi_action()),
                                 variable(var, {})),
                             may(createRegularFormula(a, false), phi2))));
  }

  /**
   * @brief delta Create a state formula that distinguishes two given states for
   *   the non-straightforward approach. The pseudocode is as follows:
   *   delta(s1, s2)
   *     DB := deepest block in block tree that contains s1 and s2
   *     sL := s1 if s1 in the left child, else s2
   *     sR := s1 if s1 in the right child, else s2
   *     a := action used to split DB
   *     B' := block used to split DB
   *     size := \infty
   *     SL := \{s' | sL -a-> s'\} \cap B'
   *     SR := \{s' | sR -a-> s'\}
   *     sPhi := false
   *     for sLp in SL
   *       Gamma := \emptyset
   *       for sRp \in SR
   *         Gamma := Gamma \cup \{delta(sLp, sRp)\}
   *       Phi = \bigwedge Gamma
   *       if |Phi| < size
   *         size := |Phi|
   *         sPhi := Phi
   *     if sL = s1
   *       return <a>sPhi
   *     else
   *       return -<a>sPhi
   * @param s1 The first of two states to distinguish
   * @param s2 The second of two states to distinguish
   * @param weak Whether the used equivalence is weak (or strong)
   * @return A state formula that is true on s1 but false on s2
   */
  state_formula delta(State s1, State s2, bool weak)
  {
    /* Find the deepest block DB in the split tree that contains s1 and s2.
     * Below DB, it is split into two blocks L (B1) and R (B2) using action a
     *   and splitter B' */
    Block DB = allStates;
    // sL: the state in {s1, s2} that is in L after the split
    // sR: the state in {s1, s2} that is in R after the split
    State sL, sR;
    while (true)
    {
      Block left = leftChild.at(DB);
      if (left.count(s1) > 0)
      {
        if (left.count(s2) > 0)
        {
          DB = left;
        }
        else
        {
          sL = s1;
          sR = s2;
          break;
        }
      }
      else
      {
        if (left.count(s2) > 0)
        {
          sL = s2;
          sR = s1;
          break;
        }
        else
        {
          DB = rightChild.at(DB);
        }
      }
    }

    Action a = splitByAction.at(DB);
    Block Bp = splitByBlock.at(DB);

    size_t smallestSize = SIZE_MAX;
    state_formula smallestPhi;
    // SL: all states in B' that can be reached with an a step from sR
    // cannot be empty, otherwise there is no split and s1 and s2 are equivalent
    Block SL = utilities::detail::set_intersection(nextStates(sL, a), Bp);
    // SR: all states (outside of B') that can be reached with an a step from sR
    // if empty, sL can simply be distinguished from sR with <a>true
    Block SR = nextStates(sR, a);

    /* We can distinguish sL with sR if we can distinguish a state in SL with
     *   all states in SR.
     * We try out all states in SL and pick the smallest formula.
     * We only need one state from SL since for sL we want to create a formula
     *   of the form <a>Phi, which we can satisfy by picking some a-transition
     *   into SL for which Phi holds.
     * We need every state from SR since for sR we want to create a formula of
     *   the form !<a>Phi, which we can only satisfy if after every a-transition
     *   Phi does not hold */
    for (State sLp : SL)
    {
      // create a mucalculus formula that distinguishes sLp with all states in
      //   SR by taking the conjunction of the formulas that distinguish sLp
      //   with sRp for every sRp in SR
      std::set<state_formula> Gamma;
      for (State sRp : SR)
      {
        // this recursive call eventually terminates, since sLp and sRp were
        //   split from each other earlier than the split of s1 and s2 (if not,
        //   sLp and sRp would be in the same set)
        Gamma.insert(delta(sLp, sRp, weak));
      }
      state_formula Phi = utilities::detail::join<state_formula>(
          Gamma.begin(), Gamma.end(),
          [](state_formula a, state_formula b) { return and_(a, b); }, true_());
      // if Phi using this sLp is smaller than the up to now smallest found Phi,
      //   replace it
      size_traverser t;
      t.apply(Phi);
      size_t PhiSize = t.result;
      if (PhiSize < smallestSize)
      {
        smallestSize = PhiSize;
        smallestPhi = Phi;
      }
    }

    // create the final formula <a>Phi
    state_formula dPhi = may(createRegularFormula(a, weak), smallestPhi);

    // with <a>Phi we distinguish sL from sR, but we want to distinguish s1 from
    //   s2, so we need to negate the formula in case sL == s2
    if (sL == s1)
    {
      return dPhi;
    }
    else
    {
      return not_(dPhi);
    }
  }

  /**
   * @brief split Splits a block into two blocks, one with states that can
   *   reach exactly the same blocks when following a given action, and one
   *   with states that can't. Which blocks can be reached depends on the
   *   state initially picked. The pseudocode is as follows:
   *   split(B, a, Bp)
   *     for s \in B
   *       if exists s' \in B' : s -a-> s' then
   *         B1 := B1 U {t}
   *       else
   *         B2 := B2 U {t}
   *     return B1, B2
   * @param B A block to split
   * @param a The action to split over
   * @param Bp The block to split against
   * @param branching Whether the equivalence is branching
   * @return A pair of blocks, one with states that can reach block B' when
   *   following action a and one with states that can't.
   */
  std::pair<Block, Block> split(Block B, Action a, Block Bp, bool branching)
  {
    Block B1, B2 = {};

    // collect all states that can move into exactly the same blocks
    for (State s : B)
    {
      if (canMoveIntoBlock(s, B, a, Bp, branching))
      {
        B1.insert(s);
      }
      else
      {
        B2.insert(s);
      }
    }

    return std::pair<Block, Block>(B1, B2);
  }

  public:
  /**
   * @brief distinguish Checks whether the two given LTSs <S1, s01, L, ->1> and
   *   <S2, s02, L, ->2> are equivalent. If not, returns a mu-calculus formula
   *   that is true on one LTS and false on the other. The pseudo code is as
   *   follows:
   *   bisim(l1, l2)
   *     P := {S1 U S2}
   *     changed := true
   *     while changed
   *       P2 := P1
   *       changed := false
   *       for B \in P
   *         for a \in L
   *           for Bp \in P
   *             B1, B2 := split(B, a, Bp)
   *             if B1 != {} && B2 != {}
   *               changed := true
   *               replace B in P by B1 and B2
   *               move to next block to split
   * @param l1 The first LTS to compare with
   * @param l2 The second LTS to compare with
   * @param equivalence The equivalence used
   * @param straightforward Whether to use the "straightforward" approach, which
   *   is simpler but generates larger formulas
   * @return A mu-calculus formula that is true on one LTS and false on the
   *   other if they are not bisimilar, else the mu-calculus formula true
   */
  state_formula distinguish(LTS_TYPE l1, LTS_TYPE l2,
                            lts_equivalence equivalence, bool straightforward)
  {
    // change equivalence problems to bisimulation problems where possible
    switch (equivalence)
    {
    case lts_eq_weak_bisim:
      weak_bisimulation_reduce(l1);
      weak_bisimulation_reduce(l2);
      break;

    case lts_eq_weak_trace:
      bisimulation_reduce(l1, true);
      tau_star_reduce(l1);
      bisimulation_reduce(l2, true);
      tau_star_reduce(l2);

    case lts_eq_trace:
      bisimulation_reduce(l1);
      determinise(l1);
      bisimulation_reduce(l2);
      determinise(l2);
      break;
    }

    bool weak =
        equivalence == lts_eq_weak_bisim || equivalence == lts_eq_weak_trace;
    bool branching = equivalence == lts_eq_branching_bisim;

    init1 = l1.initial_state();
    init2 = l2.initial_state() + l1.num_states();
    mcrl2::lts::detail::merge(l1, l2);
    l2.clear();

    // First put all transitions in a map for easier access
    for (transition& t : l1.get_transitions())
    {
      if (nextStatesMap.count(t.from()) == 0)
      {
        nextStatesMap[t.from()] = std::map<Action, std::set<State>>();
      }
      if (nextStatesMap[t.from()].count(l1.action_label(t.label())) == 0)
      {
        nextStatesMap[t.from()][l1.action_label(t.label())] = {};
      }
      nextStatesMap[t.from()][l1.action_label(t.label())].insert(t.to());
    }

    /* Create the partitioning */
    for (size_t s = 0; s < l1.num_states(); s++)
    {
      allStates.insert(s);
    }
    blockFormulas[allStates] = true_();

    // we'll use 2 partitions: one to refine (Pr) and one to iterate over (Pi)
    Partition Pr, Pi = {};
    Pr.insert(allStates);
    bool changed = true;

    while (changed)
    {
      Pi = Pr;
      changed = false;
      for (Block B : Pi)
      {
        bool split = false;
        for (Action a : l1.action_labels())
        {
          for (Block Bp : Pr)
          {
            if (!branching || B != Bp || a != Action::tau_action())
            {
              std::pair<Block, Block> B1B2 = this->split(B, a, Bp, branching);
              Block B1 = B1B2.first;
              Block B2 = B1B2.second;
              // if the block was actually split, also split it in Pr and move
              //   to the next block in Pi
              if (!(B1.empty() || B2.empty()))
              {
                changed = true;
                split = true;
                Pr.erase(B);
                Pr.insert(B1);
                Pr.insert(B2);

#ifndef NDEBUG
                std::cout << "Split block B = " << blockToString(B)
                          << " into blocks B1 = " << blockToString(B1)
                          << " and B2 = " << blockToString(B2)
                          << " over action " << pp(a)
                          << " using block B' = " << blockToString(Bp) << "\n";
#endif // !NDEBUG

                if (straightforward)
                {
                  // assign distinguishing formulas
                  state_formula stepFormula;
                  if (branching)
                  {
                    stepFormula = untilFormula(blockFormulas.at(B), a,
                                               blockFormulas.at(Bp));
                  }
                  else
                  {
                    stepFormula = may(createRegularFormula(a, weak),
                                      blockFormulas.at(Bp));
                  }

                  blockFormulas[B1] = and_(blockFormulas.at(B), stepFormula);
                  blockFormulas[B2] =
                      and_(blockFormulas.at(B), not_(stepFormula));

#ifndef NDEBUG
                  std::cout << "Block B1 = " << blockToString(B1)
                            << " got formula " << pp(blockFormulas.at(B1))
                            << "\n";
                  std::cout << "Block B2 = " << blockToString(B2)
                            << " got formula " << pp(blockFormulas.at(B2))
                            << "\n";
#endif // !NDEBUG
                }
                else
                {
                  // add children to the block tree
                  leftChild[B] = B1;
                  rightChild[B] = B2;
                  splitByAction[B] = a;
                  splitByBlock[B] = Bp;
                }
                break;
              }
            }
          }

          if (split)
          {
            break;
          }
        }
      }
    }

#ifndef NDEBUG
    std::cout << "Final partitioning:  " << partitionToString(Pr) << "\n";
#endif // !NDEBUG

    /* Check if the two initial states are in the same block */
    bool init1found = false;
    bool init2found = false;
    for (Block B : Pr)
    {
      for (State s : B)
      {
        if (s == init1)
        {
          init1found = true;
        }
        if (s == init2)
        {
          init2found = true;
        }
      }
      // if both are found in the same block, the two LTSs are equivalent
      if (init1found && init2found)
      {
        return true_();
      }
      // if one is in this block but the other isn't, the LTSs are not
      //   equivalent
      else if (init1found)
      {
        if (straightforward)
        {
          return blockFormulas.at(B);
        }
        else
        {
          if (branching)
          {
            return false_();
          }
          else
          {
            return delta(init1, init2, weak);
          }
        }
      }
    }

    return false_();
  }
};

} // namespace mcrl2::distinguisher
