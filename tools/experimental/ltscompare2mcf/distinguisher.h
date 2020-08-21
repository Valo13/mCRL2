// Author(s): Olav Bunte
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

#include <set>

#include "mcrl2/lts/action_label_string.h"
#include "mcrl2/lts/detail/liblts_merge.h"
#include "mcrl2/modal_formula/action_formula.h"
#include "mcrl2/modal_formula/state_formula.h"
#include "mcrl2/modal_formula/traverser.h"
#include "mcrl2/modal_formula/regular_formula.h"
#include "mcrl2/process/untyped_multi_action.h"

using namespace mcrl2;
using namespace mcrl2::lts;
using namespace mcrl2::state_formulas;
using namespace mcrl2::utilities;

namespace mcrl2::distinguisher
{

/**
 * Implements the Kanellakis-Smolka algorithm based that returns a mu-calculus
 *   formula according to "On Automatically Explaining Bisimulation
 *   inequivalence" from 1990 by Rance Cleaveland
 */
template <class LTS_TYPE> class Distinguisher
{
  typedef size_t State;
  typedef std::set<State> Block;
  typedef std::set<Block> Partition;

  typedef typename LTS_TYPE::action_label_t Action;

  private:
  State init1, init2;
  Block allStates;
  std::map<State, std::map<Action, std::set<State>>> nextStatesMap;

  /* Holds the formulas assigned to blocks for the straightforward approach */
  std::map<Block, state_formula> blockFormulas;

  /* Describes a partitioning tree of blocks for the non-straightforward
   *   approach. When a block B is split in B1 and B2 using action a and block
   *   B', B1 (can do a into B') becomes the left child, B2 (cannot do a into
   *   B') the right child and the plit is labelled with a and B' */
  std::map<Block, Block> leftChild;
  std::map<Block, Block> rightChild;
  std::map<Block, Action> splitByAction;
  std::map<Block, Block> splitByBlock;

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
   * @brief canMoveToBlock Returns whether a given state has a transition with a
   *   given action into a given block (exists s' \in B : s -a-> s')
   * @param s The state from which to move
   * @param a The action to move along
   * @param B The block to move into
   * @return Whether a given state has a transition with a given action into a
   *   given block
   */
  bool canMoveIntoBlock(State s, Action a, Block B)
  {
    for (State sp : B)
    {
      if (nextStates(s, a).count(sp) > 0)
      {
        return true;
      }
    }
    return false;
  }

  /**
   * @brief Creates a regular formula that represents a given action in case the
   *   compared LTSs are in the lts format
   * @param a The action for which to create a regular formula
   * @return The created regular formula
   */
  regular_formulas::regular_formula createRegularFormula(lps::multi_action a)
  {
    return regular_formulas::regular_formula(
        action_formulas::multi_action(a.actions()));
  }

  /**
   * @brief Creates a regular formula that represents a given action in case the
   *   compared LTSs are in the aut or fsm format
   * @param a The action for which to create a regular formula
   * @return The created regular formula
   */
  regular_formulas::regular_formula
  createRegularFormula(lts::action_label_string a)
  {
    return regular_formulas::regular_formula(
        action_formulas::multi_action(process::action_list(
            {process::action(process::action_label(a, {}), {})})));
  }

  /**
   * @brief Create a state formula that distinguishes two given states for the
   *   non-straightforward approach. The pseudocode is as follows:
   *   delta(s1, s2)
   *     DB := deepest block in block tree that contains s1 and s2
   *     sL := s1 if s1 in the left child, else s2
   *     sR := s1 if s1 in the right child, else s2
   *     a := action used to split DB
   *     B' := block used to split DB
   *     size := \infty
   *     SL := \{s' | sL -a-> s'\} \cap B'
   *     SR := \{s' | sR -a-> s'\}
   *     sPhi := false;
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
   * @return A state formula that is true on s1 but false on s2
   */
  state_formula delta(State s1, State s2)
  {
    // find the deepest block that contains s1 and s2
    Block DB = allStates;
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
    Block SL = utilities::detail::set_intersection(nextStates(sL, a), Bp);
    Block SR = nextStates(sR, a);

    // create the smallest formula
    for (State sLp : SL)
    {
      // create a conjunction of subformulas
      std::set<state_formula> Gamma;
      for (State sRp : SR)
      {
        Gamma.insert(delta(sLp, sRp));
      }
      state_formula Phi = utilities::detail::join<state_formula>(
          Gamma.begin(), Gamma.end(),
          [](state_formula a, state_formula b) { return and_(a, b); }, true_());
      // if it is smaller than the up to now smallest found Phi, replace it
      size_traverser t;
      t.apply(Phi);
      size_t PhiSize = t.result;
      if (PhiSize < smallestSize)
      {
        smallestSize = PhiSize;
        smallestPhi = Phi;
      }
    }

    state_formula dPhi = may(createRegularFormula(a), smallestPhi);
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
   * @return A pair of blocks, one with states that can reach block B' when
   *   following action a and one with states that can't.
   */
  std::pair<Block, Block> split(Block B, Action a, Block Bp)
  {
    Block B1, B2 = {};

    // collect all states that can move into exactly the same blocks
    for (State s : B)
    {
      if (canMoveIntoBlock(s, a, Bp))
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
   * @brief bisim Checks whether the two given LTSs <S1, s01, L, ->1> and <S2,
   *   s02, L, ->2> are strongly bisimilar. If not, returns a mu-calculus
   *   formula that is true on one LTS and false on the other. The pseudo code
   *   is as follows:
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
   * @param l1 The first LTS to comapre with
   * @param l2 The second LTS to compare with
   * @return A mu-calculus formula that is true on one LTS and false on the
   *   other if they are not bisimilar, else the mu-calculus formula true
   */
  state_formula distinguish(LTS_TYPE l1, LTS_TYPE l2, bool straightforward)
  {
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
            std::pair<Block, Block> B1B2 = this->split(B, a, Bp);
            Block B1 = B1B2.first;
            Block B2 = B1B2.second;
            // if the block was actually split, also split it in Pr and move to
            //   the next block in Pi
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
                        << " and B2 = " << blockToString(B2) << " over action "
                        << pp(a) << " using block B' = " << blockToString(Bp)
                        << "\n";
#endif // !NDEBUG

              if (straightforward)
              {
                // assign distinguishing formulas
                state_formula diamond =
                    may(createRegularFormula(a), blockFormulas.at(Bp));
                blockFormulas[B1] = and_(blockFormulas.at(B), diamond);
                blockFormulas[B2] = and_(blockFormulas.at(B), not_(diamond));

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

          if (split)
          {
            break;
          }
        }
      }
    }

    /* Check if the two initial states are in the same block */
    bool init1found, init2found = false;
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
          return delta(init1, init2);
        }
      }
    }

    return false_();
  }
};

} // namespace mcrl2::distinguisher
