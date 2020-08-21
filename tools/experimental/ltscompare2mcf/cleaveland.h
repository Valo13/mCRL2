// Author(s): Olav Bunte
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

#include <set>

#include "mcrl2/modal_formula/state_formula.h"
#include "mcrl2/lts/detail/liblts_merge.h"

using namespace mcrl2::state_formulas;
using namespace mcrl2::lts;
using namespace mcrl2::utilities;

namespace mcrl2::cleaveland
{

/**
 * Implements the Kanellakis-Smolka algorithm based on
 * https://www.ru.is/faculty/luca/PAPERS/algobisimchapter.pdf that returns a
 * mu-calculus formula according to the first method described in "On
 * Automatically Explaining Bisimulation inequivalence" from 1990 by Rance
 * Cleaveland
 */
template <class LTS_TYPE> class Cleaveland
{
  typedef size_t State;
  typedef std::set<State> Block;
  typedef std::set<Block> Partition;

  typedef typename LTS_TYPE::action_label_t Action;

  private:
  State init1, init2;
  std::map<State, std::map<Action, std::set<State>>> nextStates;

  /**
   * @brief nextState Returns the set of reachable states given a source state
   *   and an action
   * @param s A source state
   * @param a An action
   * @returns The set of reachable states
   */
  std::set<State> nextState(State s, Action a)
  {
    if (nextStates.count(s) > 0 && nextStates[s].count(a) > 0)
    {
      return nextStates[s][a];
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
   * @returns  whether a given state has a transition with a given action into a
   *   given block
   */
  bool canMoveIntoBlock(State s, Action a, Block B)
  {
    for (State sp : B)
    {
      if (nextState(s, a).count(sp) == 1)
      {
        return true;
      }
    }
    return false;
  }

  /**
   * @brief split Splits a block into two blocks, one with states that can
   *   reach exactly the same blocks when following a given action, and one
   *   with states that can't. Which blocks can be reached depends on the
   *   state initially picked. The pseudocode is as follows: split(B, a, P2)
   *     pick s \in B
   *     P2' := {B' \in P2 | exists s' \in B' : s -a-> s'}
   *     B1, B2 := {}
   *     for t \in B
   *       if {B' \in P2 | exists t' \in B' : t -a-> t'} == P2 then
   *         B1 := B1 U {t}
   *       else
   *         B2 := B2 U {t}
   *       endif
   *     endfor
   *     return B1, B2
   * @param B A block to split
   * @param a The action to split over
   * @param P2 The block to split against
   * @returns A pair of blocks, one with states that can reach the same
   * blocks when following a given action, and one with states that can't.
   */
  std::pair<Block, Block> split(Block B, Action a, Partition P2)
  {
    Block B1, B2 = {};

    // pick a state
    State s = *B.cbegin();

    // compute the set of blocks it can move into via an a action
    Partition P2p = {};
    for (Block Bp : P2)
    {
      if (canMoveIntoBlock(s, a, Bp))
      {
        P2p.insert(Bp);
      }
    }

    // collect all states that can move into exactly the same blocks
    for (State t : B)
    {
      bool handled = false;
      for (Block Bp : P2)
      {
        if (canMoveIntoBlock(t, a, Bp) != (P2p.count(Bp) == 1))
        {
          B2.insert(t);
          handled = true;
          break;
        }
      }
      if (!handled)
      {
        B1.insert(t);
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
   *     P1 := {S1 U S2}
   *     P2 := {}
   *     changed := true
   *     while changed
   *       P2 := P1
   *       P1 := {}
   *       changed := false
   *       for B \in P2
   *         for a \in L
   *           B1, B2 := split(B, a, P2)
   *           if B1 != {} && B2 != {}
   *             changed := true
   *           P1 := P1 U {B1, B2}-{{}}
   * @param l1 The first LTS to comapre with
   * @param l2 The second LTS to compare with
   * @returns A mu-calculus formula that is true on one LTS and false on the
   *   other if they are not bisimilar, else the mu-calculus formula true
   */
  state_formula bisim(LTS_TYPE l1, LTS_TYPE l2)
  {
    init1 = l1.initial_state();
    init2 = l2.initial_state() + l1.num_states();
    mcrl2::lts::detail::merge(l1, l2);
    l2.clear();

    // First put all transitions in a map for easier access
    for (transition& t : l1.get_transitions())
    {
      if (nextStates.count(t.from()) == 0)
      {
        nextStates[t.from()] = std::map<Action, std::set<State>>();
      }
      if (nextStates[t.from()].count(l1.action_label(t.label())) == 0)
      {
        nextStates[t.from()][l1.action_label(t.label())] = {};
      }
      else
      {
        nextStates[t.from()][l1.action_label(t.label())].insert(t.to());
      }
    }

    /* Create the partitioning */
    Block S;
    for (size_t s = 0; s < l1.num_states(); s++)
    {
      S.insert(s);
    }
    Partition P1, P2 = {};
    P1.insert(S);
    bool changed = true;
    while (changed)
    {
      P2 = P1;
      P1 = {};
      changed = false;
      for (Block B : P2)
      {
        for (Action a : l1.action_labels())
        {
          std::pair<Block, Block> B1B2 = split(B, a, P2);
          // check if the block was actually split
          if (!(B1B2.first.empty() || B1B2.second.empty()))
          {
            changed = true;
          }
          // add the new blocks to P1
          if (!B1B2.first.empty())
          {
            P1.insert(B1B2.first);
          }
          if (!B1B2.second.empty())
          {
            P1.insert(B1B2.second);
          }
        }
      }
    }

    /* Check if the two initial states are in the same block */
    bool init1found, init2found = false;
    for (Block B : P1)
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
      // equivalent
      else if (init1found || init2found)
      {
        break;
      }
    }

    /* Create distinguishing formula */
    return false_();
  }
};

} // namespace mcrl2::cleaveland
