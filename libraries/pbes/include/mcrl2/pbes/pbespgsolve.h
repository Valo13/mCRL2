// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/pbespgsolve.h
/// \brief add your file description here.

#ifndef MCRL2_PBES_PBESPGSOLVE_H
#define MCRL2_PBES_PBESPGSOLVE_H

#include "../../../../../tools/pbespgsolve/pbespgsolve.h"
#include "mcrl2/utilities/execution_timer.h"

namespace mcrl2 {

namespace pbes_system {

/// \brief Solves a pbes using a parity game solver
/// \return The solution of the pbes
inline
bool pbespgsolve(pbes<>& p, utilities::execution_timer& timer, const pbespgsolve_options& options = pbespgsolve_options())
{
  pbespgsolve_algorithm algorithm(timer, options);
  return algorithm.run(p);
}

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_PBESPGSOLVE_H
