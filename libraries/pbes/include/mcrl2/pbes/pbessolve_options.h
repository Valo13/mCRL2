// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/pbessolve_options.h
/// \brief add your file description here.

#ifndef MCRL2_PBES_PBESSOLVE_OPTIONS_H
#define MCRL2_PBES_PBESSOLVE_OPTIONS_H

#include <iomanip>
#include "mcrl2/core/detail/print_utility.h"
#include "mcrl2/data/rewrite_strategy.h"
#include "mcrl2/pbes/search_strategy.h"

namespace mcrl2 {

namespace pbes_system {

struct explorer_options
{
  data::rewrite_strategy rewrite_strategy = data::jitty;
  bool replace_constants_by_variables = false;
  bool reset_todo = false;
  search_strategy search_strategy;
};

inline
std::ostream& operator<<(std::ostream& out, const explorer_options& options)
{
  out << "rewrite-strategy = " << options.rewrite_strategy << std::endl;
  out << "replace-constants-by-variables = " << std::boolalpha << options.replace_constants_by_variables << std::endl;
  out << "reset-todo = " << std::boolalpha << options.reset_todo << std::endl;
  out << "search-strategy = " << options.search_strategy << std::endl;
  return out;
}

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_PBESSOLVE_OPTIONS_H