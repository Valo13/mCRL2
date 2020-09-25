// Author(s): Olav Bunte
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//

#include "distinguisher.h"

#include "mcrl2/lts/lts_aut.h"
#include "mcrl2/lts/lts_equivalence.h"
#include "mcrl2/lts/lts_io.h"
#include "mcrl2/modal_formula/state_formula.h"
#include "mcrl2/utilities/input_input_tool.h"
#include "mcrl2/utilities/tool.h"

using namespace mcrl2;
using namespace mcrl2::log;
using namespace mcrl2::lts;
using namespace mcrl2::lts::detail;
using namespace mcrl2::utilities;

typedef utilities::tools::input_input_tool ltscompare2mcf_base;

class ltscompare2mcf_tool : public ltscompare2mcf_base
{
  private:
  std::string lts1_name = "";
  std::string lts2_name = "";
  lts_equivalence equivalence = lts_eq_none;
  bool straightforward;
  bool blocky_delta;
  bool just_before;

  template <class LTS_TYPE> bool lts_compare(void)
  {
    LTS_TYPE l1, l2;
    l1.load(lts1_name);
    l2.load(lts2_name);

    distinguisher::Distinguisher<LTS_TYPE> distinguisher(
        l1, l2, equivalence, straightforward, blocky_delta, just_before);
    state_formula f = distinguisher.distinguish();
    mCRL2log(info) << "Distinguishing formula: " << pp(f);

    return true;
  }

  protected:
  void add_options(interface_description& desc) override
  {
    ltscompare2mcf_base::add_options(desc);

    desc.add_option(
        "straightforward",
        "use the \"straightforward\" approach for generating formulas", 's');
    desc.add_option("blocky_delta",
                    "distinguish using blocks (like in Henri Korver's work) "
                    "instead of states (like in Rance Cleaveland's work); only "
                    "has effect for the non-straightforward approach",
                    'b');
    desc.add_option(
        "just_before",
        "use the semantics of the just before operator instead of the until "
        "operator when representing the branching modal operator in the modal "
        "mu-calculus",
        'j');
    desc.add_option("equivalence",
                    make_enum_argument<lts_equivalence>("NAME)")
                        .add_value(lts_eq_none, true)
                        .add_value(lts_eq_bisim)
                        .add_value(lts_eq_branching_bisim)
                        .add_value(lts_eq_weak_bisim)
                        .add_value(lts_eq_trace)
                        .add_value(lts_eq_weak_trace),
                    "use equivalence NAME :", 'e');
  };

  void parse_options(const command_line_parser& parser) override
  {
    if (parser.arguments.size() > 1)
    {
      lts1_name = parser.arguments[0];
      lts2_name = parser.arguments[1];
    }
    else
    {
      parser.error("No input files found");
    }

    equivalence = parser.option_argument_as<lts_equivalence>("equivalence");
    if (equivalence == lts_eq_none)
    {
      parser.error("Please select an equivalence");
    }

    straightforward = parser.has_option("straightforward");
    blocky_delta = parser.has_option("blocky_delta");
    just_before = parser.has_option("just_before");
  }

  public:
  ltscompare2mcf_tool()
      : ltscompare2mcf_base(
            "ltscompare2mcf", "Olav Bunte",
            "Generates counterexamples for equivalence checks in the form of a "
            "mu-calculus formula",
            "Takes two LTSs as input and produces a mu-calculus formula that "
            "describes the counterexample in case the these two LTSs are not "
            "equivalent acccording to a given equivalence")
  {
  }

  bool run() override
  {
    lts_type lts1_format = guess_format(lts1_name);
    lts_type lts2_format = guess_format(lts2_name);

    if (lts1_format == lts_none)
    {
      lts1_format = guess_format(lts1_name);
    }
    if (lts2_format == lts_none)
    {
      lts2_format = guess_format(lts2_name);
    }

    if (lts1_format != lts2_format)
    {
      throw mcrl2::runtime_error(
          "The input labelled transition systems have different types");
    }

    switch (lts1_format)
    {
    case lts_lts:
    {
      return lts_compare<lts_lts_t>();
    }
    case lts_aut:
    {
      return lts_compare<lts_aut_t>();
    }
    case lts_fsm:
    {
      return lts_compare<lts_fsm_t>();
    }
    default:
      mCRL2log(mcrl2::log::warning) << "Unsupported format";
    }

    return true;
  }
};

int main(int argc, char** argv)
{
  return ltscompare2mcf_tool().execute(argc, argv);
}
