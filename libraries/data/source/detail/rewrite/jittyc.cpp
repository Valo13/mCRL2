// Author(s): Muck van Weerdenburg
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file jittyc.cpp

#include "boost.hpp" // precompiled headers

#include "mcrl2/data/detail/rewrite.h"

#ifdef MCRL2_JITTYC_AVAILABLE

#define NAME "rewr_jittyc"

#include <utility>
#include <string>
#include <sstream>
#include <stdexcept>
#include <cstdio>
#include <cstdlib>
#include <unistd.h>
#include <cerrno>
#include <cstring>
#include <cassert>
#include <sstream>
#include "mcrl2/utilities/detail/memory_utility.h"
#include "mcrl2/utilities/logger.h"
#include "mcrl2/atermpp/aterm_access.h"
#include "mcrl2/core/print.h"
#include "mcrl2/core/detail/struct_core.h"
#include "mcrl2/data/detail/rewrite/jittyc.h"
#include "mcrl2/data/traverser.h"

using namespace mcrl2::core;
using namespace mcrl2::core::detail;
using namespace std;
using namespace atermpp;
using namespace mcrl2::log;

namespace mcrl2
{
namespace data
{
namespace detail
{

static atermpp::function_symbol afunS, afunM, afunF, afunN, afunD, afunR, afunCR, afunC, afunX, afunRe, afunCRe, afunMe;
static aterm dummy;
static atermpp::function_symbol afunARtrue, afunARfalse, afunARand, afunARor, afunARvar;
static aterm_appl ar_true, ar_false;

#define isS(x) x.function()==afunS
#define isM(x) x.function()==afunM
#define isF(x) x.function()==afunF
#define isN(x) x.function()==afunN
#define isD(x) x.function()==afunD
#define isR(x) x.function()==afunR
#define isCR(x) x.function()==afunCR
#define isC(x) x.function()==afunC
#define isX(x) x.function()==afunX
#define isRe(x) x.function()==afunRe
#define isCRe(x) x.function()==afunCRe
#define isMe(x) x.function()==afunMe

static size_t is_initialised = 0;

static void initialise_common()
{
  if (is_initialised == 0)
  {
    afunS = atermpp::function_symbol("@@S",2); // Store term ( target_variable, result_tree )
    afunM = atermpp::function_symbol("@@M",3); // Match term ( match_variable, true_tree , false_tree )
    afunF = atermpp::function_symbol("@@F",3); // Match function ( match_function, true_tree, false_tree )
    afunN = atermpp::function_symbol("@@N",1); // Go to next parameter ( result_tree )
    afunD = atermpp::function_symbol("@@D",1); // Go down a level ( result_tree )
    afunR = atermpp::function_symbol("@@R",1); // End of tree ( matching_rule )
    afunCR = atermpp::function_symbol("@@CR",2); // End of tree ( condition, matching_rule )
    afunC = atermpp::function_symbol("@@C",3); // Check condition ( condition, true_tree, false_tree )
    afunX = atermpp::function_symbol("@@X",0); // End of tree
    afunRe = atermpp::function_symbol("@@Re",2); // End of tree ( matching_rule , vars_of_rule)
    afunCRe = atermpp::function_symbol("@@CRe",4); // End of tree ( condition, matching_rule, vars_of_condition, vars_of_rule )
    afunMe = atermpp::function_symbol("@@Me",2); // Match term ( match_variable, variable_index )

    dummy = gsMakeNil();

    afunARtrue = atermpp::function_symbol("@@true",0);
    afunARfalse = atermpp::function_symbol("@@false",0);
    afunARand = atermpp::function_symbol("@@and",2);
    afunARor = atermpp::function_symbol("@@or",2);
    afunARvar = atermpp::function_symbol("@@var",1);
    ar_true = atermpp::aterm_appl(afunARtrue);
    ar_false = atermpp::aterm_appl(afunARfalse);
  }

  is_initialised++;
}

static void finalise_common()
{
  is_initialised--;
}

#define is_ar_true(x) (x==ar_true)
#define is_ar_false(x) (x==ar_false)
#define is_ar_and(x) (x.function()==afunARand)
#define is_ar_or(x) (x.function()==afunARor)
#define is_ar_var(x) (x.function()==afunARvar)

// Prototype
static aterm toInner_list_odd(const data_expression &t);

static aterm_appl make_ar_true()
{
  return ar_true;
}

static aterm_appl make_ar_false()
{
  return ar_false;
}

static aterm_appl make_ar_and(const aterm_appl &x, const aterm_appl &y)
{
  if (is_ar_true(x))
  {
    return y;
  }
  else if (is_ar_true(y))
  {
    return x;
  }
  else if (is_ar_false(x) || is_ar_false(y))
  {
    return make_ar_false();
  }

  return aterm_appl(afunARand,static_cast<aterm>(x),static_cast<aterm>(y));
}

static aterm_appl make_ar_or(aterm_appl x, aterm_appl y)
{
  if (is_ar_false(x))
  {
    return y;
  }
  else if (is_ar_false(y))
  {
    return x;
  }
  else if (is_ar_true(x) || is_ar_true(y))
  {
    return make_ar_true();
  }

  return aterm_appl(afunARor,static_cast<aterm>(x),static_cast<aterm>(y));
}

static aterm_appl make_ar_var(int var)
{
  return atermpp::aterm_appl(afunARvar,atermpp::aterm_int(var));
}

static size_t num_int2aterms = 0;
static atermpp::detail::_aterm** int2aterms = NULL; // An array with prepared aterm_int's.
static atermpp::detail::_aterm* get_int2aterm_value(int i)
{
  assert(i >= 0);
  if (((size_t) i) >= num_int2aterms)
  {
    size_t old_num = num_int2aterms;
    num_int2aterms = i+1;

    int2aterms = (atermpp::detail::_aterm**) realloc(int2aterms,num_int2aterms*sizeof(aterm));
    if (int2aterms == NULL)
    {
      throw mcrl2::runtime_error("Cannot allocate enough memory.");
    }
    for (size_t j=old_num; j < num_int2aterms; j++)
    {
      int2aterms[j] = NULL;
    }
    for (; old_num < num_int2aterms; old_num++)
    {
      int2aterms[old_num] = reinterpret_cast<atermpp::detail::_aterm*>( &*atermpp::aterm_int(old_num));
    }
  }
  return int2aterms[i];
}

static atermpp::detail::_aterm* get_int2aterm_value(const aterm_int &i)
{
  return get_int2aterm_value(i.value());
}

static std::vector <aterm_appl> rewr_appls;

static void set_rewrappl_value(const size_t i)
{
  while (rewr_appls.size()<i+1)
  {
    rewr_appls.push_back(Apply0(atermpp::aterm_int(rewr_appls.size())));
  }
}

const aterm_appl &get_rewrappl_value_without_check(const size_t i)
{
  assert(i<rewr_appls.size());
  return rewr_appls[i];
}

static aterm_appl get_rewrappl_value(const size_t i)
{
  set_rewrappl_value(i);
  return rewr_appls[i];
}

atermpp::aterm_appl RewriterCompilingJitty::toRewriteFormat(const data_expression &t)
{
  size_t old_opids = get_num_opids();

  atermpp::aterm_appl r = toInner(t,true);

  if (old_opids != get_num_opids())
  {
    need_rebuild = true;
  }

  return r;
}

/* data_expression RewriterCompilingJitty::fromRewriteFormat(const atermpp::aterm_appl t)
{
  return fromInner(t);
} */

static char* whitespace_str = NULL;
static int whitespace_len;
static int whitespace_pos;
static char* whitespace(int len)
{
  int i;

  if (whitespace_str == NULL)
  {
    whitespace_str = (char*) malloc((2*len+1)*sizeof(char));
    for (i=0; i<2*len; i++)
    {
      whitespace_str[i] = ' ';
    }
    whitespace_len = 2*len;
    whitespace_pos = len;
    whitespace_str[whitespace_pos] = 0;
  }
  else
  {
    if (len > whitespace_len)
    {
      whitespace_str = (char*) realloc(whitespace_str,(2*len+1)*sizeof(char));
      for (i=whitespace_len; i<2*len; i++)
      {
        whitespace_str[i] = ' ';
      }
      whitespace_len = 2*len;
    }

    whitespace_str[whitespace_pos] = ' ';
    whitespace_pos = len;
    whitespace_str[whitespace_pos] = 0;
  }

  return whitespace_str;
}


static void term2seq(const aterm &t, aterm_list* s, int* var_cnt)
{
  if (t.type_is_int())
  {
    term2seq(ATmakeList1(t),s,var_cnt);
  }
  else if (t.type()==AT_APPL)
  {
    if (gsIsDataVarId((aterm_appl) t))
    {
      aterm store = atermpp::aterm_appl(afunS, t,dummy);

      if (std::find(s->begin(),s->end(),store) != s->end())
      {
        *s = push_front<aterm>(*s, static_cast<atermpp::aterm>(atermpp::aterm_appl(afunM,t,dummy,dummy)));
      }
      else
      {
        (*var_cnt)++;
        *s = push_front<aterm>(*s, store);
      }
    }
    else
    {
      int arity = t.function().arity(); 

      *s = push_front<aterm>(*s, atermpp::aterm_appl(afunF,atermpp::aterm_cast<const aterm_appl>(t)(0),dummy,dummy));

      for (int i=1; i<arity; ++i)
      {
        term2seq(atermpp::aterm_cast<const aterm_appl>(t)(i),s,var_cnt);
        if (i<arity-1)
        {
          *s = push_front<aterm>(*s, atermpp::aterm_appl(afunN,dummy));
        }
      }
      *s = push_front<aterm>(*s, atermpp::aterm_appl(afunD,dummy));
    }
  }
  else
  {
    assert(0);
  }

}

static void get_used_vars_aux(const aterm &t, aterm_list* vars)
{
  using namespace atermpp;
  if (t.type_is_list())
  {
    const atermpp::aterm_list &l=atermpp::aterm_cast<const aterm_list>(t);
    for (aterm_list::const_iterator i=l.begin(); i!=l.end(); ++i)
    {
      get_used_vars_aux(*i,vars);
    }
  }
  else if (t.type()==AT_APPL)
  {
    if (gsIsDataVarId((aterm_appl) t))
    {
      if (find(vars->begin(),vars->end(),t) == vars->end())
      {
        *vars = push_front<aterm>(*vars,t);
      }
    }
    else
    {
      int a = t.function().arity(); 
      for (int i=0; i<a; i++)
      {
        get_used_vars_aux(aterm_cast<const aterm_appl>(t)(i),vars);
      }
    }
  }
}

static aterm_list get_used_vars(const aterm &t)
{
  aterm_list l;

  get_used_vars_aux(t,&l);

  return l;
}

static aterm_list create_sequence(const data_equation &rule, int* var_cnt, const aterm_int &true_inner)
{
  aterm_appl pat = toInner(rule.lhs(),true);
  int pat_arity = pat.function().arity(); 
  aterm cond = toInner_list_odd(rule.condition());
  aterm rslt = toInner_list_odd(rule.rhs());
  aterm_list rseq;

  for (int i=1; i<pat_arity; ++i)
  {
    term2seq(pat(i),&rseq,var_cnt);
    if (i<pat_arity-1)
    {
      rseq = push_front<aterm>(rseq, atermpp::aterm_appl(afunN,dummy));
    }
  }

  if (cond.type_is_int() && cond==true_inner)
  {
    rseq = push_front<aterm>(rseq,atermpp::aterm_appl(afunRe,rslt,get_used_vars(rslt)));
  }
  else
  {
    rseq = push_front<aterm>(rseq, atermpp::aterm_appl(afunCRe,cond,rslt, get_used_vars(cond), get_used_vars(rslt)));
  }

  return reverse(rseq);
}


// Structure for build_tree paramters
typedef struct
{
  aterm_list Flist;   // List of sequences of which the first action is an F
  aterm_list Slist;   // List of sequences of which the first action is an S
  aterm_list Mlist;   // List of sequences of which the first action is an M
  aterm_list stack;   // Stack to maintain the sequences that do not have to
  // do anything in the current term
  aterm_list upstack; // List of sequences that have done an F at the current
  // level
} build_pars;

static void initialise_build_pars(build_pars* p)
{
  p->Flist = aterm_list();
  p->Slist = aterm_list();
  p->Mlist = aterm_list();
  p->stack = ATmakeList1(aterm_list());
  p->upstack = aterm_list();
}

static aterm_list add_to_stack(const aterm_list &stack, aterm_list seqs, aterm_appl* r, aterm_list* cr)
{
  if (stack.empty())
  {
    return stack;
  }

  aterm_list l;
  aterm_list h = ATLgetFirst(stack);

  for (; !seqs.empty(); seqs=ATgetNext(seqs))
  {
    aterm_list e = ATLgetFirst(seqs);

    if (isD(ATAgetFirst(e)))
    {
      l = push_front<aterm>(l,ATgetNext(e));
    }
    else if (isN(ATAgetFirst(e)))
    {
      h = push_front<aterm>(h,ATgetNext(e));
    }
    else if (isRe(ATAgetFirst(e)))
    {
      *r = ATAgetFirst(e);
    }
    else
    {
      *cr = push_front<aterm>(*cr,ATgetFirst(e));
    }
  }

  return push_front<aterm>(add_to_stack(ATgetNext(stack),l,r,cr),h);
}

static void add_to_build_pars(build_pars* pars, aterm_list seqs, aterm_appl* r, aterm_list* cr)
{
  aterm_list l;

  for (; !seqs.empty(); seqs=ATgetNext(seqs))
  {
    aterm_list e = ATLgetFirst(seqs);

    if (isD(ATAgetFirst(e)) || isN(ATAgetFirst(e)))
    {
      l = push_front<aterm>(l,e);
    }
    else if (isS(ATAgetFirst(e)))
    {
      pars->Slist = push_front<aterm>(pars->Slist,e);
    }
    else if (isMe(ATAgetFirst(e)))     // M should not appear at the head of a seq
    {
      pars->Mlist = push_front<aterm>(pars->Mlist,e);
    }
    else if (isF(ATAgetFirst(e)))
    {
      pars->Flist = push_front<aterm>(pars->Flist,e);
    }
    else if (isRe(ATAgetFirst(e)))
    {
      *r = ATAgetFirst(e);
    }
    else
    {
      *cr = push_front<aterm>(*cr,ATgetFirst(e));
    }
  }

  pars->stack = add_to_stack(pars->stack,l,r,cr);
}

static char tree_var_str[20];
static aterm_appl createFreshVar(aterm_appl sort,int* i)
{
  sprintf(tree_var_str,"@var_%i",(*i)++);
  return gsMakeDataVarId(gsString2ATermAppl(tree_var_str),sort);
}

static aterm_list subst_var(aterm_list l, const aterm_appl &old, const aterm &new_val, const aterm &num, const aterm_list &substs)
{
  if (l.empty())
  {
    return l;
  }

  aterm_appl head = (aterm_appl) ATgetFirst(l);
  l = ATgetNext(l);

  if (isM(head))
  {
    if (ATisEqual(ATgetArgument(head,0),old))
    {
      head = atermpp::aterm_appl(afunMe,new_val,num);
    }
  }
  else if (isCRe(head))
  {
    aterm_list l = (aterm_list) ATgetArgument(head,2);
    aterm_list m ;
    for (; !l.empty(); l=ATgetNext(l))
    {
      if (ATisEqual(ATgetFirst(l),old))
      {
        m = push_front<aterm>(m,num);
      }
      else
      {
        m = push_front<aterm>(m,ATgetFirst(l));
      }
    }
    l = (aterm_list) ATgetArgument(head,3);
    aterm_list n;
    for (; !l.empty(); l=ATgetNext(l))
    {
      if (ATisEqual(ATgetFirst(l),old))
      {
        n = push_front<aterm>(n,num);
      }
      else
      {
        n = push_front<aterm>(n,ATgetFirst(l));
      }
    }
    head = atermpp::aterm_appl(afunCRe,gsSubstValues(substs,ATgetArgument(head,0),true),gsSubstValues(substs,ATgetArgument(head,1),true),m, n);
  }
  else if (isRe(head))
  {
    aterm_list l = (aterm_list) ATgetArgument(head,1);
    aterm_list m ;
    for (; !l.empty(); l=ATgetNext(l))
    {
      if (ATisEqual(ATgetFirst(l),old))
      {
        m = push_front<aterm>(m,num);
      }
      else
      {
        m = push_front<aterm>(m,ATgetFirst(l));
      }
    }
    head = atermpp::aterm_appl(afunRe,gsSubstValues(substs,ATgetArgument(head,0),true),m);
  }

  return push_front<aterm>(subst_var(l,old,new_val,num,substs), head);
}

static int* treevars_usedcnt;

static void inc_usedcnt(aterm_list l)
{
  for (; !l.empty(); l=ATgetNext(l))
  {
    aterm first=ATgetFirst(l);
    if (first.type_is_int())
    {
      treevars_usedcnt[ATgetInt(static_cast<aterm_int>(first))]++;
    }
  }
}

static aterm_appl build_tree(build_pars pars, int i)
{
  if (!pars.Slist.empty())
  {
    aterm_list l,m;

    int k = i;
    aterm_appl v = createFreshVar(ATAgetArgument(ATAgetArgument(ATAgetFirst(ATLgetFirst(pars.Slist)),0),1),&i);
    treevars_usedcnt[k] = 0;

    l = aterm_list();
    m = aterm_list();
    for (; !pars.Slist.empty(); pars.Slist=ATgetNext(pars.Slist))
    {
      aterm_list e = ATLgetFirst(pars.Slist);

      e = subst_var(e,ATAgetArgument(ATAgetFirst(e),0), v,ATmakeInt(k),ATmakeList1(gsMakeSubst(ATgetArgument(ATAgetFirst(e),0),v)));

      l = push_front<aterm>(l,ATgetFirst(e));
      m = push_front<aterm>(m,ATgetNext(e));
    }

    aterm_appl r;
    aterm_list readies;

    pars.stack = add_to_stack(pars.stack,m,&r,&readies);

    if (r==aterm_appl())
    {
      aterm_appl tree;

      tree = build_tree(pars,i);
      for (; !readies.empty(); readies=ATgetNext(readies))
      {
        inc_usedcnt((aterm_list) ATgetArgument(ATAgetFirst(readies),2));
        inc_usedcnt((aterm_list) ATgetArgument(ATAgetFirst(readies),3));
        tree = atermpp::aterm_appl(afunC,ATgetArgument(ATAgetFirst(readies),0),atermpp::aterm_appl(afunR,ATgetArgument(ATAgetFirst(readies),1)),tree);
      }
      r = tree;
    }
    else
    {
      inc_usedcnt((aterm_list) ATgetArgument(r,1));
      r = atermpp::aterm_appl(afunR,ATgetArgument(r,0));
    }

    if ((treevars_usedcnt[k] > 0) || ((k == 0) && isR(r)))
    {
       return aterm_appl(afunS,static_cast<aterm>(v),static_cast<aterm>(r));
    }
    else
    {
       return r;
    }
  }
  else if (!pars.Mlist.empty())
  {
    aterm M = ATgetFirst(ATLgetFirst(pars.Mlist));

    aterm_list l;
    aterm_list m;
    for (; !pars.Mlist.empty(); pars.Mlist=ATgetNext(pars.Mlist))
    {
      if (ATisEqual(M,ATgetFirst(ATLgetFirst(pars.Mlist))))
      {
        l = push_front<aterm>(l,ATgetNext(ATLgetFirst(pars.Mlist)));
      }
      else
      {
        m = push_front<aterm>(m,ATgetFirst(pars.Mlist));
      }
    }
    pars.Mlist = m;

    aterm_appl true_tree,false_tree;
    aterm_appl r ;
    aterm_list readies;

    aterm_list newstack = add_to_stack(pars.stack,l,&r,&readies);

    false_tree = build_tree(pars,i);

    if (r==aterm_appl())
    {
      pars.stack = newstack;
      true_tree = build_tree(pars,i);
      for (; !readies.empty(); readies=ATgetNext(readies))
      {
        inc_usedcnt((aterm_list) ATgetArgument(ATAgetFirst(readies),2));
        inc_usedcnt((aterm_list) ATgetArgument(ATAgetFirst(readies),3));
        true_tree = atermpp::aterm_appl(afunC,ATgetArgument(ATAgetFirst(readies),0),atermpp::aterm_appl(afunR,ATgetArgument(ATAgetFirst(readies),1)),true_tree);
      }
    }
    else
    {
      inc_usedcnt((aterm_list) ATgetArgument(r,1));
      true_tree = atermpp::aterm_appl(afunR,ATgetArgument(r,0));
    }

    if (ATisEqual(true_tree,false_tree))
    {
       return true_tree;
    }
    else
    {
      treevars_usedcnt[ATgetInt(static_cast<aterm_int>(ATgetArgument((aterm_appl) M,1)))]++;
      return atermpp::aterm_appl(afunM,ATgetArgument((aterm_appl) M,0),true_tree,false_tree);
    }
  }
  else if (!pars.Flist.empty())
  {
    aterm_list F = ATLgetFirst(pars.Flist);
    aterm_appl true_tree,false_tree;

    aterm_list newupstack = pars.upstack;
    aterm_list l;

    for (; !pars.Flist.empty(); pars.Flist=ATgetNext(pars.Flist))
    {
      if (ATisEqual(ATgetFirst(ATLgetFirst(pars.Flist)),ATgetFirst(F)))
      {
        newupstack = push_front<aterm>(newupstack, ATgetNext(ATLgetFirst(pars.Flist)));
      }
      else
      {
        l = push_front<aterm>(l,ATgetFirst(pars.Flist));
      }
    }

    pars.Flist = l;
    false_tree = build_tree(pars,i);
    pars.Flist = aterm_list();
    pars.upstack = newupstack;
    true_tree = build_tree(pars,i);

    if (ATisEqual(true_tree,false_tree))
    {
      return true_tree;
    }
    else
    {
      return atermpp::aterm_appl(afunF,ATgetArgument(ATAgetFirst(F),0),true_tree,false_tree);
    }
  }
  else if (!pars.upstack.empty())
  {
    aterm_list l;

    aterm_appl r;
    aterm_list readies;

    pars.stack = push_front<aterm>(pars.stack,aterm_list());
    l = pars.upstack;
    pars.upstack = aterm_list();
    add_to_build_pars(&pars,l,&r,&readies);


    if (r==aterm_appl())
    {
      aterm_appl t = build_tree(pars,i);

      for (; !readies.empty(); readies=ATgetNext(readies))
      {
        inc_usedcnt((aterm_list) ATgetArgument(ATAgetFirst(readies),2));
        inc_usedcnt((aterm_list) ATgetArgument(ATAgetFirst(readies),3));
        t = atermpp::aterm_appl(afunC,ATgetArgument(ATAgetFirst(readies),0),atermpp::aterm_appl(afunR,ATgetArgument(ATAgetFirst(readies),1)),t);
      }

      return t;
    }
    else
    {
      inc_usedcnt((aterm_list) ATgetArgument(r,1));
      return atermpp::aterm_appl(afunR,ATgetArgument(r,0));
    }
  }
  else
  {
    if (ATLgetFirst(pars.stack).empty())
    {
      if (ATgetNext(pars.stack).empty())
      {
        return atermpp::aterm_appl(afunX);
      }
      else
      {
        pars.stack = ATgetNext(pars.stack);
        return atermpp::aterm_appl(afunD,build_tree(pars,i));
      }
    }
    else
    {
      aterm_list l = ATLgetFirst(pars.stack);
      aterm_appl r ;
      aterm_list readies;

      pars.stack = push_front<aterm>(ATgetNext(pars.stack),aterm_list());
      add_to_build_pars(&pars,l,&r,&readies);

      aterm_appl tree;
      if (r==aterm_appl())
      {
        tree = build_tree(pars,i);
        for (; !readies.empty(); readies=ATgetNext(readies))
        {
          inc_usedcnt((aterm_list) ATgetArgument(ATAgetFirst(readies),2));
          inc_usedcnt((aterm_list) ATgetArgument(ATAgetFirst(readies),3));
          tree = atermpp::aterm_appl(afunC,ATgetArgument(ATAgetFirst(readies),0),atermpp::aterm_appl(afunR,ATgetArgument(ATAgetFirst(readies),1)),tree);
        }
      }
      else
      {
        inc_usedcnt((aterm_list) ATgetArgument(r,1));
        tree = atermpp::aterm_appl(afunR,ATgetArgument(r,0));
      }

      return atermpp::aterm_appl(afunN,tree);
    }
  }
}

static aterm_appl create_tree(const data_equation_list &rules, int /*opid*/, int /*arity*/, const aterm_int &true_inner)
// Create a match tree for OpId int2term[opid] and update the value of
// *max_vars accordingly.
//
// Pre:  rules is a list of rewrite rules for int2term[opid] in the
//       INNER internal format
//       opid is a valid entry in int2term
//       max_vars is a valid pointer to an integer
// Post: *max_vars is the maximum of the original *max_vars value and
//       the number of variables in the result tree
// Ret:  A match tree for int2term[opid]
{
  // Create sequences representing the trees for each rewrite rule and
  // store the total number of variables used in these sequences.
  // (The total number of variables in all sequences should be an upper
  // bound for the number of variable in the final tree.)
  aterm_list rule_seqs;
  int total_rule_vars = 0;
  for (data_equation_list::const_iterator it=rules.begin(); it!=rules.end(); ++it)
  {
    rule_seqs = push_front<aterm>(rule_seqs, create_sequence(*it,&total_rule_vars, true_inner));
  }

  // Generate initial parameters for built_tree
  build_pars init_pars;
  aterm_appl r;
  aterm_list readies;

  initialise_build_pars(&init_pars);
  add_to_build_pars(&init_pars,rule_seqs,&r,&readies);

  aterm_appl tree;
  if (r==aterm_appl())
  {
    MCRL2_SYSTEM_SPECIFIC_ALLOCA(a,int,total_rule_vars);
    treevars_usedcnt = a;
    tree = build_tree(init_pars,0);
    for (; !readies.empty(); readies=ATgetNext(readies))
    {
      tree = atermpp::aterm_appl(afunC,ATgetArgument(ATAgetFirst(readies),0),atermpp::aterm_appl(afunR,ATgetArgument(ATAgetFirst(readies),1)), tree);
    }
  }
  else
  {
    tree = atermpp::aterm_appl(afunR,ATgetArgument(r,0));
  }

  return tree;
}

template < template <class> class Traverser >
struct auxiliary_count_variables_class: public Traverser < auxiliary_count_variables_class < Traverser > >
{
  typedef Traverser< auxiliary_count_variables_class < Traverser > > super;
  using super::enter;
  using super::leave;
  using super::operator();

  std::map <variable,size_t> m_map;

  void operator ()(const variable &v)
  {
    if (m_map.count(v)==0)
    {
      m_map[v]=1;
    }
    else
    {
      m_map[v]=m_map[v]+1;
    }
  }

  std::map <variable,size_t> get_map()
  {
    return m_map;
  }
};

static variable_list get_doubles(const data_expression &t)
{
  typedef std::map <variable,size_t> t_variable_map;
  auxiliary_count_variables_class<data::variable_traverser> acvc;
  acvc(t);
  t_variable_map variable_map=acvc.get_map();
  variable_list result;
  for(t_variable_map::const_iterator i=variable_map.begin();
         i!=variable_map.end(); ++i)
  {
    if (i->second>1)
    {
      result=atermpp::push_front<aterm>(result,i->first);
    }
  }
  return result;
}


static variable_list get_vars(const data_expression &t)
{
  std::set < variable > s=find_free_variables(t);
  variable_list result;
  for(std::set < variable >::const_iterator i=s.begin(); i!=s.end(); ++i)
  {
    result=atermpp::push_front<aterm>(result,*i);
  }
  return result;
}


static aterm_list get_vars(const aterm &a)
{
  if (a.type_is_int())
  {
    return aterm_list();
  }
  else if (ATisAppl(a) && gsIsDataVarId((aterm_appl) a))
  {
    return ATmakeList1(a);
  }
  else if (ATisList(a))
  {
    aterm_list l;
    for (aterm_list m=(aterm_list) a; !m.empty(); m=ATgetNext(m))
    {
      l = ATconcat(get_vars(ATgetFirst(m)),l);
    }
    return l;
  }
  else     // ATisAppl(a)
  {
    aterm_list l;
    int arity = a.function().arity();
    for (int i=0; i<arity; ++i)
    {
      l = ATconcat(get_vars(ATgetArgument((aterm_appl) a,i)),l);
    }
    return l;
  }
}

static aterm_list dep_vars(const data_equation &eqn)
{
  size_t rule_arity = toInner(eqn.lhs(),true).function().arity()-1;
  MCRL2_SYSTEM_SPECIFIC_ALLOCA(bs,bool,rule_arity);

  aterm_appl pars = toInner(eqn.lhs(),true); // pars is actually the lhs of the equation.
  aterm_list vars = ATmakeList1( ATconcat(
                                 get_doubles(eqn.rhs()),
                                 get_vars(eqn.condition())
                               )); // List of variables occurring in each argument of the lhs
                                   // (except the first element which contains variables from the
                                   // condition and variables which occur more than once in the result)

  // Indices of arguments that need to be rewritten
  for (size_t i = 0; i < rule_arity; i++)
  {
    bs[i] = false;
  }

  // Check all arguments
  for (size_t i = 0; i < rule_arity; i++)
  {
    if (!gsIsDataVarId(ATAgetArgument(pars,i+1)))
    {
      // Argument is not a variable, so it needs to be rewritten
      bs[i] = true;
      aterm_list evars = get_vars(ATgetArgument(pars,i+1));
      for (; !evars.empty(); evars=ATgetNext(evars))
      {
        int j=i-1; // ATgetLength(ATgetNext(vars))-1
        for (aterm_list o=ATgetNext(vars); !o.empty(); o=ATgetNext(o))
        {
          if (ATindexOf(ATLgetFirst(o),ATgetFirst(evars)) != ATERM_NON_EXISTING_POSITION)
          {
            bs[j] = true;
          }
          --j;
        }
      }
    }
    else
    {
      // Argument is a variable; check whether it occurred before
      int j = i-1; // ATgetLength(vars)-1-1
      bool b = false;
      for (aterm_list o=vars; !o.empty(); o=ATgetNext(o))
      {
        if (ATindexOf(ATLgetFirst(o),ATgetArgument(pars,i+1)) != ATERM_NON_EXISTING_POSITION)
        {
          // Same variable, mark it
          if (j >= 0)
          {
            bs[j] = true;
          }
          b = true;
        }
        --j;
      }
      if (b)
      {
        // Found same variable(s), so mark this one as well
        bs[i] = true;
      }
    }
    // Add vars used in expression
    vars = push_front<aterm>(vars, get_vars(ATgetArgument(pars,i+1)));
  }

  aterm_list deps;
  for (size_t i = 0; i < rule_arity; i++)
  {
    if (bs[i] && gsIsDataVarId(ATAgetArgument(pars,i+1)))
    {
      deps = push_front<aterm>(deps,ATgetArgument(pars,i+1));
    }
  }

  return deps;
}

// This function assigns a unique index to variable v and stores
// v at this position in the vector rewriter_bound_variables. This is
// used in the compiling rewriter to obtain this variable again.
// Note that the static variable variable_indices is not cleared
// during several runs, as generally the variables bound in rewrite
// rules do not change.
size_t RewriterCompilingJitty::bound_variable_index(const variable &v)
{
  if (variable_indices0.count(v)>0)
  {
    return variable_indices0[v];
  }
  const size_t index_for_v=rewriter_bound_variables.size();
  variable_indices0[v]=index_for_v;
  rewriter_bound_variables.push_back(v);
  return index_for_v;
}

// This function assigns a unique index to variable list vl and stores
// vl at this position in the vector rewriter_binding_variable_lists. This is
// used in the compiling rewriter to obtain this variable again.
// Note that the static variable variable_indices is not cleared
// during several runs, as generally the variables bound in rewrite
// rules do not change.
size_t RewriterCompilingJitty::binding_variable_list_index(const variable_list &vl)
{
  if (variable_list_indices1.count(vl)>0)
  {
    return variable_list_indices1[vl];
  }
  const size_t index_for_vl=rewriter_binding_variable_lists.size();
  variable_list_indices1[vl]=index_for_vl;
  rewriter_binding_variable_lists.push_back(vl);
  return index_for_vl;
}

static aterm_list create_strategy(
        const data_equation_list &rules,
        const int opid,
        const size_t arity,
        nfs_array &nfs,
        const aterm_int &true_inner)
{
  aterm_list strat;
  // Array to keep note of the used parameters
  std::vector <bool> used;
  for (size_t i = 0; i < arity; i++)
  {
    used.push_back(nfs.get(i));
  }

  // Maintain dependency count (i.e. the number of rules that depend on a given argument)
  MCRL2_SYSTEM_SPECIFIC_ALLOCA(args,int,arity);
  for (size_t i = 0; i < arity; i++)
  {
    args[i] = -1;
  }

  // Process all (applicable) rules
  MCRL2_SYSTEM_SPECIFIC_ALLOCA(bs,bool,arity);
  aterm_list dep_list;
  for (data_equation_list::const_iterator it=rules.begin(); it!=rules.end(); ++it)
  {
    size_t rule_arity = (toInner(it->lhs(),true).function().arity())-1;
    if (rule_arity > arity)
    {
      continue;
    }

    aterm_appl pars = toInner(it->lhs(),true);  // the lhs, pars is an odd name.
    aterm_list vars = ATmakeList1( ATconcat(
                                   get_doubles(it->rhs()),
                                   get_vars(it->condition())
                                 )); // List of variables occurring in each argument of the lhs
                                     // (except the first element which contains variables from the
                                     // condition and variables which occur more than once in the result)

    // Indices of arguments that need to be rewritten
    for (size_t i = 0; i < rule_arity; i++)
    {
      bs[i] = false;
    }

    // Check all arguments
    for (size_t i = 0; i < rule_arity; i++)
    {
      if (!gsIsDataVarId(ATAgetArgument(pars,i+1)))
      {
        // Argument is not a variable, so it needs to be rewritten
        bs[i] = true;
        aterm_list evars = get_vars(ATgetArgument(pars,i+1));
        for (; !evars.empty(); evars=ATgetNext(evars))
        {
          int j=i-1;
          for (aterm_list o=vars; !o.tail().empty(); o=ATgetNext(o))
          {
            if (ATindexOf(ATLgetFirst(o),ATgetFirst(evars)) != ATERM_NON_EXISTING_POSITION)
            {
              bs[j] = true;
            }
            --j;
          }
        }
      }
      else
      {
        // Argument is a variable; check whether it occurred before
        int j = i-1; // ATgetLength(vars)-1-1
        bool b = false;
        for (aterm_list o=vars; !o.empty(); o=ATgetNext(o))
        {
          if (ATindexOf(ATLgetFirst(o),ATgetArgument(pars,i+1)) != ATERM_NON_EXISTING_POSITION)
          {
            // Same variable, mark it
            if (j >= 0)
            {
              bs[j] = true;
            }
            b = true;
          }
          --j;
        }
        if (b)
        {
          // Found same variable(s), so mark this one as well
          bs[i] = true;
        }
      }
      // Add vars used in expression
      vars = push_front<aterm>(vars, get_vars(ATgetArgument(pars,i+1)));
    }

    // Create dependency list for this rule
    aterm_list deps;
    for (size_t i = 0; i < rule_arity; i++)
    {
      // Only if needed and not already rewritten
      if (bs[i] && !used[i])
      {
        deps = push_front<aterm>(deps, ATmakeInt(i));
        // Increase dependency count
        args[i] += 1;
        //fprintf(stderr,"dep of arg %i\n",i);
      }
    }
    deps = reverse(deps);

    // Add rule with its dependencies
    dep_list = push_front<aterm>(dep_list, ATmakeList2( deps, (aterm_appl)*it));
  }

  // Process all rules with their dependencies
  while (1)
  {
    // First collect rules without dependencies to the strategy
    data_equation_list no_deps = data_equation_list(aterm_list());
    aterm_list has_deps;
    for (; !dep_list.empty(); dep_list=ATgetNext(dep_list))
    {
      if (ATLgetFirst(ATLgetFirst(dep_list)).empty())
      {
        no_deps = push_front<aterm>(no_deps, data_equation(ATgetFirst(ATgetNext(ATLgetFirst(dep_list)))));
      }
      else
      {
        has_deps = push_front<aterm>(has_deps,ATgetFirst(dep_list));
      }
    }
    dep_list = reverse(has_deps);

    // Create and add tree of collected rules
    if (!no_deps.empty())
    {
      strat = push_front<aterm>(strat,  create_tree(no_deps,opid,arity,true_inner));
    }

    // Stop if there are no more rules left
    if (dep_list.empty())
    {
      break;
    }

    // Otherwise, figure out which argument is most useful to rewrite
    int max = -1;
    int maxidx = -1;
    for (size_t i = 0; i < arity; i++)
    {
      if (args[i] > max)
      {
        maxidx = i;
        max = args[i];
      }
    }

    // If there is a maximum (which should always be the case), add it to the strategy and remove it from the dependency lists
    assert(maxidx >= 0);
    if (maxidx >= 0)
    {
      args[maxidx] = -1;
      used[maxidx] = true;
      aterm_int rewr_arg = ATmakeInt(maxidx);

      strat = push_front<aterm>(strat, rewr_arg);

      aterm_list l;
      for (; !dep_list.empty(); dep_list=ATgetNext(dep_list))
      {
        l = push_front<aterm>(l, push_front<aterm>(ATgetNext(ATLgetFirst(dep_list)),
                    remove_one_element<aterm>(ATLgetFirst(ATLgetFirst(dep_list)), rewr_arg)));
      }
      dep_list = reverse(l);
    }
  }

  return reverse(strat);
}

void RewriterCompilingJitty::add_base_nfs(nfs_array &nfs, const atermpp::aterm_int &opid, size_t arity)
{
  for (size_t i=0; i<arity; i++)
  {
    if (always_rewrite_argument(opid,arity,i))
    {
      nfs.set(i);
    }
  }
}

void RewriterCompilingJitty::extend_nfs(nfs_array &nfs, const atermpp::aterm_int &opid, size_t arity)
{
  data_equation_list eqns = (size_t(opid.value())<jittyc_eqns.size()?jittyc_eqns[opid.value()]:data_equation_list());
  if (eqns.empty())
  {
    nfs.fill(arity);
    return;
  }
  aterm_list strat = create_strategy(eqns,opid.value(),arity,nfs,true_inner);
  while (!strat.empty() && ATgetFirst(strat).type_is_int())
  {
    nfs.set(ATgetInt(static_cast<aterm_int>(ATgetFirst(strat))));
    strat = ATgetNext(strat);
  }
}

// Determine whether the opid is a normal form, with the given number of arguments.
bool RewriterCompilingJitty::opid_is_nf(const atermpp::aterm_int &opid, size_t num_args)
{
  // First check whether the opid is a forall or an exists with one argument.
  // Then the routines for exists/forall quantifier enumeration must be applied.
  /* if (num_args==1 &&
        (get_int2term(opid.value()).name() == exists_function_symbol() ||
         get_int2term(opid.value()).name() == forall_function_symbol()))
  {
    return false;
  } */

  // Otherwise check whether there are applicable rewrite rules.
  data_equation_list l = (size_t(opid.value())<jittyc_eqns.size()?jittyc_eqns[opid.value()]:data_equation_list());

  if (l.empty())
  {
    return true;
  }

  for (data_equation_list::const_iterator it=l.begin(); it!=l.end(); ++it)
  {
    if (toInner(it->lhs(),true).function().arity()-1 <= num_args)
    {
      return false;
    }
  }

  return true;
}

void RewriterCompilingJitty::calc_nfs_list(nfs_array &nfs, size_t arity, aterm_list args, int startarg, aterm_list nnfvars)
{
  if (args.empty())
  {
    return;
  }

  nfs.set(arity-ATgetLength(args),calc_nfs(ATgetFirst(args),startarg,nnfvars));
  calc_nfs_list(nfs,arity,ATgetNext(args),startarg+1,nnfvars);
}

bool RewriterCompilingJitty::calc_nfs(aterm t, int startarg, aterm_list nnfvars)
{
  if (ATisList(t))
  {
    int arity = ATgetLength((aterm_list) t)-1;
    if (ATgetFirst((aterm_list) t).type_is_int())
    {
      if (opid_is_nf(static_cast<aterm_int>(ATgetFirst((aterm_list) t)),arity) && arity != 0)
      {
        nfs_array args(arity);
        calc_nfs_list(args,arity,ATgetNext((aterm_list) t),startarg,nnfvars);
        bool b = args.is_filled(arity);
        return b;
      }
      else
      {
        return false;
      }
    }
    else
    {
      if (arity == 0)
      {
        assert(false);
        return calc_nfs(ATgetFirst((aterm_list) t), startarg, nnfvars);
      }
      return false;
    }
  }
  else if (t.type_is_int())
  {
    return opid_is_nf(static_cast<aterm_int>(t),0);
  }
  else if (/*ATisAppl(t) && */ gsIsNil((aterm_appl) t))
  {
    return (nnfvars==aterm_list(aterm())) || (ATindexOf(nnfvars, ATmakeInt(startarg)) == ATERM_NON_EXISTING_POSITION);
  }
  else if (/* ATisAppl(t) && */ gsIsDataVarId((aterm_appl) t))
  {
    assert(ATisAppl(t) && gsIsDataVarId((aterm_appl) t));
    return (nnfvars==aterm_list(aterm())) || (ATindexOf(nnfvars,t) == ATERM_NON_EXISTING_POSITION);
  }
  else if (is_abstraction(atermpp::aterm_appl(t)))
  {
    assert(ATisAppl(t));
    return false; // I assume that lambda, forall and exists are not in normal form by default.
                  // This might be too weak, and may require to be reinvestigated later.
  }
  else
  {
    assert(ATisAppl(t) && is_where_clause(atermpp::aterm_appl(t)));
    return false; // I assume that a where clause is not in normal form by default.
                  // This might be too weak, and may require to be reinvestigated later.
  }
}

string RewriterCompilingJitty::calc_inner_terms(nfs_array &nfs, size_t arity, aterm_list args, int startarg, aterm_list nnfvars, nfs_array *rewr)
{
  if (args.empty())
  {
    return "";
  }

  pair<bool,string> head = calc_inner_term(ATgetFirst(args),startarg,nnfvars,rewr?(rewr->get(arity-ATgetLength(args))):false,arity);
  nfs.set(arity-ATgetLength(args),head.first);
  string tail = calc_inner_terms(nfs,arity,ATgetNext(args),startarg+1,nnfvars,rewr);
  return head.second+(args.tail().empty()?"":",")+tail;
}

static string calc_inner_appl_head(size_t arity)
{
  stringstream ss;
  if (arity == 1)
  {
    ss << "makeAppl1";  // This is to avoid confusion with atermpp::aterm_appl on a function symbol and two iterators.
  }
  else if (arity == 2)
  {
    ss << "makeAppl2";  // This is to avoid confusion with atermpp::aterm_appl on a function symbol and two iterators.
  }
  else if (arity <= 5)
  {
    ss << "atermpp::aterm_appl";
  }
  else
  {
    ss << "make_term_with_many_arguments";
  }
  ss << "(" << ((long int) get_appl_afun_value(arity+1)) << ",";    // YYYY
  return ss.str();
}

// if total_arity<=5 a term of type atermpp::aterm is generated, otherwise a term of type aterm_appl is generated.
pair<bool,string> RewriterCompilingJitty::calc_inner_term(
                  aterm t,
                  int startarg,
                  aterm_list nnfvars,
                  const bool rewr,
                  const size_t total_arity)
{
  if (ATisList(t))
  {
    stringstream ss;
    bool b;
    size_t arity = ATgetLength((aterm_list) t)-1;


    if (ATgetFirst((aterm_list) t).type_is_int())
    {
      b = opid_is_nf(static_cast<aterm_int>(ATgetFirst((aterm_list) t)),arity);

      if (b || !rewr)
      {
        /* if (total_arity>5)
        {
          ss << "(aterm_appl)";
        } */
        ss << calc_inner_appl_head(arity);
      }

      if (arity == 0)
      {
        if (b || !rewr)
        {
          ss << "atermpp::aterm((atermpp::detail::_aterm*) " << (void*) get_int2aterm_value(static_cast<aterm_int>(ATgetFirst((aterm_list) t))) << "))";
        }
        else
        {
          ss << "rewr_" << ATgetInt(static_cast<aterm_int>(ATgetFirst((aterm_list) t))) << "_0_0()";
        }
      }
      else
      {
        // arity != 0
        nfs_array args_nfs(arity);
        calc_nfs_list(args_nfs,arity,ATgetNext((aterm_list) t),startarg,nnfvars);
        if (!(b || !rewr))
        {
            ss << "rewr_";
          /* if (arity<=5)
          {
            ss << "rewr_";
          }
          else
          {
            ss << "(aterm_appl)rewr_";
          } */
          add_base_nfs(args_nfs,static_cast<aterm_int>(ATgetFirst((aterm_list) t)),arity);
          extend_nfs(args_nfs,static_cast<aterm_int>(ATgetFirst((aterm_list) t)),arity);
        }
        if (arity > NF_MAX_ARITY)
        {
          args_nfs.clear(arity);
        }
        if (args_nfs.is_clear(arity) || b || rewr || (arity > NF_MAX_ARITY))
        {
          if (b || !rewr)
          {
            /* if (arity<=5)
            { */
              ss << "atermpp::aterm((atermpp::detail::_aterm*) " << (void*) get_int2aterm_value(static_cast<aterm_int>(ATgetFirst((aterm_list) t))) << ")";
            /* }
            else
            {
              ss << "(aterm_appl)(atermpp::detail::_aterm*) " << (void*) get_int2aterm_value(static_cast<aterm_int>(ATgetFirst((aterm_list) t)));
            } */
          }
          else
            ss << ATgetInt(static_cast<aterm_int>(ATgetFirst((aterm_list) t)));
        }
        else
        {
          if (b || !rewr)
          {
            const int index=ATgetInt(static_cast<aterm_int>(ATgetFirst((aterm_list) t)));
            const data::function_symbol old_head=get_int2term(index);
            std::stringstream new_name;
            new_name << "@_rewr" << "_" << index << "_" << ATgetLength((aterm_list)t)-1 << "_" << args_nfs.get_value(arity)
                                 << "_term";
            const data::function_symbol f(new_name.str(),old_head.sort());
            if (partially_rewritten_functions.count(f)==0)
            {
              OpId2Int(f);
              partially_rewritten_functions.insert(f);
            }
            /* if (arity<=5)
            { */
              /* Exclude adding an extra increase of the OpId index, which refers to an OpId that is not available.
                 The intention of this increase is to generate an index of an OpId of which it is indicated in args_nfs
                 which arguments are guaranteed to be in normal form. For these variables it is not necessary anymore
                 to recalculate the normal form. TODO: this needs to be reconstructed. */
              /* ss << "atermpp::aterm( " << (void*) get_int2aterm_value(ATgetInt((ATermInt) ATgetFirst((aterm_list) t))
                               + ((1 << arity)-arity-1)+args_nfs.get_value(arity) ) << ")"; */
              ss << "atermpp::aterm((atermpp::detail::_aterm*) " << (void*) get_int2aterm_value(ATgetInt(OpId2Int(f))) << ")";
            /* }
            else
            {
              / * See the remark above. * /
              / * ss << "(aterm_appl) " << (void*) get_int2aterm_value(ATgetInt((ATermInt) ATgetFirst((aterm_list) t))
                                 + ((1 << arity)-arity-1)+args_nfs.get_value(arity) ) << ""; * /
              ss << "(aterm_appl)(atermpp::detail::_aterm*) " << (void*) get_int2aterm_value(ATgetInt(OpId2Int(f))) << "";
            } */

          }
          else
          {
            // QUE?! Dit stond er vroeger // Sjoerd
            //   ss << (ATgetInt((ATermInt) ATgetFirst((aterm_list) t))+((1 << arity)-arity-1)+args_nfs);
            ss << (ATgetInt(static_cast<aterm_int>(ATgetFirst((aterm_list) t)))+((1 << arity)-arity-1)+args_nfs.getraw(0));
          }
        }
        nfs_array args_first(arity);
        if (rewr && b)
        {
          args_nfs.fill(arity);
        }
        string args_second = calc_inner_terms(args_first,arity,ATgetNext((aterm_list) t),startarg,nnfvars,&args_nfs);
        // The assert is not valid anymore, bcause lambda are sometimes returned in normal form, although not strictly
        // asked for...
        assert(!rewr || b || (arity > NF_MAX_ARITY) || args_first.equals(args_nfs,arity));
        if (rewr && !b)
        {
          ss << "_" << arity << "_";
          if (arity <= NF_MAX_ARITY)
          {
            ss << args_first.get_value(arity);
          }
          else
          {
            ss << "0";
          }
          ss << "(";
        }
        else
        {
          ss << ",";
        }
        ss << args_second << ")";
        if (!args_first.is_filled(arity))
        {
          b = false;
        }
      }
      b = b || rewr;

    }
    else
    {
      // ATgetFirst((aterm_list) t).type()!=AT_INT). So the first element of this list is
      // either a variable, or a lambda term. It cannot be a forall or exists, because in
      // that case there would be a type error.
      if (arity == 0)
      {
        assert(false);
        // return calc_inner_term(ATgetFirst((aterm_list) t), startarg, nnfvars,true,total_arity);
      }
      if (is_abstraction(atermpp::aterm_appl(ATgetFirst((aterm_list) t))))
      {
        atermpp::aterm_appl lambda_term(ATgetFirst((aterm_list) t));
        assert(lambda_term(0)==gsMakeLambda());

        b = rewr;
        nfs_array args_nfs(arity);
        calc_nfs_list(args_nfs,arity,ATgetNext((aterm_list) t),startarg,nnfvars);
        if (arity > NF_MAX_ARITY)
        {
          args_nfs.clear(arity);
        }

        nfs_array args_first(arity);
        if (rewr && b)
        {
          args_nfs.fill(arity);
        }

        pair<bool,string> head = calc_inner_term(lambda_term,startarg,nnfvars,false,arity);

        if (rewr)
        {
          ss << "rewrite(";
        }

        ss << calc_inner_appl_head(arity) << head.second << "," <<
                 calc_inner_terms(args_first,arity,ATgetNext((aterm_list) t),startarg,nnfvars,&args_nfs) << ")";
        if (rewr)
        {
          ss << ")";
        }

      }
      else
      {
        // So, t must be a single variable.
        assert(gsIsDataVarId(atermpp::aterm_appl(ATgetFirst((aterm_list) t))));
        b = rewr;
        pair<bool,string> head = calc_inner_term(ATgetFirst((aterm_list) t),startarg,nnfvars,false,arity);
        nfs_array tail_first(arity);
        string tail_second = calc_inner_terms(tail_first,arity,ATgetNext((aterm_list) t),startarg,nnfvars,NULL);
        /* if (arity>5)
        {
          ss << "(aterm_appl)";
        } */
        ss << "isAppl(" << head.second << ")?";
        if (rewr)
        {
            ss << "rewrite(";
        }
        ss <<"build" << arity << "(" << head.second << "," << tail_second << ")";
        if (rewr)
        {
          ss << ")";
        }
        ss << ":";
        bool c = rewr;
        if (rewr && (nnfvars!=aterm_list(aterm())) && (ATindexOf(nnfvars, ATmakeInt(startarg)) != ATERM_NON_EXISTING_POSITION))
        {
          ss << "rewrite(";
          c = false;
        }
        else
        {
          ss << "atermpp::aterm_appl(";
        }
        ss << calc_inner_appl_head(arity) << " " << head.second << ",";
        if (c)
        {
          tail_first.clear(arity);
          nfs_array rewrall(arity);
          rewrall.fill(arity);
          tail_second = calc_inner_terms(tail_first,arity,ATgetNext((aterm_list) t),startarg,nnfvars,&rewrall);
        }
        ss << tail_second << ")";
        {
          ss << ")";
        }
      }
    }

    return pair<bool,string>(b,ss.str());

  }
  else if (t.type_is_int())
  {
    stringstream ss;
    bool b = opid_is_nf(static_cast<aterm_int>(t),0);
    /* if (total_arity>5)
    {
      ss << "(aterm_appl)";
    } */
    if (rewr && !b)
    {
      ss << "rewr_" << static_cast<aterm_int>(t).value() << "_0_0()";
    }
    else
    {
      /* ss << "atermpp::aterm_appl((atermpp::detail::_aterm*) " << (void*) &*get_rewrappl_value(static_cast<aterm_int>(t).value()) << ")"; */
      set_rewrappl_value(static_cast<aterm_int>(t).value());
      ss << "mcrl2::data::detail::get_rewrappl_value_without_check(" << static_cast<aterm_int>(t).value() << ")"; 
    }
    return pair<bool,string>(
             rewr || b,
             ss.str()
           );

  }
  else if (gsIsNil((aterm_appl) t))
  {
    stringstream ss;
    /* if (total_arity>5)  XXXXXXXXXXXXXXXXXXXXXXXX
    {
      ss << "&*";
    } */
    assert(nnfvars!=aterm_list(aterm()));
    bool b = (ATindexOf(nnfvars, ATmakeInt(startarg)) != ATERM_NON_EXISTING_POSITION);
    if (rewr && b)
    {
      ss << "rewrite(arg_not_nf" << startarg << ")";
    }
    else if (b)
    {
      ss << "arg_not_nf" << startarg;    
    }
    else
    {
      ss << "arg" << startarg;    
    }
    return pair<bool,string>(rewr || !b, ss.str());

  }
  else if (gsIsDataVarId((aterm_appl)t))
  {
    assert(ATisAppl(t));
    stringstream ss;
    /* if (total_arity>5)
    {
      ss << "(aterm_appl)";
    } */
    const bool b = (nnfvars!=aterm_list(aterm())) && (ATindexOf(nnfvars,t) != ATERM_NON_EXISTING_POSITION);
    const variable v=variable((aterm_appl)t);
    string variable_name=v.name();
    // Remove the initial @ if it is present in the variable name, because then it is an variable introduced
    // by this rewriter.
    if (variable_name[0]=='@')
    {
      if (rewr && b)
      {
        ss << "rewrite(" << variable_name.substr(1) << ")";
      }
      else
      {
        ss << variable_name.substr(1);
      }
    }
    else
    {
      ss << "this_rewriter->bound_variable_get(" << bound_variable_index(v) << ")";
    }
    return pair<bool,string>(rewr || !b, ss.str());
  }
  else if (is_abstraction(atermpp::aterm_appl(t)))
  {
    stringstream ss;
    if (ATAgetArgument((aterm_appl)t,0)==gsMakeLambda())
    {
      if (rewr)
      {
        // The resulting term must be rewritten.
        pair<bool,string> r=calc_inner_term(ATgetArgument((aterm_appl)t,2),startarg,nnfvars,true,total_arity);
        ss << "this_rewriter->rewrite_single_lambda(" <<
               "this_rewriter->binding_variable_list_get(" << binding_variable_list_index(variable_list(ATgetArgument((aterm_appl)t,1))) << ")," <<
               r.second << "," << r.first << ",*(this_rewriter->global_sigma))";
        return pair<bool,string>(true,ss.str());
      }
      else
      {
        pair<bool,string> r=calc_inner_term(ATgetArgument((aterm_appl)t,2),startarg,nnfvars,false,total_arity);
        ss << "mcrl2::core::detail::gsMakeBinder(mcrl2::core::detail::gsMakeLambda()," <<
               "this_rewriter->binding_variable_list_get(" << binding_variable_list_index(variable_list(ATgetArgument((aterm_appl)t,1))) << ")," <<
               r.second << ")";
        return pair<bool,string>(false,ss.str());
      }
    }
    else if (ATAgetArgument((aterm_appl)t,0)==gsMakeForall())
    {
      if (rewr)
      {
        // A result in normal form is requested.
        pair<bool,string> r=calc_inner_term(ATgetArgument((aterm_appl)t,2),startarg,nnfvars,false,total_arity);
        ss << "this_rewriter->internal_universal_quantifier_enumeration(" <<
               "this_rewriter->binding_variable_list_get(" << binding_variable_list_index(variable_list(ATgetArgument((aterm_appl)t,1))) << ")," <<
               r.second << "," << r.first << "," << "*(this_rewriter->global_sigma))";
        return pair<bool,string>(true,ss.str());
      }
      else
      {
        // A result which is not a normal form is requested.
        pair<bool,string> r=calc_inner_term(ATgetArgument((aterm_appl)t,2),startarg,nnfvars,false,total_arity);
        ss << "mcrl2::core::detail::gsMakeBinder(mcrl2::core::detail::gsMakeForall()," <<
               "this_rewriter->binding_variable_list_get(" << binding_variable_list_index(variable_list(ATgetArgument((aterm_appl)t,1))) << ")," <<
               r.second << ")";
        return pair<bool,string>(false,ss.str());
      }
    }
    else if (ATAgetArgument((aterm_appl)t,0)==gsMakeExists())
    {
      if (rewr)
      {
        // A result in normal form is requested.
        pair<bool,string> r=calc_inner_term(ATgetArgument((aterm_appl)t,2),startarg,nnfvars,false,total_arity);
        ss << "this_rewriter->internal_existential_quantifier_enumeration(" <<
               "this_rewriter->binding_variable_list_get(" << binding_variable_list_index(variable_list(ATgetArgument((aterm_appl)t,1))) << ")," <<
               r.second << "," << r.first << "," << "*(this_rewriter->global_sigma))";
        return pair<bool,string>(true,ss.str());
      }
      else
      {
        // A result which is not a normal form is requested.
        pair<bool,string> r=calc_inner_term(ATgetArgument((aterm_appl)t,2),startarg,nnfvars,false,total_arity);
        ss << "mcrl2::core::detail::gsMakeBinder(mcrl2::core::detail::gsMakeExists()," <<
               "this_rewriter->binding_variable_list_get(" << binding_variable_list_index(variable_list(ATgetArgument((aterm_appl)t,1))) << ")," <<
               r.second << ")";
        return pair<bool,string>(false,ss.str());
      }
    }
  }
  else if (is_where_clause(atermpp::aterm_appl(t)))
  {

    stringstream ss;
    const aterm_appl w=(aterm_appl)t; // w is the where clause

    if (rewr)
    {
      // A rewritten result is expected.
      pair<bool,string> r=calc_inner_term(ATgetArgument(w,0),startarg,nnfvars,true,total_arity);

      // TODO REMOVE gsMakeWhr.
      ss << "this_rewriter->rewrite_where(mcrl2::core::detail::gsMakeWhr(" << r.second << ",";

      aterm_list assignments=ATLgetArgument(w,1);
      for( size_t no_opening_brackets=ATgetLength(assignments); no_opening_brackets>0 ; no_opening_brackets--)
      {
        ss << "push_front<aterm>(";
      }
      ss << "ATempty";
      for( ; !assignments.empty() ; assignments=ATgetNext(assignments))
      {
        aterm_appl assignment=ATAgetFirst(assignments);
        pair<bool,string> r=calc_inner_term(ATgetArgument(assignment,1),startarg,nnfvars,true,total_arity);
        ss << ",mcrl2::core::detail::gsMakeDataVarIdInit(" <<
                 "this_rewriter->bound_variable_get(" << bound_variable_index(variable(ATAgetArgument(assignment,0))) << ")," <<
                 r.second << "))";
      }

      ss << "),*(this_rewriter->global_sigma))";

      return pair<bool,string>(true,ss.str());
    }
    else
    {
      // The result does not need to be rewritten.
      pair<bool,string> r=calc_inner_term(ATgetArgument(w,0),startarg,nnfvars,false,total_arity);
      ss << "mcrl2::core::detail::gsMakeWhr(" << r.second << ",";

      aterm_list assignments=ATLgetArgument(w,1);
      for( size_t no_opening_brackets=ATgetLength(assignments); no_opening_brackets>0 ; no_opening_brackets--)
      {
        ss << "push_front<aterm>(";
      }
      ss << "ATempty";
      for( ; !assignments.empty() ; assignments=ATgetNext(assignments))
      {
        aterm_appl assignment=ATAgetFirst(assignments);
        pair<bool,string> r=calc_inner_term(ATgetArgument(assignment,1),startarg,nnfvars,true,total_arity);
        ss << ",mcrl2::core::detail::gsMakeDataVarIdInit(" <<
                 "this_rewriter->bound_variable_get(" << bound_variable_index(variable(ATAgetArgument(assignment,0))) << ")," <<
                 r.second << "))";
      }

      ss << ")";

      return pair<bool,string>(false,ss.str());
    }
  }
  assert(0);
  return pair<bool,string>(false,"----");
}

void RewriterCompilingJitty::calcTerm(FILE* f, aterm t, int startarg, aterm_list nnfvars, bool rewr)
{
  pair<bool,string> p = calc_inner_term(t,startarg,nnfvars,rewr,0);
  fprintf(f,"%s",p.second.c_str());
  return;
}

static aterm add_args(aterm a, int num)
{
  if (num == 0)
  {
    return a;
  }
  else
  {
    aterm_list l;

    if (ATisList(a))
    {
      l = (aterm_list) a;
    }
    else
    {
      l = ATmakeList1(a);
    }

    while (num > 0)
    {
      l = ATappend(l, gsMakeNil());
      num--;
    }
    return  l;
  }
}

static int get_startarg(aterm a, int n)
{
  if (ATisList(a))
  {
    return n-ATgetLength((aterm_list) a)+1;
  }
  else
  {
    return n;
  }
}


static int* i_t_st = NULL;
static int i_t_st_s = 0;
static int i_t_st_p = 0;
static void reset_st()
{
  i_t_st_p = 0;
}
static void push_st(int i)
{
  if (i_t_st_s <= i_t_st_p)
  {
    if (i_t_st_s == 0)
    {
      i_t_st_s = 16;
    }
    else
    {
      i_t_st_s = i_t_st_s*2;
    }
    i_t_st = (int*) realloc(i_t_st,i_t_st_s*sizeof(int));
  }
  i_t_st[i_t_st_p] = i;
  i_t_st_p++;
}
static int pop_st()
{
  if (i_t_st_p == 0)
  {
    return 0;
  }
  else
  {
    i_t_st_p--;
    return i_t_st[i_t_st_p];
  }
}
static int peekn_st(int n)
{
  if (i_t_st_p <= n)
  {
    return 0;
  }
  else
  {
    return i_t_st[i_t_st_p-n-1];
  }
}

// #define IT_DEBUG
#define IT_DEBUG_INLINE
#ifdef IT_DEBUG_INLINE
#define IT_DEBUG_FILE f,"//"
#else
#define IT_DEBUG_FILE stderr,
#endif
void RewriterCompilingJitty::implement_tree_aux(FILE* f, aterm_appl tree, int cur_arg, int parent, int level, int cnt, int d, const size_t arity, 
      const std::vector<bool> &used, aterm_list nnfvars)
// Print code representing tree to f.
//
// cur_arg   Indices refering to the variable that contains the current
// parent    term. For level 0 this means arg<cur_arg>, for level 1 it
//           means ATgetArgument(arg<parent>,<cur_arg) and for higher
//           levels it means ATgetArgument(t<parent>,<cur_arg>)
//
// parent    Index of cur_arg in the previous level
//
// level     Indicates the how deep we are in the term (e.g. in
//           f(.g(x),y) . indicates level 0 and in f(g(.x),y) level 1
//
// cnt       Counter indicating the number of variables t<i> (0<=i<cnt)
//           used so far (in the current scope)
//
// d         Indicates the current scope depth in the code (i.e. new
//           lines need to use at least 2*d spaces for indent)
//
// arity     Arity of the head symbol of the expression where are
//           matching (for construction of return values)
{
  if (isS(tree))
  {
    if (level == 0)
    {
      if (used[cur_arg])
      {
        fprintf(f,"%sconst atermpp::aterm_appl &%s = arg%i; // S1\n",whitespace(d*2),
                ATgetName(ATgetAFun(ATAgetArgument(ATAgetArgument(tree,0),0)))+1,cur_arg);
      }
      else
      {
        fprintf(f,"%sconst atermpp::aterm_appl &%s = arg_not_nf%i; // S1\n",whitespace(d*2),
                ATgetName(ATgetAFun(ATAgetArgument(ATAgetArgument(tree,0),0)))+1,cur_arg);
        nnfvars = push_front<aterm>(nnfvars,ATgetArgument(tree,0));
      }
    }
    else
    {
      fprintf(f,"%sconst atermpp::aterm_appl &%s = reinterpret_cast<const atermpp::aterm_appl &>(%s%i(%i)); // S2\n",whitespace(d*2),ATgetName(ATgetAFun(ATAgetArgument(ATAgetArgument(tree,0),0)))+1,(level==1)?"arg":"t",parent,cur_arg);
    }
    implement_tree_aux(f,ATAgetArgument(tree,1),cur_arg,parent,level,cnt,d,arity,used,nnfvars);
    return;
  }
  else if (isM(tree))
  {
    if (level == 0)
    {
      fprintf(f,"%sif (%s==arg%i) // M\n"
              "%s{\n",
              whitespace(d*2),ATgetName(ATgetAFun(ATAgetArgument(ATAgetArgument(tree,0),0)))+1,cur_arg,
              whitespace(d*2)
             );
    }
    else
    {
      fprintf(f,"%sif (%s==static_cast<atermpp::aterm_appl>(%s%i(%i))) // M\n"
              "%s{\n",
              whitespace(d*2),ATgetName(ATgetAFun(ATAgetArgument(ATAgetArgument(tree,0),0)))+1,(level==1)?"arg":"t",parent,cur_arg,
              whitespace(d*2)
             );
    }
    implement_tree_aux(f,ATAgetArgument(tree,1),cur_arg,parent,level,cnt,d+1,arity,used,nnfvars);
    fprintf(f,"%s}\n%selse\n%s{\n",whitespace(d*2),whitespace(d*2),whitespace(d*2));
    implement_tree_aux(f,ATAgetArgument(tree,2),cur_arg,parent,level,cnt,d+1,arity,used,nnfvars);
    fprintf(f,"%s}\n",whitespace(d*2));
    return;
  }
  else if (isF(tree))
  {
    if (level == 0)
    {
      fprintf(f,"%sif (&*(arg%i(0))==reinterpret_cast<atermpp::detail::_aterm*>(%p)) // F\n"
              "%s{\n",
              whitespace(d*2),
              cur_arg,
              (void*)get_int2aterm_value(static_cast<aterm_int>(ATgetArgument(tree,0))),
              whitespace(d*2)
             );
    }
    else
    {
      fprintf(f,"%sif (isAppl(%s%i(%i)) && &*(reinterpret_cast<const atermpp::aterm_appl &>(%s%i(%i))(0))==reinterpret_cast<atermpp::detail::_aterm*>(%p)) // F\n"
              "%s{\n"
              "%s  atermpp::aterm_appl t%i (%s%i(%i));\n",
              whitespace(d*2),
              (level==1)?"arg":"t",parent,cur_arg,
              (level==1)?"arg":"t",parent,cur_arg,
              (void*)get_int2aterm_value(static_cast<aterm_int>(ATgetArgument(tree,0))),
              whitespace(d*2),
              whitespace(d*2),cnt,(level==1)?"arg":"t",parent,cur_arg
             );
    }
    push_st(cur_arg);
    push_st(parent);
    implement_tree_aux(f,ATAgetArgument(tree,1),1,(level==0)?cur_arg:cnt,level+1,cnt+1,d+1,arity,used,nnfvars);
    pop_st();
    pop_st();
    fprintf(f,"%s}\n%selse\n%s{\n",whitespace(d*2),whitespace(d*2),whitespace(d*2));
    implement_tree_aux(f,ATAgetArgument(tree,2),cur_arg,parent,level,cnt,d+1,arity,used,nnfvars);
    fprintf(f,"%s}\n",whitespace(d*2));
    return;
  }
  else if (isD(tree))
  {
    int i = pop_st();
    int j = pop_st();
    implement_tree_aux(f,ATAgetArgument(tree,0),j,i,level-1,cnt,d,arity,used,nnfvars);
    push_st(j);
    push_st(i);
    return;
  }
  else if (isN(tree))
  {
    implement_tree_aux(f,ATAgetArgument(tree,0),cur_arg+1,parent,level,cnt,d,arity,used,nnfvars);
    return;
  }
  else if (isC(tree))
  {
    fprintf(f,"%sif (",whitespace(d*2));
    calcTerm(f,ATgetArgument(tree,0),0,nnfvars);

    fprintf(f,"==atermpp::aterm_appl((atermpp::detail::_aterm*) %p)) // C\n"
            "%s{\n",
            (void*)&*get_rewrappl_value(true_num),
            whitespace(d*2)
           ); 
    /* set_rewrappl_value(true_num);
    fprintf(f,"==mcrl2::data::detail::get_rewrappl_value_without_check(%i)) // C\n"
            "%s{\n",
            true_num,
            whitespace(d*2)
           ); */
    implement_tree_aux(f,ATAgetArgument(tree,1),cur_arg,parent,level,cnt,d+1,arity,used,nnfvars);
    fprintf(f,"%s}\n%selse\n%s{\n",whitespace(d*2),whitespace(d*2),whitespace(d*2));
    implement_tree_aux(f,ATAgetArgument(tree,2),cur_arg,parent,level,cnt,d+1,arity,used,nnfvars);
    fprintf(f,"%s}\n",whitespace(d*2));
    return;
  }
  else if (isR(tree))
  {
    fprintf(f,"%sreturn ",whitespace(d*2));
    if (level > 0)
    {
      //cur_arg = peekn_st(level);
      cur_arg = peekn_st(2*level-1);
    }
    calcTerm(f,add_args(ATgetArgument(tree,0),arity-cur_arg-1),get_startarg(ATgetArgument(tree,0),cur_arg+1),nnfvars);
    fprintf(f,"; // R1\n");
    return;
  }
  else
  {
    return;
  }
}

void RewriterCompilingJitty::implement_tree(
            FILE* f, 
            aterm_appl tree, 
            const size_t arity, 
            int d, 
            int /* opid */, 
            const std::vector<bool> &used)
{
  int l = 0;

  aterm_list nnfvars;
  for (size_t i=0; i<arity; i++)
  {
    if (!used[i])
    {
      nnfvars = push_front<aterm>(nnfvars, ATmakeInt(i));
    }
  }

  while (isC(tree))
  {
    fprintf(f,"%sif (",whitespace(d*2));
    calcTerm(f,tree(0),0,aterm_list());

    fprintf(f,"==atermpp::aterm_appl((atermpp::detail::_aterm*) %p)) // C\n"
            "%s{\n"
            "%sreturn ",
            (void*)&*get_rewrappl_value(true_num),
            whitespace(d*2),
            whitespace(d*2)
           ); 
    /* set_rewrappl_value(true_num);
    fprintf(f,"==mcrl2::data::detail::get_rewrappl_value_without_check(%i)) // C\n"
            "%s{\n"
            "%sreturn ",
            true_num,
            whitespace(d*2),
            whitespace(d*2)
           ); */
    assert(isR(ATAgetArgument(tree,1)));
    calcTerm(f,add_args(ATgetArgument(ATAgetArgument(tree,1),0),arity),get_startarg(ATgetArgument(ATAgetArgument(tree,1),0),0),nnfvars);
    fprintf(f,";\n"
            "%s}\n%selse\n%s{\n", whitespace(d*2),whitespace(d*2),whitespace(d*2)
           );
    tree = ATAgetArgument(tree,2);
    d++;
    l++;
  }
  if (isR(tree))
  {
    if (arity==0)
    { // return a reference to an aterm_appl
      fprintf(f,"%sstatic aterm_appl static_term(rewrite(",whitespace(d*2));
      calcTerm(f,add_args(ATgetArgument(tree,0),arity),get_startarg(ATgetArgument(tree,0),0),nnfvars);
      fprintf(f,")); \n");
      fprintf(f,"%sreturn static_term",whitespace(d*2));
      fprintf(f,"; // R2a\n");
    }
    else
    { // arity>0
      fprintf(f,"%sreturn ",whitespace(d*2));
      calcTerm(f,add_args(ATgetArgument(tree,0),arity),get_startarg(ATgetArgument(tree,0),0),nnfvars);
      fprintf(f,"; // R2b\n");
    }
  }
  else
  {
    reset_st();
    implement_tree_aux(f,tree,0,0,0,0,d,arity,used,nnfvars);
  }
  while (l > 0)
  {
    --d;
    fprintf(f,"%s}\n",whitespace(d*2));
    --l;
  }
}

static void finish_function(FILE* f, size_t arity, int opid, const std::vector<bool> &used)
{
  if (arity == 0)
  {
    /* fprintf(f,  "  return (atermpp::aterm_appl((atermpp::detail::_aterm*) %p)",
            (void*)&*get_rewrappl_value(opid)
           );  */
    set_rewrappl_value(opid);
    fprintf(f,  "  return mcrl2::data::detail::get_rewrappl_value_without_check(%i",
            opid
           ); 
  }
  else
  {
    if (arity > 5)
    {
      fprintf(f,  "  return make_term_with_many_arguments("
              "%li,"
              "(atermpp::detail::_aterm*)%p",
              (long int) get_appl_afun_value(arity+1),  
              (void*)get_int2aterm_value(opid)
             );
    }
    else
    {
      fprintf(f,  "  return atermpp::aterm_appl("
              "%li,"
              "(atermpp::detail::_aterm*) %p",
              (long int) get_appl_afun_value(arity+1),  
              (void*)get_int2aterm_value(opid)
             );
    }
  }
  for (size_t i=0; i<arity; i++)
  {
    if (used[i])
    {
      /* if (arity > 5)
      {
        fprintf(f,                 ",(atermpp::detail::_aterm*)&*arg%zu",i);
      }
      else */
      {
        fprintf(f,                 ", arg%zu",i); 
      }
    }
    else
    {
      /* if (arity > 5)
      {
        fprintf(f,                 ",(atermpp::detail::_aterm*)&*rewrite(arg_not_nf%zu)",i);
      }
      else */
      {
        fprintf(f,                 ", rewrite(arg_not_nf%zu)",i);
      }
    }
  }
  fprintf(f,                 ");\n");
}

void RewriterCompilingJitty::implement_strategy(FILE* f, aterm_list strat, int arity, int d, int opid, size_t nf_args)
{
  std::vector<bool> used;
  for (int i=0; i<arity; i++)
  {
    used.push_back((nf_args & (1 << i)) != 0);
  }

  while (!strat.empty())
  {
    if (ATgetFirst(strat).type_is_int())
    {
      int arg = ATgetInt(static_cast<aterm_int>(ATgetFirst(strat)));

      if (!used[arg])
      {
        fprintf(f,"%sconst atermpp::aterm_appl arg%i = rewrite(arg_not_nf%i);\n",whitespace(2*d),arg,arg);

        used[arg] = true;
      }
    }
    else
    {
      fprintf(f,"%s{\n",whitespace(2*d));
      implement_tree(f,(aterm_appl) ATgetFirst(strat),arity,d+1,opid,used);
      fprintf(f,"%s}\n",whitespace(2*d));
    }

    strat = ATgetNext(strat);
  }

  finish_function(f,arity,opid,used);
}

aterm_appl RewriterCompilingJitty::build_ar_expr(aterm expr, aterm_appl var)
{
  if (expr.type_is_int())
  {
    return make_ar_false();
  }

  if (ATisAppl(expr) && gsIsDataVarId((aterm_appl) expr))
  {
    if (ATisEqual(expr,var))
    {
      return make_ar_true();
    }
    else
    {
      return make_ar_false();
    }
  }

  aterm head = ATgetFirst((aterm_list) expr);
  if (!head.type_is_int())
  {
    return ATisEqual(head,var)?make_ar_true():make_ar_false();
  }

  aterm_appl result = make_ar_false();

  aterm_list args = ATgetNext((aterm_list) expr);
  size_t arity = ATgetLength(args);
  for (size_t i=0; i<arity; i++, args=ATgetNext(args))
  {
    int idx = int2ar_idx[atermpp::aterm_int(head).value()] + ((arity-1)*arity)/2 + i;
    aterm_appl t = build_ar_expr(ATgetFirst(args),var);
    result = make_ar_or(result,make_ar_and(make_ar_var(idx),t));
  }

  return result;
}

aterm_appl RewriterCompilingJitty::build_ar_expr_aux(const data_equation &eqn, const size_t arg, const size_t arity)
{
  atermpp::aterm_appl lhs = toInner(eqn.lhs(),true); // the lhs in internal format.

  size_t eqn_arity = ATgetArity(ATgetAFun(lhs))-1;
  if (eqn_arity > arity)
  {
    return make_ar_true();
  }
  if (eqn_arity <= arg)
  {
    aterm rhs = toInner_list_odd(eqn.rhs());  // rhs in special internal list format.
    if (rhs.type_is_int())
    {
      int idx = int2ar_idx[atermpp::aterm_int(rhs).value()] + ((arity-1)*arity)/2 + arg;
      return make_ar_var(idx);
    }
    else if (ATisList(rhs) && ATgetFirst((aterm_list) rhs).type_is_int())
    {
      int rhs_arity = ATgetLength((aterm_list) rhs)-1;
      size_t diff_arity = arity-eqn_arity;
      int rhs_new_arity = rhs_arity+diff_arity;
      size_t idx = int2ar_idx[atermpp::aterm_int(ATgetFirst((aterm_list) rhs)).value()] +
                         ((rhs_new_arity-1)*rhs_new_arity)/2 + (arg - eqn_arity + rhs_arity);
      return make_ar_var(idx);
    }
    else
    {
      return make_ar_false();
    }
  }

  aterm_appl arg_term = ATAgetArgument(lhs,arg+1);
  if (!gsIsDataVarId(arg_term))
  {
    return make_ar_true();
  }

  if (ATindexOf(dep_vars(eqn), arg_term) != ATERM_NON_EXISTING_POSITION)
  {
    return make_ar_true();
  }

  return build_ar_expr(toInner_list_odd(eqn.rhs()),arg_term);
}

aterm_appl RewriterCompilingJitty::build_ar_expr(const data_equation_list &eqns, const size_t arg, const size_t arity)
{
  if (eqns.empty())
  {
    return make_ar_true();
  }
  else
  {
    return make_ar_and(build_ar_expr_aux(eqns.front(),arg,arity),build_ar_expr(pop_front(eqns),arg,arity));
  }
}

bool RewriterCompilingJitty::always_rewrite_argument(
     const atermpp::aterm_int &opid,
     const size_t arity,
     const size_t arg)
{
  return !is_ar_false(ar[int2ar_idx[atermpp::aterm_int(opid).value()]+((arity-1)*arity)/2+arg]);
}

bool RewriterCompilingJitty::calc_ar(const aterm_appl &expr)
{
  if (is_ar_true(expr))
  {
    return true;
  }
  else if (is_ar_false(expr))
  {
    return false;
  }
  else if (is_ar_and(expr))
  {
    return calc_ar(ATAgetArgument(expr,0)) && calc_ar(ATAgetArgument(expr,1));
  }
  else if (is_ar_and(expr))
  {
    return calc_ar(ATAgetArgument(expr,0)) || calc_ar(ATAgetArgument(expr,1));
  }
  else     // is_ar_var(expr)
  {
    return !is_ar_false(ar[ATgetInt(static_cast<aterm_int>(ATgetArgument(expr,0)))]);
  }
}

void RewriterCompilingJitty::fill_always_rewrite_array()
{
  ar=std::vector <aterm_appl> (ar_size); // = (aterm_appl*) malloc(ar_size*sizeof(aterm_appl));
  /* if (ar == NULL)
  {
    throw mcrl2::runtime_error("cannot allocate enough memory (" + utilities::to_string(ar_size*sizeof(aterm_appl)) + "bytes)");
  }
  for (size_t i=0; i<ar_size; i++)
  {
    ar[i] = NULL;
  }
  */

  for(std::map <int,int> ::const_iterator it=int2ar_idx.begin(); it!=int2ar_idx.end(); ++it)
  {
    size_t arity = getArity(get_int2term(it->first));
    data_equation_list eqns = (size_t(it->first)<jittyc_eqns.size()?jittyc_eqns[it->first]:data_equation_list());
    int idx = it->second;
    for (size_t i=1; i<=arity; i++)
    {
      for (size_t j=0; j<i; j++)
      {
        ar[idx+((i-1)*i)/2+j] = build_ar_expr(eqns,j,i);
      }
    }
  }

  bool notdone = true;
  while (notdone)
  {
    notdone = false;
    for (size_t i=0; i<ar_size; i++)
    {
      if (!is_ar_false(ar[i]) && !calc_ar(ar[i]))
      {
        ar[i] = make_ar_false();
        notdone = true;
      }
    }
  }
}

static aterm toInner_list_odd(const data_expression &t)
{
  if (is_application(t))
  {
    aterm_list l;
    const data_expression_list a=application(t).arguments();
    for (data_expression_list::const_iterator i=a.begin(); i!=a.end(); ++i )
    {
      l = push_front<aterm>(l,toInner_list_odd(*i));
    }

    l = reverse(l);

    aterm arg0 = toInner_list_odd(application(t).head());
    if (arg0.type_is_list())
    {
      l = aterm_cast<const aterm_list>(arg0) + l;
    }
    else
    {
      l = push_front<aterm>(l, arg0);
    }
    return  l;
  }
  else if (is_function_symbol(t))
  {
    return static_cast<aterm_int>(OpId2Int(data_expression(t)));
  }
  else if (is_variable(t))
  {
    // Here the expression is a binder or a where expression.
    return (aterm_appl) t;
  }
  else if (is_abstraction(t))
  {
    const abstraction a=t;
    return gsMakeBinder(a.binding_operator(),a.variables(),(aterm_appl)toInner_list_odd(a.body()));
  }
  else if (is_where_clause(t))
  {
    const where_clause w=t;
    assignment_expression_list assignments=w.declarations();
    atermpp::term_list <atermpp::aterm_appl > translated_assignments;
    for (assignment_expression_list::const_iterator i=assignments.begin(); i!=assignments.end(); ++i)
    {
      translated_assignments=push_back(translated_assignments,
                                   core::detail::gsMakeDataVarIdInit(i->lhs(),(aterm_appl)toInner_list_odd(i->rhs())));
    }
    return gsMakeWhr((aterm_appl)toInner_list_odd(w.body()),
                     (aterm_list)reverse(translated_assignments));
  }
  assert(0);
  return aterm();
}


bool RewriterCompilingJitty::addRewriteRule(const data_equation &rule1)
{
  // const data_equation rule=m_conversion_helper.implement(rule1);
  const data_equation rule=rule1;
  try
  {
    CheckRewriteRule(rule);
  }
  catch (std::runtime_error& e)
  {
    mCRL2log(warning) << e.what() << std::endl;
    return false;
  }

  if (rewrite_rules.insert(rule).second)
  {
    // The equation has been added as a rewrite rule, otherwise the equation was already present.
    // Add and number new OpIds, if so required.
    toRewriteFormat(rule.condition());
    toRewriteFormat(rule.lhs());
    toRewriteFormat(rule.rhs());
    data_equation_selector.add_function_symbols(rule.lhs());
    need_rebuild = true;
  }
  return true;
}

bool RewriterCompilingJitty::removeRewriteRule(const data_equation &rule1)
{
  // const data_equation rule=m_conversion_helper.implement(rule1);
  const data_equation rule=rule1;
  if (rewrite_rules.erase(rule)>0) // An equation is erased
  {
    // The equation has been added as a rewrite rule, otherwise the equation was already present.
    need_rebuild = true;
    return true;
  }
  return false;
}

void RewriterCompilingJitty::CompileRewriteSystem(const data_specification& DataSpec)
{
  made_files = false;

  need_rebuild = true;

  true_inner = OpId2Int(sort_bool::true_());
  true_num = ATgetInt(true_inner);

  for (function_symbol_vector::const_iterator it=DataSpec.mappings().begin(); it!=DataSpec.mappings().end(); ++it)
  {
    OpId2Int(*it);
  }

  for (function_symbol_vector::const_iterator it=DataSpec.constructors().begin(); it!=DataSpec.constructors().end(); ++it)
  {
    OpId2Int(*it);
  }

  const data_equation_vector l=DataSpec.equations();
  for (data_equation_vector::const_iterator j=l.begin(); j!=l.end(); ++j)
  {
    if (data_equation_selector(*j))
    {
      addRewriteRule(*j);
    }
  }

  int2ar_idx.clear();
  ar=std::vector<aterm_appl>();
}

void RewriterCompilingJitty::CleanupRewriteSystem()
{
  if (so_rewr_cleanup != NULL)
  {
    so_rewr_cleanup();
  }
  if (rewriter_so != NULL)
  {
    delete rewriter_so;
    rewriter_so = NULL;
  }
}

/* Opens a .cpp file, saves filenames to file_c, file_o and file_so.
 *
 */
FILE* RewriterCompilingJitty::MakeTempFiles()
{
	FILE* result;

	std::ostringstream file_base;
        char* file_dir = getenv("MCRL2_COMPILEDIR");
        if (file_dir != NULL)
        {
          int l = strlen(file_dir);
          if (file_dir[l - 1] == '/')
          {
            file_dir[l - 1] = 0;
          }
          file_base << file_dir;
        }
        else
        {
          file_base << ".";
        }
	file_base << "/jittyc_" << getpid() << "_" << reinterpret_cast< long >(this) << ".cpp";

	rewriter_source = file_base.str();

	result = fopen(const_cast< char* >(rewriter_source.c_str()),"w");
	if (result == NULL)
	{
		perror("fopen");
		throw mcrl2::runtime_error("Could not create temporary file for rewriter.");
	}

	return result;
}

// The function below yields true if the function indicated by the
// function index can legitemately be used with a arguments.
// Typically a function f:D1x...xDn->D can be used with 0 and n arguments.
// A function f:(D1x...xDn)->(E1x...Em)->F can be used with 0, n, and n+m
// arguments.
static bool arity_is_allowed(
                     const sort_expression s,
                     const size_t a)
{
  if (a==0)
  {
    return true;
  }
  if (is_function_sort(s))
  {
    const function_sort fs(s);
    size_t n=fs.domain().size();
    if (n>a)
    {
      return false;
    }
    return arity_is_allowed(fs.codomain(),a-n);
  }
  return false;
}

static bool arity_is_allowed(
                     const size_t func_index,
                     const size_t a)
{
  return arity_is_allowed(get_int2term(func_index).sort(),a);
}

inline
void declare_rewr_functions(FILE* f, const size_t func_index, const size_t arity)
{
  /* If generate_code is false, only the variable aux is increased to calculate the
     return value. TODO. This can be optimized.
     Declare the function that gets function func_index in normal form */
  // int aux = 0;
  for (size_t a=0; a<=arity; a++)
  {
    if (arity_is_allowed(func_index,a))
    {
      const size_t b = (a<=NF_MAX_ARITY)?a:0;
      for (size_t nfs=0; (nfs >> b) == 0; nfs++)
      {
        if (a==0)
        {
          // This is a constant function; result can be derived by reference.
          fprintf(f,  "static inline const atermpp::aterm_appl &rewr_%zu_%zu_%zu(",func_index,a,nfs);
        }
        else
        {
          fprintf(f,  "static inline atermpp::aterm_appl rewr_%zu_%zu_%zu(",func_index,a,nfs);
        }
        for (size_t i=0; i<a; i++)
        {
          if (((nfs >> i) & 1) ==1) // nfs indicates in binary form which arguments are in normal form.
          { 
            fprintf(f, (i==0)?"const atermpp::aterm_appl &arg%zu":", const atermpp::aterm_appl &arg%zu",i);
          }
          else
          {
            fprintf(f, (i==0)?"const atermpp::aterm_appl &arg_not_nf%zu":", const atermpp::aterm_appl &arg_not_nf%zu",i);
          } 
        }
        fprintf(f,  ");\n");

        fprintf(f,  "static inline atermpp::aterm_appl rewr_%zu_%zu_%zu_term(const atermpp::aterm_appl &t) { return rewr_%zu_%zu_%zu(", func_index, a, nfs,func_index, a,nfs);
        for(size_t i = 1; i <= a; ++i)
        {
          fprintf(f,  "%sreinterpret_cast<const atermpp::aterm_appl &>(t(%zu))", (i == 1?"":", "), i);
        }
        fprintf(f,  "); }\n");
      }
    }
  }
  // return aux;
}

void RewriterCompilingJitty::BuildRewriteSystem()
{
  FILE* f;
  CleanupRewriteSystem();

  // Try to find out from environment which compile script to use. Use
  // default script called "mcrl2compilerewriter" if not set.
  std::string compile_script;
  char* env_compile_script = getenv("MCRL2_COMPILEREWRITER");
  if (env_compile_script != NULL)
    compile_script = env_compile_script;
  else
    compile_script = "mcrl2compilerewriter";
  rewriter_so = new uncompiled_library(compile_script);
  mCRL2log(verbose) << "using '" << compile_script << "' to compile rewriter." << std::endl;

  jittyc_eqns.clear();

  ar_size = 0;
  int2ar_idx.clear();

  for(std::map< data::function_symbol, atermpp::aterm_int >::const_iterator l = term2int_begin()
        ; l != term2int_end()
        ; ++l)
  {
    int i = l->second.value();
    if (int2ar_idx.count(i) == 0)
    {
      size_t arity = getArity(l->first);
      int2ar_idx[i]=ar_size;
      ar_size += (arity*(arity+1))/2;
    }
  }
  for(std::set < data_equation >::const_iterator it=rewrite_rules.begin();
                   it!=rewrite_rules.end(); ++it)
  {
    size_t main_op_id_index=atermpp::aterm_int(toInner(it->lhs(),true)(0)).value(); // main symbol of equation.
    if (main_op_id_index>=jittyc_eqns.size())
    {
      jittyc_eqns.resize(main_op_id_index+1);
    }
    jittyc_eqns[main_op_id_index] = push_front<aterm>(jittyc_eqns[main_op_id_index],*it);
  }
  fill_always_rewrite_array();

  f = MakeTempFiles();

  //
  //  Print includes
  //
  fprintf(f, "#include \"mcrl2/data/detail/rewrite/jittycpreamble.h\"\n");

  //
  // Print defs
  //
  fprintf(f,
          "#define isAppl(x) (x.function().number() != %li)\n"
          "\n", ATgetAFun(static_cast<aterm_appl>(data::variable("x", data::sort_bool::bool_()))).number()
         );

  //
  // - Calculate maximum occurring arity
  // - Forward declarations of rewr_* functions
  //
  size_t max_arity = 0;
  for (size_t j=0; j < get_num_opids(); ++j)
  {
    const data::function_symbol fs=get_int2term(j);
    size_t arity = getArity(fs);
    if (arity > max_arity)
    {
      max_arity = arity;
    }
    if (data_equation_selector(fs))
    {
      declare_rewr_functions(f, j, arity);
    }
  }
  fprintf(f,  "\n\n");

  //
  // Declare function types
  //
  fprintf(f,  "typedef atermpp::aterm_appl (*func_type)(const atermpp::aterm_appl &);\n");
  fprintf(f,  "func_type* int2func[%zu];\n", max_arity+2);

  // Set this rewriter, to use its functions.
  fprintf(f,  "mcrl2::data::detail::RewriterCompilingJitty *this_rewriter;\n");

  // Make functions that construct applications with arity n where 5< n <= max_arity.
  for (size_t i=5; i<=max_arity; ++i)
  {
    fprintf(f,
            "static atermpp::aterm_appl make_term_with_many_arguments(const function_symbol &f");
    for (size_t j=0; j<=i; ++j)
    {
      fprintf(f, ", const atermpp::aterm &arg%zu",j);
    }
    fprintf(f, ")\n"
            "{\n");
    fprintf(f, 
      "const size_t arity = f.arity();\n"

      "MCRL2_SYSTEM_SPECIFIC_ALLOCA(buffer,detail::_aterm*,arity);\n");

    for (size_t j=0; j<=i; ++j)
    {
      fprintf(f, "buffer[%zu] = &*arg%zu;\n",j,j);
    }
    
    fprintf(f, "return aterm_appl(f,buffer,buffer+arity);\n");

    fprintf(f, "}\n\n");
  }


  //
  // "build" functions
  //
  for (size_t i=1; i<=max_arity; ++i)
  {
    fprintf(f,
            "static atermpp::aterm_appl build%zu(const atermpp::aterm_appl &a",i);
    for (size_t j=0; j<i; ++j)
    {
      fprintf(f, ", const atermpp::aterm_appl &arg%zu",j);
    }
    fprintf(f, ")\n"
            "{\n");
    fprintf(f,
            "  size_t arity = a.size();\n"
            "  if (arity == 1 )\n"
            "  {\n"
            "      return %sa(0)", calc_inner_appl_head(i).c_str()); 

    for (size_t j=0; j<i; j++)
    {
      fprintf(f, ",arg%zu",j);
    }
    fprintf(f,
            ");\n"
            "  }\n"
            "  else if (mcrl2::data::is_abstraction(a))\n"
            "  {\n"
            "    return %sa", calc_inner_appl_head(i).c_str()); 

    for (size_t j=0; j<i; j++)
    {
      fprintf(f, ",arg%zu",j);
    }
    fprintf(f,
            ");\n"
            "  }\n"
            "  else\n"
            "  {\n"
            "    //atermpp::aterm args[arity+ld];\n"
            "    MCRL2_SYSTEM_SPECIFIC_ALLOCA(args,atermpp::detail::_aterm*,(arity+%zu));\n"
            "\n"
            "    for (size_t i=0; i<arity; i++)\n"
            "    {\n"
            "      args[i]=&*a(i);\n"
            "    }\n",i);
    for (size_t j=0; j<i; j++)
    {
      fprintf(f,
              "    args[arity+%zu]=&*arg%zu;\n",j,j);
    } 
    fprintf(f,
            "\n"
            "    return atermpp::aterm_appl(mcrl2::data::detail::get_appl_afun_value(arity+%zu),&args[0],&args[0]+(arity+%zu));\n"  
/*            "    for (size_t i=0; i<(arity+%zu); ++i)\n"
            "    {\n"
            "      args[i].~aterm();\n"
            "    }\n"  
            "    return result;\n" */
            "  }\n"
            "}\n"
            "\n",i,i);
  }

  //
  // Implement the equations of every operation.
  //
  for (size_t j=0; j < get_num_opids(); j++)
  {
    const data::function_symbol fs=get_int2term(j);
    const size_t arity = getArity(fs);

    if (data_equation_selector(fs))
    {
      fprintf(f,  "// %s\n",atermpp::aterm(fs).to_string().c_str());

      for (size_t a=0; a<=arity; a++)
      {
        if (arity_is_allowed(j,a))
        {
          nfs_array nfs_a(a);
          int b = (a<=NF_MAX_ARITY)?a:0;
          for (size_t nfs=0; (nfs >> b) == 0; nfs++)
          {
            if (a==0)
            { 
              fprintf(f,  "static const atermpp::aterm_appl &rewr_%zu_%zu_%zu(",j,a,nfs);
            }
            else 
            {
              fprintf(f,  "static atermpp::aterm_appl rewr_%zu_%zu_%zu(",j,a,nfs);
            }
            for (size_t i=0; i<a; i++)
            {
              if (((nfs >> i) & 1) ==1) // nfs indicates in binary form which arguments are in normal form.
              {  
                fprintf(f, (i==0)?"const atermpp::aterm_appl &arg%zu":", const atermpp::aterm_appl &arg%zu",i);
              }
              else
              {
                fprintf(f, (i==0)?"const atermpp::aterm_appl &arg_not_nf%zu":", const atermpp::aterm_appl &arg_not_nf%zu",i);
              } 
            }
            fprintf(f,  ")\n"
                    "{\n"
                   );
            if (j<jittyc_eqns.size() && !jittyc_eqns[j].empty() )
            {
            // Implement strategy
              if (0 < a)
              {
                nfs_a.set_value(a,nfs);
              }
              implement_strategy(f,create_strategy(jittyc_eqns[j],j,a,nfs_a,true_inner),a,1,j,nfs);
            }
            else
            {
              std::vector<bool> used;
              for (size_t k=0; k<a; k++)
              {
                used.push_back((nfs & ((size_t)1 << k)) != 0);
              }
              finish_function(f,a,j,used);
            }

            fprintf(f,                 "}\n");
          }
        }
      }
      fprintf(f,  "\n");
    }
  }

  fprintf(f,
          "void rewrite_init(RewriterCompilingJitty *r)\n"
          "{\n"
          "  this_rewriter=r;\n"
          "  mcrl2::data::detail::get_appl_afun_value(%zu);\n"
          "  assert(this_rewriter->rewriter_binding_variable_lists.size()==%zu);\n"
          "  assert(this_rewriter->rewriter_bound_variables.size()==%zu);\n",
          max_arity+1,rewriter_binding_variable_lists.size(),rewriter_bound_variables.size()
         );
  fprintf(f,  "\n");

  /* put the functions that start the rewriting in the array int2func */
  fprintf(f,  "\n");
  fprintf(f,  "\n");
  for (size_t i=0; i<=max_arity; i++)
  {
    fprintf(f,  "  int2func[%zu] = (func_type *) malloc(%zu*sizeof(func_type));\n",i+1,get_num_opids());
    for (size_t j=0; j < get_num_opids(); j++)
    {
      const data::function_symbol fs=get_int2term(j);
      // const size_t arity = getArity(fs);
      if (partially_rewritten_functions.count(fs)>0)
      {
        if (arity_is_allowed(j,i))
        {
          // We are dealing with a partially rewritten function here. Remove the "@_" at
          // the beginning of the string.
          const string c_function_name=pp(fs.name());
          fprintf(f,  "  int2func[%zu][%zu] = %s;\n",i+1,j,c_function_name.substr(3,c_function_name.size()-4).c_str());
        }
      }
      else if (/* (i <= arity) && */ data_equation_selector(fs) && arity_is_allowed(j,i))
      {
        fprintf(f,  "  int2func[%zu][%zu] = rewr_%zu_%zu_0_term;\n",i+1,j,j,i);
      }
    }
  }
  fprintf(f,  "}\n"
          "\n"
          "void rewrite_cleanup()\n"
          "{\n"
         );
  fprintf(f,  "\n");
  for (size_t i=0; i<=max_arity; i++)
  {
    fprintf(f,  "  free(int2func[%zu]);\n",i+1);
  }
  fprintf(f,  "}\n"
          "\n"

         );

  fprintf(f,
      "struct argument_rewriter_struct\n"
      "{\n"
      "  argument_rewriter_struct()\n"
      "  {}\n"
      "\n"
      "  atermpp::aterm_appl operator()(const atermpp::aterm &arg)\n"
      "  {\n"
      "    return rewrite(reinterpret_cast<const atermpp::aterm_appl &>(arg));\n"
      "  }\n"
      "};\n"
      "\n"
      "static atermpp::aterm_appl rewrite_int_aux(const atermpp::aterm_appl &t)\n"
      "{\n"
//      "  const size_t arity = t.size();\n"
//      "  MCRL2_SYSTEM_SPECIFIC_ALLOCA(args,atermpp::aterm,(arity));\n"
//      "  std::vector<atermpp::aterm> args(arity);\n"
//      "  args[0] = head;\n"
//      "  for (size_t i=1; i<arity; ++i)\n"
//      "  {\n"
//      "    args[i] = rewrite(atermpp::aterm_appl(t(i)));\n"
//      "  }\n"
//      "  return atermpp::aterm_appl(t.function(),args.begin(),args.end());\n"
      "  const argument_rewriter_struct argument_rewriter;\n"
      "  return atermpp::aterm_appl(t.function(),t.begin(),t.end(),argument_rewriter);\n"
      "}\n\n");

  fprintf(f,
      "static atermpp::aterm_appl rewrite_appl_aux(\n"
      "     atermpp::aterm_appl head,\n"
      "     const atermpp::aterm_appl &t)\n"
      "{\n"
      "  using namespace mcrl2::core::detail;\n"
      "  using namespace atermpp;\n"
      "  if (mcrl2::core::detail::gsIsDataVarId(head))\n"
      "  {\n"
      "    head=(*(this_rewriter->global_sigma))(atermpp::aterm_cast<const mcrl2::data::variable>(head));\n"
      "  }\n"
      "  else if (mcrl2::data::is_where_clause(head))\n"
      "  {\n"
      "    head = this_rewriter->rewrite_where(head,*(this_rewriter->global_sigma));\n"
      "  }\n"
      "  \n"
      "  // Here head has the shape\n"
      "  // variable, u(u1,...,um), lambda y1,....,ym.u, forall y1,....,ym.u or exists y1,....,ym.u,\n"
      "  if (mcrl2::data::is_abstraction(head))\n"
      "  {\n"
      "    const atermpp::aterm_appl binder(head(0));\n"
      "    if (binder==gsMakeLambda())\n"
      "    {\n"
      "      return this_rewriter->rewrite_lambda_application(head,t,*(this_rewriter->global_sigma));\n"
      "    }\n"
      "    if (binder==gsMakeExists())\n"
      "    {\n"
      "      return this_rewriter->internal_existential_quantifier_enumeration(head,*(this_rewriter->global_sigma));\n"
      "    }\n"
      "    if (binder==gsMakeForall())\n"
      "    {\n"
      "      return this_rewriter->internal_universal_quantifier_enumeration(head,*(this_rewriter->global_sigma));\n"
      "    }\n"
      "    assert(0); // One cannot end up here.\n"
      "  }\n"
      "  \n"
      "  const size_t arity=t.size();\n"
      "  if (gsIsDataVarId(head))\n"
      "  {\n"
      "    MCRL2_SYSTEM_SPECIFIC_ALLOCA(args,atermpp::aterm, arity);\n"
//      "    std::vector < atermpp::aterm > args(arity); \n"
      "    new (&args[0]) atermpp::aterm(head);\n"
      "    for(size_t i=1; i<arity; ++i)\n"
      "    {\n"
      "      new (&args[i]) atermpp::aterm(rewrite(atermpp::aterm_cast<const atermpp::aterm_appl>(t(i))));\n"
      "    }\n"
      "    const aterm_appl result= ApplyArray(arity,&args[0],&args[0]+arity);\n"
      "    for(size_t i=0; i<arity; ++i)\n"
      "    {\n"
      "      args[i].~aterm();\n"
      "    }\n"
      "    return result;\n"
      "  }\n"
      "  \n"
      "  \n"
      "  // Here head has the shape #REWR#(u0,u1,...,un).\n"

      "  const atermpp::aterm_appl u=head;\n"
      "  const size_t arity_t = t.size();\n"
      "  const atermpp::aterm head1 = u(0);\n"
      "  const size_t arity_u=u.size();\n"
      "  MCRL2_SYSTEM_SPECIFIC_ALLOCA(args,atermpp::aterm,(arity_u+arity_t-1));\n"
//       "  std::vector<atermpp::aterm> args(arity_u+arity_t-1);\n"
      "  new (&args[0]) aterm(head1);\n"
      "  int function_index;\n"
      "  if ((head1.function().number()==%ld) && ((function_index = atermpp::aterm_int(head1).value()) < %zu) )\n"
      "  {\n"
      "    for (size_t i=1; i<arity_u; ++i)\n"
      "    {\n"
      "      new (&args[i]) aterm(u(i));\n"
      "    }\n"
      "    size_t k = arity_u;\n"
      "    for (size_t i=1; i<arity_t; ++i,++k)\n"
      "    {\n"
      "      new (&args[k]) aterm(t(i));\n"
      "    }\n"
      "    size_t arity = arity_u+arity_t-2;\n"
      "    const atermpp::aterm_appl intermediate(mcrl2::data::detail::get_appl_afun_value(arity+1),&args[0],&args[0]+arity_u+arity_t-1);\n"   // YYYY+
      "    for(size_t i=0; i<arity_u+arity_t-1; ++i)\n"
      "    {\n"
      "      args[i].~aterm();\n"
      "    }\n"
      "    assert(arity <= %zu);\n"
      "    assert(int2func[arity+1][function_index] != NULL);\n"
      "    return int2func[arity+1][function_index](intermediate);\n"
      "  }\n"
      "  else\n"
      "  {\n"
      "    for (size_t i=1; i<arity_u; ++i)\n"
      "    {\n"
      "      new (&args[i]) aterm(rewrite(atermpp::aterm_cast<const atermpp::aterm_appl>(u(i))));\n"
      "    }\n"
      "    size_t k = arity_u;\n"
      "    for (size_t i=1; i<arity_t; ++i,++k)\n"
      "    {\n"
      "      new (&args[k]) aterm(rewrite(atermpp::aterm_cast<const atermpp::aterm_appl>(t(i))));\n"
      "    }\n"
      "    const aterm_appl result(mcrl2::data::detail::get_appl_afun_value(arity_u+arity_t-1),&args[0],&args[0]+arity_u+arity_t-1);\n"   // YYYY+
      "    for(size_t i=0; i<arity_u+arity_t-1; ++i)\n"
      "    {\n"
      "      args[i].~aterm();\n"
      "    }\n"
      "    return result;\n"
      "  }\n"
      "}\n\n",
      atermpp::detail::function_adm.AS_INT.number(),get_num_opids(), max_arity
      );

  fprintf(f,
      "atermpp::aterm_appl rewrite_external(const atermpp::aterm_appl &t)\n"
      "{\n"
      "  return rewrite(t);\n"
      "}\n\n"
       );

  // Moved part of the rewrite function to rewrite_aux, such that the compiler
  // can inline rewrite more often, and so gain some performance.
  fprintf(f,
      "static atermpp::aterm_appl rewrite_aux(const atermpp::aterm_appl &t)\n"
      "{\n"
      "  using namespace mcrl2::core::detail;\n"
      "  if (mcrl2::data::is_abstraction(t))\n"
      "  {\n"
      "    atermpp::aterm_appl binder(t(0));\n"
      "    if (binder==gsMakeExists())\n"
      "    {\n"
      "      return this_rewriter->internal_existential_quantifier_enumeration(t,*(this_rewriter->global_sigma));\n"
      "    }\n"
      "    if (binder==gsMakeForall())\n"
      "    {\n"
      "      return this_rewriter->internal_universal_quantifier_enumeration(t,*(this_rewriter->global_sigma));\n"
      "    }\n"
      "    if (binder==gsMakeLambda())\n"
      "    {\n"
      "      return this_rewriter->rewrite_single_lambda(\n"
      "               atermpp::aterm_cast<const mcrl2::data::variable_list>(t(1)),\n"
      "               atermpp::aterm_cast<const atermpp::aterm_appl>(t(2)),false,*(this_rewriter->global_sigma));\n"
      "    }\n"
      "    assert(0);\n"
      "    return t;\n"
      "  }\n"
      "  assert(mcrl2::data::is_where_clause(t));\n"
      "  return this_rewriter->rewrite_where(t,*(this_rewriter->global_sigma));\n"
      "}\n");

  fprintf(f,
      "static inline atermpp::aterm_appl rewrite(const atermpp::aterm_appl &t)\n"
      "{\n"
      "  using namespace mcrl2::core::detail;\n"
      "  const function_symbol &fun=t.function();\n"
      "  const size_t arity=fun.arity();\n"
      "  if (fun==apples[arity])\n"
      "  {\n"
      "    // Term t has the shape #REWR#(t1,...,tn)\n"
      "    const atermpp::aterm &head = t(0);\n"
      "    if (head.function().number()==%ld)\n"
      "    {\n"
      "      const int function_index = reinterpret_cast<const atermpp::aterm_int&>(head).value();\n"
      "      if (function_index < %zu )\n"
      "      {\n"
      "        assert(arity <= %zu);\n"
      "        assert(int2func[arity][function_index] != NULL);\n"
      "        return int2func[arity][function_index](t);\n"
      "      }\n"
      "      else\n"
      "      {\n"
      "        return rewrite_int_aux(t);"
      "      }\n"
      "    }\n"
      "    else\n"
      "    {\n"
      "      return rewrite_appl_aux(reinterpret_cast<const atermpp::aterm_appl&>(head), t);\n"
      "    }\n"
      "  }\n"
      "  \n"
      "  // Term t does not have the shape #REWR#(t1,...,tn)\n"
      "  if (gsIsDataVarId(t))\n"
      "  {\n"
      "    return (*(this_rewriter->global_sigma))(t);\n"
      "  }\n"
      "  return rewrite_aux(t);\n"
      "}\n",
      atermpp::detail::function_adm.AS_INT.number(),get_num_opids(), max_arity);


  fclose(f);

  mCRL2log(verbose) << "compiling rewriter..." << std::endl;

  try
  {
    rewriter_so->compile(rewriter_source);
  }
  catch(std::runtime_error &e)
  {
    rewriter_so->leave_files();
    throw mcrl2::runtime_error(std::string("Could not compile rewriter: ") + e.what());
  }

  mCRL2log(verbose) << "loading rewriter..." << std::endl;

  try
  {
    so_rewr_init = reinterpret_cast<void(*)(RewriterCompilingJitty *)>(rewriter_so->proc_address("rewrite_init"));
    so_rewr_cleanup = reinterpret_cast<void (*)()>(rewriter_so->proc_address("rewrite_cleanup"));
    so_rewr = reinterpret_cast<atermpp::aterm_appl(*)(const atermpp::aterm_appl &)> (rewriter_so->proc_address("rewrite_external"));

  }
  catch(std::runtime_error &e)
  {
    rewriter_so->leave_files();
    throw mcrl2::runtime_error(std::string("Could not load rewriter: ") + e.what());
  }

  so_rewr_init(this);
  need_rebuild = false;
}

RewriterCompilingJitty::RewriterCompilingJitty(const data_specification& DataSpec, const used_data_equation_selector &equations_selector):
   Rewriter()
{
  data_equation_selector=equations_selector;
  so_rewr_cleanup = NULL;
  rewriter_so = NULL;
  m_data_specification_for_enumeration = DataSpec;
  initialise_common();
  CompileRewriteSystem(DataSpec);
}

RewriterCompilingJitty::~RewriterCompilingJitty()
{
  CleanupRewriteSystem();
  finalise_common();
}

data_expression RewriterCompilingJitty::rewrite(
     const data_expression &term,
     substitution_type &sigma)
{
  internal_substitution_type internal_sigma = apply(sigma, boost::bind(&RewriterCompilingJitty::toRewriteFormat, this, _1));
  return fromRewriteFormat(rewrite_internal(toRewriteFormat(term),internal_sigma));
}

atermpp::aterm_appl RewriterCompilingJitty::rewrite_internal(
     const atermpp::aterm_appl &term,
     internal_substitution_type &sigma)
{
  if (need_rebuild)
  {
    BuildRewriteSystem();
  }
  // Save global sigma and restore it afterwards, as rewriting might be recursive with different
  // substitutions, due to the enumerator.
  internal_substitution_type *saved_sigma=global_sigma;
  global_sigma= &sigma;
  const atermpp::aterm_appl result=so_rewr(term);
  global_sigma=saved_sigma;
  return result;
}

rewrite_strategy RewriterCompilingJitty::getStrategy()
{
  return jitty_compiling;
}

}
}
}

#endif
