// Author(s): A.J. (Hannes) Pretorius
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file ./node.h

#ifndef NODE_H
#define NODE_H

#include <QtCore>
#include <QtGui>

#include <cstddef>
#include <map>
#include <vector>

class Cluster;
class Edge;

class Node
{
  public:
    // -- constructors and destructors ------------------------------
    Node(std::size_t idx): index(idx), cluster(0) {}
    Node(std::size_t idx, const std::vector<double> &tpl): index(idx), tuple(tpl), cluster(0) {}

    // -- set functions ---------------------------------------------
    void swapTupleVal(std::size_t idx1, std::size_t idx2);
    void moveTupleVal(std::size_t idxFr, std::size_t idxTo);
    void moveTupleVals(std::map<std::size_t, std::size_t> &idcsFrTo);
    void addTupleVal(std::size_t idx, double val) { tuple.insert(tuple.begin() + idx, val); }
    void delTupleVal(std::size_t idx) { tuple.erase(tuple.begin() + idx); }
    void addInEdge(Edge* e) { inEdges.push_back(e); }
    void setInEdges(const std::vector<Edge *> &e) { inEdges = e; }
    void addOutEdge(Edge* e) { outEdges.push_back(e); }
    void setOutEdges(const std::vector<Edge *> &e) { outEdges = e; }
    void setCluster(Cluster* c) { cluster = c; }

    // -- get functions ---------------------------------------------
    std::size_t getIndex() const { return index; }
    std::size_t getSizeTuple() const { return tuple.size(); }
    double getTupleVal(const std::size_t& idx) const { return tuple[idx]; }
    std::size_t getSizeInEdges() const { return inEdges.size(); }
    Edge* getInEdge(const std::size_t& idx) const { return inEdges[idx]; }
    std::size_t getSizeOutEdges() const { return outEdges.size(); }
    Edge* getOutEdge(const std::size_t& idx) const { return outEdges[idx]; }
    Cluster* getCluster() const { return cluster; }

  protected:
    // -- data members ----------------------------------------------
    std::size_t index; // index in list of graph nodes
    std::vector< double >   tuple;
    std::vector< Edge* > inEdges;  // association
    std::vector< Edge* > outEdges; // association
    Cluster* cluster;
};

#endif

// -- end -----------------------------------------------------------
