// Author(s): Bas Ploeger and Carst Tankink
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file state.cpp
/// \brief Add your file description here.
#include "state.h"
using namespace std;
using namespace Utils;

State::State() {
  cluster = NULL;
  rank = 0;
  positionRadius = 0.0f;
  positionAngle = -1.0f;
  id = 0;
  marked = false;
  markAllEmpty = false;
  simulated = false;
  selected = false;
  zoomLevel = 0;
}

State::~State() {
  unsigned int i;
  for (i = 0; i < outTransitions.size(); ++i) {
    delete outTransitions[i];
  }
  for (i = 0; i < loops.size(); ++i) {
    delete loops[i];
  }
}

void State::addInTransition(Transition* trans) {
  inTransitions.push_back(trans);
}

void State::addOutTransition(Transition* trans) {
  outTransitions.push_back(trans);
}

void State::addLoop(Transition* trans) {
  loops.push_back(trans);
}

void State::addParameterValue(int valindex) {
	stateVector.push_back(valindex);
}

bool State::isDeadlock() const {
  return (outTransitions.size() + loops.size() == 0);
}

bool State::isMarked() const {
  return marked && (markAllEmpty ||(rulesMatched.size() > 0));
}

unsigned int State::nrRulesMatched() const {
  return rulesMatched.size();
}

void State::setMarking(bool b)
{
  marked = b;
}

void State::setMarkAllEmpty(bool b)
{
  markAllEmpty = b;
}

int State::mark(Utils::MarkRule* rule) {
  bool found = false;

  for(std::vector<Utils::MarkRule*>::iterator it = rulesMatched.begin();
      it != rulesMatched.end() && !found; ++it)
  {
    if ((*it) == rule)
    {
      found = true;
    }
  }

  if (!found)
  {
    rulesMatched.push_back(rule);
  }

  return rulesMatched.size();
}

int State::unmark(Utils::MarkRule* rule) {
  // Search for rule in rulesMatched, and erase it.

  std::vector<Utils::MarkRule*>::iterator it = rulesMatched.begin();
  while(it != rulesMatched.end())
  {
    if ((*it) == rule)
    {
      it = rulesMatched.erase(it);
    }
    else
    {
      ++it;
    }
  }

  return rulesMatched.size();
}

bool State::isSelected() const {
  return selected;
}

void State::select() {
  selected = true;
}

void State::deselect() {
  selected = false;
}


int State::getID() {
	return id;
}

void State::setID(int i) {
	id = i;
}

int State::getRank() const {
  return rank;
}

void State::setRank(int r) {
  rank = r;
}

bool State::isCentered() const {
  return (positionAngle < -0.9f);
}

void State::center() {
  positionRadius = 0.0f;
  positionAngle = -1.0f;
}

float State::getPositionAngle() const {
  return positionAngle;
}

float State::getPositionRadius() const {
  return positionRadius;
}

Point3D State::getPositionAbs() const {
  return positionAbs;
}

Point3D State::getOutgoingControl() const {
  return outgoingControl;
}

Point3D State::getIncomingControl() const {
  return incomingControl;
}

void State::setPositionRadius(float r) {
  positionRadius = r;
}

void State::setPositionAngle(float a) {
  positionAngle = a;
}

void State::setPositionAbs(Point3D &p) {
  positionAbs.x = p.x;
  positionAbs.y = p.y;
  positionAbs.z = p.z;
}

void State::setOutgoingControl(Point3D &p) {
  outgoingControl = p;
}

void State::setIncomingControl(Point3D &p) {
  incomingControl = p;
}

Cluster* State::getCluster() const {
  return cluster;
}

void State::setCluster(Cluster* c) {
  cluster = c;
}

Transition* State::getInTransition(int i) const {
  return inTransitions[i];
}

int State::getNumInTransitions() const {
  return inTransitions.size();
}

Transition* State::getOutTransition(int i) const {
  return outTransitions[i];
}

int State::getNumOutTransitions() const {
  return outTransitions.size();
}

Transition* State::getLoop(int i) const {
  return loops[i];
}

int State::getNumLoops() const {
  return loops.size();
}

int State::getParameterValue(int parindex) {
  return stateVector[parindex];
}

void State::setSimulated(bool simulated) {
  this->simulated = simulated;
}

bool State::isSimulated() const {
  return simulated;
}

int State::getZoomLevel() const {
  return zoomLevel;
}


void State::setZoomLevel(const int level) {
  zoomLevel = level;
}

Point3D State::getForce() {
  return force;
}

void State::resetForce() {
  force.x = 0.0f;
  force.y = 0.0f;
  force.z = 0.0f;
}

void State::addForce(Point3D f) {
  force.x += f.x;
  force.y += f.y;
  force.z += f.z;
}

Vect State::getVelocity() {
  return velocity;
}

void State::resetVelocity() {
  velocity.x = 0.0f;
  velocity.y = 0.0f;
}

void State::setVelocity(Vect v) {
  velocity = v;
}


void State::mark()
{
  marked = true;
}

void State::unmark()
{
  marked = false;
}

bool State::isMarkedNoRule()
{
  return marked;
}
