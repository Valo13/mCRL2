// --- node.cpp -----------------------------------------------------
// (c) 2007  -  A.J. Pretorius  -  Eindhoven University of Technology
// ---------------------------  *  ----------------------------------


#include "node.h"


// -- constructors and destructors ----------------------------------


// -------------------------
Node::Node( const int &idx )
// -------------------------
{
    index   = idx;
    cluster = NULL;
}


// ---------------------------
Node::Node( 
    const int &idx,
    const vector< double > &tpl )
// ---------------------------
{
    index   = idx;
    tuple   = tpl;
    cluster = NULL;
}


// ----------
Node::~Node()
// ----------
{
    clearInEdges();
    clearOutEdges();
}


// -- set functions -------------------------------------------------


// ---------------------
void Node::swapTupleVal( 
    const int &idx1,
    const int &idx2 )
// ---------------------
{
    if ( ( 0 <= idx1 && idx1 < tuple.size() ) &&
         ( 0 <= idx2 && idx2 < tuple.size() ) )
    {
        double temp = tuple[idx1];
        tuple[idx1] = tuple[idx2];
        tuple[idx2] = temp;
    }
    else
        throw new string( "Error swapping node tuple values." );
}


// ---------------------
void Node::moveTupleVal( 
    const int &idxFr,
    const int &idxTo )
// ---------------------
{
    if ( ( 0 <= idxFr && idxFr < tuple.size() ) &&
         ( 0 <= idxTo && idxTo < tuple.size() ) )
    {
        double temp = tuple[idxFr];

        // 2 cases to consider
        if ( idxFr < idxTo )
        {
            // move all values after idxFr 1 pos up
            for ( int i = idxFr; i < idxTo; ++i )
                tuple[i] = tuple[i+1];
            // update idxTo
            tuple[idxTo] = temp;
        }
        else if ( idxTo < idxFr )
        {
            // move all values before idxFr 1 pos down
            for ( int i = idxFr; i > idxTo; --i )
                tuple[i] = tuple[i-1];
            // update idxTo
            tuple[idxTo] = temp;
        }
    }
    else
        throw new string( "Error moving node tuple value." );
}


// --------------------------------------------------
void Node::moveTupleVals( map< int, int > &idcsFrTo )
// --------------------------------------------------
{
    if ( idcsFrTo.size() == tuple.size() )
    {
        try
        {
            vector< double > tupleNew;
        
            // init new tuple
            {
            for ( int i = 0; i < idcsFrTo.size(); ++i )
                tupleNew.push_back( -1 );
            }

            // update new tuple
            {
            for( int i = 0; i < idcsFrTo.size(); ++i )
                tupleNew[ idcsFrTo[i] ] = tuple[i];
            }

            // set tuple to new list of attributes
            tuple.clear();
            tuple = tupleNew;
            tupleNew.clear();
        }
        catch ( ... )
        {
            throw new string( "Error moving node tuple values." );
        }
    }
    else
        throw new string( "Error moving node tuple values." );
}


// --------------------
void Node::addTupleVal( 
    const int &idx,
    const double &val )
// --------------------
{
    tuple.insert( 
        tuple.begin() + idx,
        val );
}


// -------------------------------------
void Node::delTupleVal( const int &idx )
// -------------------------------------
{
    tuple.erase( tuple.begin() + idx );
}


// -----------------------------
void Node::addInEdge( Edge* in )
// -----------------------------
{
    inEdges.push_back( in );
}


// ---------------------------------------------
void Node::setInEdges( const vector< Edge* > e )
// ---------------------------------------------
{
    clearInEdges();
    inEdges = e;
}


// -------------------------------
void Node::addOutEdge( Edge* out )
// -------------------------------
{
	outEdges.push_back( out );
}


// ----------------------------------------------
void Node::setOutEdges( const vector< Edge* > e )
// ----------------------------------------------
{
    clearOutEdges();
    outEdges = e;
}


// --------------------------------
void Node::setCluster( Cluster* c )
// --------------------------------
{
    cluster = c;
}


// -- get functions -------------------------------------------------


// -----------------
int Node::getIndex()
// -----------------
{
    return index;
}


// ---------------------
int Node::getSizeTuple()
// ---------------------
{
    return tuple.size();
}


// ------------------------------------
double Node::getTupleVal( const int &idx )
// ------------------------------------
{
    if ( 0 <= idx && idx < tuple.size() )
        return tuple[idx];
    else
        throw new string( "Error retrieving node tuple value." );
}


// -----------------------
int Node::getSizeInEdges()
// -----------------------
{
	return inEdges.size();
}


// ------------------------------------
Edge* Node::getInEdge( const int &idx )
// ------------------------------------
{
	if ( 0 <= idx && idx < inEdges.size() )
		return inEdges[idx];
	else
        throw new string( "Error retrieving node incoming edge." );
}


// ------------------------
int Node::getSizeOutEdges()
// ------------------------
{
	return outEdges.size();
}


// -------------------------------------
Edge* Node::getOutEdge( const int &idx )
// -------------------------------------
{
	if ( 0 <= idx && idx < outEdges.size() )
		return outEdges[idx];
	else
        throw new string( "Error retrieving node outgoing edge." );
}


// ------------------------
Cluster* Node::getCluster()
// ------------------------
{
    return cluster;
}


// -- clear functions -----------------------------------------------


// ----------------------
void Node::clearInEdges()
// ----------------------
{
	for ( int i = 0; i < inEdges.size(); ++i )
		inEdges[i] = NULL;
    inEdges.clear();
}


// -----------------------
void Node::clearOutEdges()
// -----------------------
{
	for ( int i = 0; i < outEdges.size(); ++i )
		outEdges[i] = NULL;
    outEdges.clear();
}


// ----------------------
void Node::clearCluster()
// ----------------------
{
    cluster = NULL;
}


// -- private utility functions -------------------------------------


// -- end -----------------------------------------------------------
