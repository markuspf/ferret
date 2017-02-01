#ifndef _NORMALISER_HPP
#define _NORMALISER_HPP

#include <set>

#include "abstract_constraint.hpp"
#include "../partition_stack.hpp"
#include "../partition_refinement.hpp"
#include "../library/algorithms.hpp"
#include "gap_cpp_mapping.hpp"
#include "../rbase/rbase.hpp"

/* Attempt at implementing normalisers in partition backtrack
 * At the moment this just implements Heiko Theißens algorithm
 *
 * It should be sufficient to just compute the normaliser of a group
 * E <= S_n, then we can intersect E with another group G and get
 * the normaliser of E in G.
 *
 * Use with extreme portions of salt, this isn't finished.
 */

class Normaliser : public AbstractConstraint
{
    Obj group;

public:
    virtual std::string name() const
    { return "Normaliser"; }

    Normaliser(Obj _group, PartitionStack* ps)
        : AbstractConstraint(ps), group(_group)
    {
    }
private:

vec1<int> getRBaseOrbitPartition(const vec1<int>& fix)
    {
        debug_out(3, "PermGroup", "Fixing: " << fix);
        Obj vec = GAP_make(fix);
        Obj orbits = GAP_callFunction(FunObj_YAPB_FixedOrbits, group, GAP_make(ps->domainSize()), vec);
        vec1<vec1<int> > oart = GAP_get<vec1<vec1<int> > >(orbits);
        debug_out(3, "PermGroup", "Got orbit partition" << oart);
        // This might not be necessary, but it doesn't hurt!
        for(int i : range1(oart.size()))
            std::sort(oart[i].begin(), oart[i].end());
        std::sort(oart.begin(), oart.end());
        vec1<int> filter = partitionToList(oart, ps->domainSize(), MissingPoints_Fixed);
        debug_out(3, "PermGroup", "Filter partition: " << filter);
        return filter;
    }

public:
    std::vector<TriggerType> triggers()
    {
        std::vector<TriggerType> v;
         v.push_back(Trigger_Fix);
        return v;
    }

    SplitState signal_start()
    {
        debug_out(0, "normaliser", "starting");
        return signal_fix();
    }

 virtual SplitState signal_fix()
    {
        Stats::ConstraintInvoke(Stats::CON_PermGroup);
        vec1<int> fixed_values;
        const vec1<int>& fixed = ps->fixed_cells();
        for(int i : range1(fixed.size()))
        {
            fixed_values.push_back(*ps->cellStartPtr(fixed[i]));
        }
        vec1<int> part = getRBaseOrbitPartition(fixed_values);
        return filterPartitionStackByUnorderedFunction(ps, SquareBrackToFunction(&part));
    }
    
    virtual bool verifySolution(const Permutation& p)
    {
        debug_out(0,"normaliser", "verifying");
        /* we could in principle first test whether p \in group, not
           sure whether that's worth it, I should test that */
        return GAP_get<bool>(GAP_callFunction(FunObj_isGroupConj, GAP_make(p), group));
    }
};

class NormGraphRefiner
{

    NormGraphRefiner();
public:
    NormGraphRefiner(int points) :
     mset(points, 0),
     msetspare(points, 0),
     edgesconsidered(0)
    {

    };

  // Construct these once, for use in filterGraph, as the cost is fairly big
    vec1<u_int64_t> mset;
    vec1<u_int64_t> msetspare;
    
    int edgesconsidered;
    
    template<typename GraphType>
    void hashCellSimple(PartitionStack* ps, const GraphType& points, MonoSet& monoset, int cell)
    {
        Range<PartitionStack::cellit> r = ps->cellRange(cell);
        for(int i : r)
        {
            debug_out(4, "filter", "filtering " << i);
            int i_cell = ps->cellOfVal(i);
            int hash = quick_hash(i_cell);
            debug_out(4, "filter", "initial cell" << ps->cellOfVal(i) << ":" << i_cell);
            for(const auto& edge : points.neighbours(i))
            {
                monoset.add(ps->cellOfVal(edge.target()));
                u_int64_t new_hash = quick_hash(hash + edge.colour());
                debug_out(4, "filter", "adding to " << edge << ":" << new_hash);
                edgesconsidered++;
                mset[edge.target()] += new_hash;
            }
        }
    }
    
    template<typename GraphType>
    void hashNeighboursOfVertexDeep2(PartitionStack* ps, const GraphType& points, 
                                     MonoSet& hitcells, int vertex, u_int64_t hash)
    {
        for(const auto& edge : points.neighbours(vertex))
        {
            hitcells.add(ps->cellOfVal(edge.target()));
            u_int64_t new_hash = quick_hash(hash + edge.colour());
            edgesconsidered++;
            msetspare[edge.target()] += new_hash;
        }
    }
 
    template<typename Range, typename GraphType>
    void hashRangeDeep2(PartitionStack* ps, const GraphType& points, MonoSet& hitcells, Range cell)
    {
        for(int i : cell)
        {
            int i_cell = ps->cellOfVal(i);
            int hash = quick_hash(i_cell + mset[i]);
            hashNeighboursOfVertexDeep2(ps, points, hitcells, i, hash);
        }
    }
    
    template<typename GraphType>
    void hashNeighboursOfVertexDeep(PartitionStack* ps, const GraphType& points, 
                                    MonoSet& hitcells, MonoSet& hitvertices, int vertex, u_int64_t hash)
    {
        for(const auto& val : points.neighbours(vertex))
        {
            hitcells.add(ps->cellOfVal(val.target()));
            hitvertices.add(val.target());
            u_int64_t new_hash = quick_hash(hash + val.colour());
            edgesconsidered++;
            mset[val.target()] += new_hash;
        }
    }
 
    template<typename Range, typename GraphType>
    void hashRangeDeep(PartitionStack* ps, const GraphType& points, 
                       MonoSet& hitcells, MonoSet& hitvertices, Range cell)
    {
        for(int i : cell)
        {
            int i_cell = ps->cellOfVal(i);
            int hash = quick_hash(i_cell);
            hashNeighboursOfVertexDeep(ps, points, hitcells, hitvertices, i, hash);
        }
    }
    
    template<typename GraphType, typename CellList>
    SplitState filterGraph(PartitionStack* ps, const GraphType& points,
                           const CellList& cells, int path_length)
    {
        // Would not normally go this low level, but it is important this is fast
        memset(&(mset.front()), 0, mset.size() * sizeof(mset[0]));
        edgesconsidered = 0;
        MonoSet monoset(ps->cellCount());
        debug_out(3, "EdgeGraph", "filtering: " << cells.size() << " cells out of " << ps->cellCount());
        if(path_length == 1) {
            for(int c : cells)
            {
                hashCellSimple(ps, points, monoset, c);
            }
        }
        else
        {
            MonoSet hitvertices(ps->domainSize());
            for(int c : cells)
            {
                hashRangeDeep(ps, points, monoset, hitvertices, ps->cellRange(c));
            }
            
            memset(&(msetspare.front()), 0, msetspare.size() * sizeof(msetspare[0]));
            hashRangeDeep2(ps, points, monoset, hitvertices.getMembers());
            for(int i : range1(mset.size())) {
                mset[i] += msetspare[i] * 71;
            }
        }
        debug_out(3, "EdgeGraph", "filtering " << mset << " : " << monoset);
        return filterPartitionStackByFunctionWithCells(ps, SquareBrackToFunction(&mset), monoset);
    }
};



class GraphNormaliser : public AbstractConstraint
{
    Obj group;
    NormGraphRefiner refiner;

public:
    virtual std::string name() const
    { return "GraphNormaliser"; }

    GraphNormaliser(Obj _group, PartitionStack* ps)
        : AbstractConstraint(ps), group(_group), refiner(ps->domainSize())
    {
    }
private:

vec1<int> getRBaseOrbitPartition(const vec1<int>& fix)
    {
        debug_out(3, "PermGroup", "Fixing: " << fix);
        Obj vec = GAP_make(fix);
        Obj orbits = GAP_callFunction(FunObj_YAPB_FixedOrbits, group, GAP_make(ps->domainSize()), vec);
        vec1<vec1<int> > oart = GAP_get<vec1<vec1<int> > >(orbits);
        debug_out(3, "PermGroup", "Got orbit partition" << oart);
        // This might not be necessary, but it doesn't hurt!
        for(int i : range1(oart.size()))
            std::sort(oart[i].begin(), oart[i].end());
        std::sort(oart.begin(), oart.end());
        vec1<int> filter = partitionToList(oart, ps->domainSize(), MissingPoints_Fixed);
        debug_out(3, "PermGroup", "Filter partition: " << filter);
        return filter;
    }

public:
    std::vector<TriggerType> triggers()
    {
        std::vector<TriggerType> v;
         v.push_back(Trigger_Fix);
        return v;
    }

    SplitState signal_start()
    {
        debug_out(0, "normaliser", "starting");
        return signal_fix();
    }

    virtual SplitState signal_fix()
    {
        Stats::ConstraintInvoke(Stats::CON_PermGroup);
        vec1<int> fixed_values;
        const vec1<int>& fixed = ps->fixed_cells();
        for(int i : range1(fixed.size())) {
            fixed_values.push_back(*ps->cellStartPtr(fixed[i]));
        }
        vec1<int> part = getRBaseOrbitPartition(fixed_values);
        debug_out(3, "PermGroup", "Signal Fix: ");
        return filterPartitionStackByUnorderedFunction(ps, SquareBrackToFunction(&part));
    }
    
    virtual bool verifySolution(const Permutation& p)
    {
        debug_out(0,"normaliser", "verifying");
        /* we could in principle first test whether p \in group, not
           sure whether that's worth it, I should test that */
        return GAP_get<bool>(GAP_callFunction(FunObj_isGroupNorm, GAP_make(p), group));
    }
};

#endif // _NORMALISER_HPP

