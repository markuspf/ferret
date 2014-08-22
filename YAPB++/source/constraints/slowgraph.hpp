#ifndef _SLOWGRAPH_HPP_AGH
#define _SLOWGRAPH_HPP_AGH

#include <set>
#include <unordered_set>

#include "abstract_constraint.hpp"
#include "../partition_stack.hpp"
#include "../partition_refinement.hpp"
#include "library/hash.hpp"
#include "library/mono_set.hpp"
#include "library/graph.hpp"

template<GraphDirected directed = GraphDirected_yes>
class SlowGraph : public AbstractConstraint
{
    vec1<vec1<int> > points;
public:
    virtual std::string name() const
    { return "SlowGraph"; }


    SlowGraph(const vec1<vec1<int> >& _points, PartitionStack* ps)
    : AbstractConstraint(ps), points(_points),
    advise_branch_monoset(ps->domainSize())
    {
        for(int i = 1; i <= points.size(); ++i)
        {
            int i_size = points[i].size();
            for(int j = 1; j <= i_size; ++j)
            {
                if(points[i][j] > 0)
                    points[points[i][j]].push_back(directed?-i:i);
            }
        }
        for(int i = 1; i <= points.size(); ++i)
        {
            std::set<int> pntset(points[i].begin(), points[i].end());
            points[i] = vec1<int>(pntset.begin(), pntset.end());
        }
        D_ASSERT(points.size() <= ps->domainSize());
    }
private:

    SplitState filterGraph(const vec1<int>& cells)
    {
        vec1<u_int64_t> mset(ps->domainSize(), 0);
        MonoSet monoset(ps->cellCount());
        debug_out(0, "SlowGraph", "filtering: " << cells.size() << " cells out of " << ps->cellCount());
        int nodes = 0, edges = 0;
        for(auto c : cells)
        {
            for(auto i : ps->cellRange(c))
            {
                nodes++;
                int i_cell = ps->cellOfVal(i);
                int poshash = quick_hash(i_cell);
                int neghash = quick_hash(-i_cell);
                for(auto val : points[i])
                {
                    edges++;
                    int valabs = std::abs(val);
                    bool valsign = (val > 0);

                    if(valsign)
                        mset[valabs] += poshash;
                    else
                        mset[valabs] += neghash;
                    monoset.add(ps->cellOfVal(valabs));
                }
            }
        }
        debug_out(0, "SlowGraph", "considered " << nodes << " nodes and " << edges << " edges.");
        return filterPartitionStackByFunctionWithCells(ps, ContainerToFunction(&mset), monoset);
    }

public:
    SplitState init()
    {
        ps->addTrigger(this, Trigger_Change);
        vec1<int> cells;
        for(int i = 1; i <= ps->cellCount(); ++i)
            cells.push_back(i);
        return filterGraph(cells);
    }

    virtual SplitState signal_changed(const vec1<int>& v)
    {
        Stats::ConstraintInvoke(Stats::CON_SlowGraph);
        debug_out(1, "slowGraph", "signal_changed");
        /*vec1<int> cells;
        for(int i = 1; i <= ps->cellCount(); ++i)
            cells.push_back(i);
        SplitState ss = filterGraph(cells);
        if(ss.hasFailed())
            return ss;
        return filterGraph(cells);*/
        return filterGraph(v);
    }

    virtual void debug_check_propagation()
    {
        int cellcount = ps->cellCount();
        vec1<int> cells;
        for(int i = 1; i <= cellcount; ++i)
            cells.push_back(i);
        SplitState ss = filterGraph(cells);
        (void)ss;
        D_ASSERT(!ss.hasFailed());
        D_ASSERT(cellcount == ps->cellCount());
    }

    // We cache this monoset to save allocations.
    MonoSet advise_branch_monoset;
    virtual int advise_branch()
    {
        D_ASSERT(advise_branch_monoset.size() == 0);
        int best_cell = -1;
        int best_neighbours = 0;
        int best_size = std::numeric_limits<int>::max();
        for(int i = 1; i <= ps->cellCount(); ++i)
        {
            if(ps->cellSize(i) > 1)
            {
                int cellfirstmem = *(ps->cellStartPtr(i));
                for(auto edge : points[cellfirstmem])
                {
                    if(ps->cellSize(edge) > 1)
                        advise_branch_monoset.add(ps->cellOfVal(edge));
                }

                if(advise_branch_monoset.size() > best_neighbours ||
                   (advise_branch_monoset.size() == best_neighbours &&
                    ps->cellSize(i) < best_size)
                  )
                {
                    best_cell = i;
                    best_neighbours = advise_branch_monoset.size();
                    best_size = ps->cellSize(i);
                }
                advise_branch_monoset.clear();
            }
        }

        return best_cell;
    }

  virtual bool verifySolution(const Permutation& p)
    {
        for(int i = 1; i <= points.size(); ++i)
        {
            const vec1<int>& p_p_i = points[p[i]];
            vec1<int> image_set;
            for(int j = 1; j <= p_p_i.size(); ++j)
                image_set.push_back(p_p_i[j]);
            std::sort(image_set.begin(), image_set.end());
            if (p_p_i.size() != image_set.size() || !std::equal(p_p_i.begin(), p_p_i.end(), image_set.begin()))
                return false;
        }
        return true;
    }
};

#endif