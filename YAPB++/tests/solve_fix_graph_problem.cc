#include "problem.hpp"
#include "constraints/slowgraph.hpp"
#include "search.hpp"
#include <iostream>

int main(void)
{
    Problem p(6);
    vec1<vec1<int> > s(6); // c++11 = {{},{2},{3},{},{},{}};
    s[2].push_back(2);
    s[3].push_back(3);
    p.addConstraint(new SlowGraph<GraphDirected_yes>(s, &p.p_stack));
    SolutionStore ss = doSearch(&p, SearchOptions());

    D_ASSERT(ss.sols().size() ==4*3*2*2);
}