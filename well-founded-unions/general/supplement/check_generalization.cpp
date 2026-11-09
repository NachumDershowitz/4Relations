// Exhaustive check of the stated finite-family criterion on finite domains.
// Each color is any acyclic directed relation; colors need not be disjoint.
#include <cstdint>
#include <iostream>
#include <vector>
#include <cstdlib>
#include <stdexcept>
#include <functional>

int main(int argc, char** argv) {
    const int n = argc > 1 ? std::atoi(argv[1]) : 3;
    const int m = argc > 2 ? std::atoi(argv[2]) : 5;
    if (n < 1 || n > 3 || m < 1 || m > 10) {
        std::cerr << "Usage: check_generalization [domain-size 1..3] [colors 1..10]\n";
        return 2;
    }
    using Mask = uint16_t;
    const int count = 1 << (n*n);
    Mask identity=0;
    for (int x=0; x<n; ++x) identity |= Mask(1 << (n*x+x));
    auto compose = [n](Mask a, Mask b) {
        Mask c=0;
        for (int x=0; x<n; ++x) for (int y=0; y<n; ++y)
            if (a & (1 << (n*x+y)))
                for (int z=0; z<n; ++z) if (b & (1 << (n*y+z)))
                    c |= Mask(1 << (n*x+z));
        return c;
    };
    std::vector<Mask> plus(count), star(count), dags;
    for (int a=0; a<count; ++a) {
        Mask t=a;
        for (int k=0; k<n; ++k) for (int x=0; x<n; ++x)
            for (int y=0; y<n; ++y)
                if ((t & (1 << (n*x+k))) && (t & (1 << (n*k+y))))
                    t |= Mask(1 << (n*x+y));
        plus[a]=t; star[a]=t|identity;
        if (!(t&identity)) dags.push_back(a);
    }
    std::vector<Mask> comp(count*count);
    for (int a=0; a<count; ++a) for (int b=0; b<count; ++b)
        comp[a*count+b]=compose(a,b);
    auto product = [&](Mask a, Mask b) { return comp[a*count+b]; };
    auto included = [](Mask a, Mask b) { return (a&~b)==0; };
    std::vector<Mask> color(m), tail(m+1);
    uint64_t examined=0, qualifying=0, cycles=0, direct_qualifying=0;
    std::function<void(int)> enumerate = [&](int pos) {
        if (pos != m) {
            for (Mask a : dags) {color[pos]=a; enumerate(pos+1);}
            return;
        }
        ++examined;
        tail[m]=0;
        for (int i=m-1; i>=0; --i) tail[i]=color[i]|tail[i+1];
        Mask rstar=star[tail[0]];
        if (!included(product(tail[1],color[0]), product(color[0],rstar)|tail[1])) return;
        Mask prefix=color[0];
        bool direct=true;
        for (int i=1; i<m-1; ++i) {
            Mask lhs=product(tail[i+1],color[i]);
            Mask rhs=product(prefix,rstar)|plus[color[i]]|tail[i+1];
            if (!included(lhs,rhs)) return;
            Mask rhs_direct=product(color[i-1],star[tail[i-1]])|plus[color[i]]|tail[i+1];
            if (!included(lhs,rhs_direct)) direct=false;
            prefix|=color[i];
        }
        ++qualifying;
        if (direct) ++direct_qualifying;
        if (plus[tail[0]]&identity) {
            ++cycles;
            std::cerr << "COUNTEREXAMPLE:";
            for (Mask c:color) std::cerr<<" "<<c;
            std::cerr<<"\n";
        }
    };
    enumerate(0);
    std::cout << "{\"domain_size\":" << n << ",\"colors\":" << m
              << ",\"acyclic_relations\":" << dags.size()
              << ",\"tuples\":" << examined
              << ",\"prefix_detour_qualifying\":" << qualifying
              << ",\"previous_color_qualifying\":" << direct_qualifying
              << ",\"cyclic_unions\":" << cycles << "}\n";
    return cycles ? 1 : 0;
}
