// fractran enumeration, run to size 20 finished on nov 13

#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef vector<int> fraction;
typedef vector<fraction> program;

const int LIM=20; // max sz to enumerate

string program_str(const program& prog) {
    string out="[";
    for (int i=0; i<prog.size(); i++) {
        out+="[";
        for (int j=0; j<prog[i].size(); j++) {
            if (j>0) out+=" ";
            out+=to_string(prog[i][j]);
        }
        out+="]";
    }
    out+="]";
    return out;
}

// 1 = cycle detected. 0 = unsure.
bool translated_cycle(const program& prog,fraction n0,fraction n1,fraction n2) {
    for (int i=0; i<n0.size(); i++) {
        if (n0[i]+n2[i]!=n1[i]+n1[i]) return 0; // not geometric
    }
    fraction k=n2;
    for (int i=0; i<n0.size(); i++) {
        k[i]-=n1[i];
        if (k[i]<0) return 0; // k has denominator
    }
    while (n1!=n2) {
        for (auto& f:prog) {
            bool apply=1;
            for (int i=0; i<f.size(); i++) {
                if (n1[i]+f[i]<0) {
                    apply=0;
                    break;
                }
            }
            if (apply) {
                for (int i=0; i<f.size(); i++) n1[i]+=f[i];
                break;
            }
            else {
                // check that n1*k^inf doesn't work
                bool apply2=1;
                for (int i=0; i<f.size(); i++) {
                    if (k[i]==0 && n1[i]+f[i]<0) {
                        apply2=0;
                        break;
                    }
                }
                if (apply2) return 0;
            }
        }
    }
    return 1;
}

/*
1 = cannot halt. 0 = unsure.
idea of graph_search2 (also called "power limit mod")

* EXP_LIM is the exponent limit
* the list [a,b,c,d,...] represents the number 2^a * 3^b * 5^c * 7^d * ...
* do a graph search, but limit the exponents to 2*EXP_LIM different groups
  * split into 2 groups, <EXP_LIM and >=EXP_LIM
  * split into EXP_LIM groups, the groups are mod EXP_LIM
  * (the code uses the numbers 0,1,...,2*EXP_LIM-1 to represent these groups)
* if halting never occurs, the program runs forever

*/
bool graph_search2(const program& prog,int maxidx,int exp_lim) {
    vector<fraction> q;
    set<fraction> vis;
    {
        fraction start(maxidx);
        start[0]=1;
        q.push_back(start);
        vis.insert(start);
    }
    // guarantee that the same inst is always used
    for (auto& f:prog) {
        for (int i:f) {
            if (i+exp_lim<0) return 0;
        }
    }
    while (!q.empty()) {
        fraction u=q.back();
        q.pop_back();
        bool found=0;
        for (auto& f:prog) {
            bool apply=1;
            for (int i=0; i<f.size(); i++) {
                if (u[i]+f[i]<0) {
                    apply=0;
                    break;
                }
            }
            if (apply) {
                // inst matches, get next states
                vector<fraction> v0{};
                v0.push_back({});
                for (int i=0; i<maxidx; i++) {
                    int r0=u[i]+(i<f.size()?f[i]:0);
                    while (r0>=2*exp_lim) r0-=exp_lim;
                    for (auto& f0:v0) f0.push_back(r0);
                    if (r0<exp_lim && u[i]>=exp_lim) {
                        // double it
                        int sz=v0.size();
                        for (int i=0; i<sz; i++) {
                            fraction f0=v0[i];
                            f0.back()+=exp_lim;
                            v0.push_back(f0);
                        }
                    }
                }
                for (auto& f:v0) {
                    if (vis.count(f)) continue;
                    vis.insert(f);
                    q.push_back(f);
                }
                found=1;
                break;
            }
        }
        if (!found) return 0; // found path to halt
    }
    return 1;
}

// 0 1 -1 2 -2 3 -3 ...
int int_ordering(int x) {
    if (x>0) return x*2-1;
    return -x*2;
}

// print tracing
ll print0=0,print1=1000000;
ll tc_record=0;

// rem = number of remaining primes
// return 1 = don't expand. return 0 = expand more.
vector<ll> cnt;
ll busy=0;
vector<program> champions;
bool solve(const program& prog,int rem) {
    int cntstep=0;
    // check for x/1
    cnt[cntstep++]++;
    {
        bool neg=0;
        for (int j=0; j<prog.back().size(); j++) {
            if (prog.back()[j]<0) neg=1;
        }
        if (!neg) return 1; // x/1, nonhalt
    }
    // check if program can be made complete within a cost of "rem".
    // assume that the rows in prog are finished, and we can only add new rows.
    int maxidx=1;
    for (auto& f:prog) maxidx=max(maxidx,(int)f.size());
    cnt[cntstep++]++;
    {
        int need_pos=0,need_neg=0;
        for (int i=1; i<maxidx; i++) {
            bool has_pos=0,has_neg=0;
            for (auto& f:prog) {
                if (f.size()<=i) continue;
                if (f[i]>0) has_pos=1;
                if (f[i]<0) has_neg=1;
            }
            if (!has_pos && has_neg) need_pos++; // need to add primes[i] later
            if (has_pos && !has_neg) need_neg++; // need to add primes[i] later
        }
        bool denom2=0; // contains x/2
        for (auto& f:prog) {
            if (f[0]!=-1) continue;
            bool ok=1;
            for (int i=1; i<f.size(); i++) {
                if (f[i]<0) ok=0;
            }
            if (ok) denom2=1;
        }
        int needed=need_pos+need_neg;
        if (denom2) {
            if (need_neg) needed+=1; // 1 fraction
            else if (need_pos) needed+=2; // 1 fraction, 1 prime in denom (to avoid x/1)
            else {} // nothing is needed
        }
        else if (need_neg) needed+=3; // 2 fractions, 1 prime in denom (for x/2)
        else needed+=2; // 1 fraction, 1 prime in denom (for x/2)
        if (needed>rem) return 1; // pruned, too inefficient with primes
    }
    // check if columns 2,3,... are in nonincreasing order
    cnt[cntstep++]++;
    {
        vector<vector<int>> primeorder;
        // start at i=1 (prime number 3), because all primes >=3 are treated equally.
        // leave out i=0 (prime number 2), because 2 is treated differently (it's the starting number).
        for (int i=1; i<maxidx; i++) { // i = prime idx
            vector<int> tmp;
            for (auto& f:prog) tmp.push_back(int_ordering(i<f.size()?f[i]:0));
            primeorder.push_back(tmp);
        }
        for (int i=1; i<primeorder.size(); i++) {
            if (primeorder[i-1]<primeorder[i]) return 1; // redundant due to column order
        }
    }
    // check for covered denominator
    cnt[cntstep++]++;
    for (int i=0; i+1<prog.size(); i++) {
        bool covered=1;
        for (int j=0; j<maxidx; j++) {
            int k0=(prog[i].size()>j?prog[i][j]:0);
            int k1=(prog.back().size()>j?prog.back()[j]:0);
            if ((k1>=0 && k0<0) || (k1<0 && k0<k1)) {
                covered=0;
                break;
            }
        }
        if (covered) return 1; // covered, prog.back() is never used
    }
    // decider: translated cycler + direct simulation
    print0++;
    if (print0>=print1) {
        print1=print1*31/30;
        fprintf(stderr,"sample %lld %s\n",print0,program_str(prog).c_str());
    }
    cnt[cntstep++]++;
    fraction n(maxidx);
    n[0]=1;
    vector<fraction> history;
    for (ll steps=0; steps<10000; steps++) {
        history.push_back(n);
        if (steps>=3) {
            if (translated_cycle(prog,history[steps-steps/3-steps/3],history[steps-steps/3],n)) {
                if (tc_record<steps) {
                    tc_record=steps;
                    fprintf(stderr,"  HARDEST TC %lld %s\n",tc_record,program_str(prog).c_str());
                }
                return 1; // nonhalt
            }
        }
        bool found=0;
        for (auto& f:prog) {
            bool apply=1;
            for (int i=0; i<f.size(); i++) {
                if (n[i]+f[i]<0) {
                    apply=0;
                    break;
                }
            }
            if (apply) {
                for (int i=0; i<f.size(); i++) n[i]+=f[i];
                found=1;
                break;
            }
        }
        if (!found) { // halted
            if (busy<steps) {
                fprintf(stderr,"  NEW CHAMPION %lld %s\n",steps,program_str(prog).c_str());
                fflush(stdout);
                busy=steps;
                champions.clear();
            }
            if (busy==steps) {
                champions.push_back(prog);
            }
            for (int i:n) {
                if (i) return 0; // halted, can expand more
            }
            return 1; // halted, don't expand more, can't use 0 vector
        }
    }
    // decider: graph_search2 / "power limit mod"
    cnt[cntstep++]++;
    for (int lim=1; lim<=4; lim++) {
        if (graph_search2(prog,maxidx,lim)) return 1; // nonhalt
    }
    // hard program
    cnt[cntstep++]++;
    printf("  HOLDOUT %s\n",program_str(prog).c_str());
    fflush(stdout);
    return 0; // expand more
}

void enumerate(int sz_max,int sz,program& prog) {
    // check for easy returns
    if (sz_max<sz) return;
    if (sz_max==sz) {
        solve(prog,sz_max-sz);
        return;
    }
    // add to num
    if (prog.back().back()<=0) {
        prog.back().back()--;
        enumerate(sz_max,sz+1,prog);
        prog.back().back()++;
    }
    if (prog.back().back()>=0) {
        prog.back().back()++;
        enumerate(sz_max,sz+1,prog);
        prog.back().back()--;
    }
    // add new num
    if (prog.back().back() || prog.back().size()<(prog.size()==1?2:prog[prog.size()-2].size())) {
        prog.back().push_back(0);
        enumerate(sz_max,sz,prog);
        prog.back().pop_back();
    }
    else if (!solve(prog,sz_max-sz)) {
        prog.push_back({0});
        enumerate(sz_max,sz+1,prog);
        prog.pop_back();
    }
}

int main() {
    freopen("fractran.txt","w",stdout);
    for (int sz=0; sz<=LIM; sz++) {
        fprintf(stderr,"sz %d\n",sz);
        printf("\n");
        cnt={}; for (int i=0; i<50; i++) cnt.push_back(0);
        champions.clear();
        program v{{0}};
        int t0=time(0);
        enumerate(sz,1,v);
        int t1=time(0);
        printf("sz=%d steps=%lld (time %d) (cnt benchmarks",sz,busy,t1-t0);
        for (ll i:cnt) {
            if (!i) break;
            printf(" %lld",i);
        }
        printf(")\n");
        printf("%d champions\n",champions.size());
        for (auto& p:champions) printf("  CHAMPION %s\n",program_str(p).c_str());
        fflush(stdout);
    }
}
