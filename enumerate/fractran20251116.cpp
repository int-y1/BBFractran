// fractran enumeration, run to size 21 finished on nov 16

#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef vector<int> fraction;
typedef vector<fraction> program;

const int THREADS=12; // number of workers to spawn
const int LIM=21; // max sz to enumerate
const vector<int> PRIMES{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}; // copied from https://oeis.org/A000040

// convert prog to a list of fractions. hopefully it doesn't overflow ll.
string program_str(const program& prog) {
    string out="[";
    for (int i=0; i<prog.size(); i++) {
        if (i>0) out+=", ";
        ll f1=1,f2=1;
        for (int j=0; j<prog.at(i).size(); j++) {
            for (int k=1; k<=prog.at(i).at(j); k++) f1*=PRIMES[j];
            for (int k=1; k<=-prog.at(i).at(j); k++) f2*=PRIMES[j];
        }
        out+=to_string(f1);
        out+="/";
        out+=to_string(f2);
    }
    out+="]";
    return out;
}

// 1 = cycle detected. 0 = unsure.
bool translated_cycle(const program& prog,fraction n0,fraction n1,fraction n2) {
    for (int i=0; i<n0.size(); i++) {
        if (n0.at(i)+n2.at(i)!=n1.at(i)+n1.at(i)) return 0; // not geometric
    }
    fraction k=n2;
    for (int i=0; i<n0.size(); i++) {
        k.at(i)-=n1.at(i);
        if (k.at(i)<0) return 0; // k has denominator
    }
    while (n1!=n2) {
        for (auto& f:prog) {
            bool apply=1;
            for (int i=0; i<f.size(); i++) {
                if (n1.at(i)+f.at(i)<0) {
                    apply=0;
                    break;
                }
            }
            if (apply) {
                for (int i=0; i<f.size(); i++) n1.at(i)+=f.at(i);
                break;
            }
            else {
                // check that n1*k^inf doesn't work
                bool apply2=1;
                for (int i=0; i<f.size(); i++) {
                    if (k.at(i)==0 && n1.at(i)+f.at(i)<0) {
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
        start.at(0)=1;
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
                if (u.at(i)+f.at(i)<0) {
                    apply=0;
                    break;
                }
            }
            if (apply) {
                // inst matches, get next states
                vector<fraction> v0{};
                v0.push_back({});
                for (int i=0; i<maxidx; i++) {
                    int r0=u.at(i)+(i<f.size()?f.at(i):0);
                    while (r0>=2*exp_lim) r0-=exp_lim;
                    for (auto& f0:v0) f0.push_back(r0);
                    if (r0<exp_lim && u.at(i)>=exp_lim) {
                        // double it
                        int sz=v0.size();
                        for (int i=0; i<sz; i++) {
                            fraction f0=v0.at(i);
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

/*
1 = cannot halt. 0 = unsure.
idea of lin_comb

* the list [a,b,c,d,...] represents the number 2^a * 3^b * 5^c * 7^d * ...
* find coefficients c_a, c_b, c_c, c_d, ... that satisfy
  * c_a > 0, starting number is positive
  * if sum(i*c_i) > 0, a fraction can be used
  * for each fraction, sum(i*c_i) stays the same or increases
* if coefficients exist, the program is non-halt, and the certificate is LIN_COMB(c_a, c_b, c_c, c_d, ...)

*/
bool lin_comb(const program& prog,int maxidx,int exp_lim) {
    vector<bool> usable(maxidx);
    for (auto& f:prog) {
        int cnt1=0,cnt2=0,found1=0;
        for (int i=0; i<f.size(); i++) {
            if (f.at(i)<-1) cnt2++;
            else if (f.at(i)==-1) {cnt1++; found1=i;}
        }
        if (cnt2==0 && cnt1==1) usable[found1]=1;
    }
    if (!usable.at(0)) return 0;
    vector<vector<int>> c0;
    for (int i=0; i<maxidx; i++) {
        int r0,r1;
        if (i==0) {r0=1; r1=exp_lim;}
        else if (usable[i]) {r0=-exp_lim; r1=exp_lim;}
        else {r0=-exp_lim; r1=0;}
        vector<int> range;
        for (int j=r0; j<=r1; j++) range.push_back(j);
        c0.push_back(range);
    }
    vector<int> idx(maxidx),c(maxidx);
    while (1) {
        for (int i=0; i<maxidx; i++) c.at(i)=c0.at(i).at(idx.at(i));
        // every inst should be >=0
        bool ok=1;
        for (auto& f:prog) {
            int sum=0;
            for (int j=0; j<f.size(); j++) sum+=c.at(j)*f.at(j);
            if (sum<0) {
                ok=0;
                break;
            }
        }
        if (ok) return 1;
        // go to next product
        for (int i=maxidx-1; i>=0; i--) {
            idx.at(i)++;
            if (idx.at(i)<c0.at(i).size()) break;
            if (i==0) return 0; // went through all products
            idx.at(i)=0;
        }
    }
    return 0;
}

// 0 1 -1 2 -2 3 -3 ...
int int_ordering(int x) {
    if (x>0) return x*2-1;
    return -x*2;
}

struct workresult {
    ll tc_record=0;
    vector<ll> cnt=vector<ll>(50);
    ll busy=0;
    vector<program> champions;
};
mutex work_mutex;
workresult final_wr;

// rem = number of remaining primes
// return 1 = don't expand. return 0 = expand more.
bool solve(const program& prog,int rem,workresult& wr) {
    int cntstep=0;
    // check for x/1
    wr.cnt[cntstep++]++;
    {
        bool neg=0;
        for (int j=0; j<prog.back().size(); j++) {
            if (prog.back().at(j)<0) neg=1;
        }
        if (!neg) return 1; // x/1, nonhalt
    }
    // check if program can be made complete within a cost of "rem".
    // assume that the rows in prog are finished, and we can only add new rows.
    int maxidx=1;
    for (auto& f:prog) maxidx=max(maxidx,(int)f.size());
    wr.cnt[cntstep++]++;
    {
        int need_pos=0,need_neg=0;
        for (int i=1; i<maxidx; i++) {
            bool has_pos=0,has_neg=0;
            for (auto& f:prog) {
                if (f.size()<=i) continue;
                if (f.at(i)>0) has_pos=1;
                if (f.at(i)<0) has_neg=1;
            }
            if (!has_pos && has_neg) need_pos++; // need to add primes[i] later
            if (has_pos && !has_neg) need_neg++; // need to add primes[i] later
        }
        bool denom2=0; // contains x/2
        for (auto& f:prog) {
            if (f.at(0)!=-1) continue;
            bool ok=1;
            for (int i=1; i<f.size(); i++) {
                if (f.at(i)<0) ok=0;
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
    wr.cnt[cntstep++]++;
    {
        vector<vector<int>> primeorder;
        // start at i=1 (prime number 3), because all primes >=3 are treated equally.
        // leave out i=0 (prime number 2), because 2 is treated differently (it's the starting number).
        for (int i=1; i<maxidx; i++) { // i = prime idx
            vector<int> tmp;
            for (auto& f:prog) tmp.push_back(int_ordering(i<f.size()?f.at(i):0));
            primeorder.push_back(tmp);
        }
        for (int i=1; i<primeorder.size(); i++) {
            if (primeorder.at(i-1)<primeorder.at(i)) return 1; // redundant due to column order
        }
    }
    // check for covered denominator
    wr.cnt[cntstep++]++;
    for (int i=0; i+1<prog.size(); i++) {
        bool covered=1;
        for (int j=0; j<maxidx; j++) {
            int k0=(prog.at(i).size()>j?prog.at(i).at(j):0);
            int k1=(prog.back().size()>j?prog.back().at(j):0);
            if ((k1>=0 && k0<0) || (k1<0 && k0<k1)) {
                covered=0;
                break;
            }
        }
        if (covered) return 1; // covered, prog.back() is never used
    }
    // decider: translated cycler + direct simulation
    wr.cnt[cntstep++]++;
    fraction n(maxidx);
    n.at(0)=1;
    vector<fraction> history;
    for (ll steps=0; steps<10000; steps++) {
        history.push_back(n);
        if (steps>=3) {
            if (translated_cycle(prog,history.at(steps-steps/3-steps/3),history.at(steps-steps/3),n)) {
                if (wr.tc_record<steps) {
                    wr.tc_record=steps;
                    lock_guard guard(work_mutex);
                    if (final_wr.tc_record<steps) {
                        final_wr.tc_record=steps;
                        fprintf(stderr,"  HARDEST TC %lld %s\n",wr.tc_record,program_str(prog).c_str());
                    }
                }
                return 1; // nonhalt
            }
        }
        bool found=0;
        for (auto& f:prog) {
            bool apply=1;
            for (int i=0; i<f.size(); i++) {
                if (n.at(i)+f.at(i)<0) {
                    apply=0;
                    break;
                }
            }
            if (apply) {
                for (int i=0; i<f.size(); i++) n.at(i)+=f.at(i);
                found=1;
                break;
            }
        }
        if (!found) { // halted
            if (wr.busy<=steps) {
                if (wr.busy<steps) wr.champions.clear(); // fix a weirdness with wr==final_wr in enumerate2
                wr.busy=steps;
                lock_guard guard(work_mutex);
                if (final_wr.busy<steps) {
                    final_wr.busy=steps;
                    final_wr.champions.clear();
                    fprintf(stderr,"  NEW CHAMPION %lld %s\n",steps,program_str(prog).c_str());
                }
                if (final_wr.busy==steps) {
                    final_wr.champions.push_back(prog);
                }
            }
            for (int i:n) {
                if (i) return 0; // halted, can expand more
            }
            return 1; // halted, don't expand more, can't use 0 vector
        }
    }
    // decider: graph_search2 / "power limit mod"
    wr.cnt[cntstep++]++;
    for (int lim=1; lim<=6; lim++) {
        if (graph_search2(prog,maxidx,lim)) return 1; // nonhalt
    }
    // decider: linear combination
    wr.cnt[cntstep++]++;
    for (int lim=1; lim<=4; lim++) {
        if (lin_comb(prog,maxidx,lim)) return 1; // nonhalt
    }
    // hard program
    wr.cnt[cntstep++]++;
    lock_guard guard(work_mutex);
    printf("  HOLDOUT %s\n",program_str(prog).c_str());
    fflush(stdout);
    return 0; // expand more
}

// newcol = number of new primes added (except 2 and 3 are not new primes)
void enumerate(int sz_max,int sz,program& prog,int newcol,workresult& wr) {
    // check for easy returns
    if (sz+(newcol>0?newcol+1:0)>sz_max) return; // if newcol>0, need a new row with these primes
    if (sz_max==sz) {
        solve(prog,sz_max-sz,wr);
        return;
    }
    assert(sz_max>sz);
    // add to num
    if (prog.back().back()<=0) {
        prog.back().back()--;
        enumerate(sz_max,sz+1,prog,newcol,wr);
        prog.back().back()++;
    }
    if (prog.back().back()>=0) {
        prog.back().back()++;
        enumerate(sz_max,sz+1,prog,newcol,wr);
        prog.back().back()--;
    }
    // add new num
    if (prog.back().size()<(prog.size()==1?2:prog.at(prog.size()-2).size())) {
        prog.back().push_back(0);
        enumerate(sz_max,sz,prog,0,wr);
        prog.back().pop_back();
    }
    else {
        prog.back().push_back(-1);
        enumerate(sz_max,sz+1,prog,newcol+1,wr);
        prog.back().back()=1;
        enumerate(sz_max,sz+1,prog,newcol+1,wr);
        prog.back().pop_back();
        if (!solve(prog,sz_max-sz,wr)) {
            prog.push_back({0});
            enumerate(sz_max,sz+1,prog,0,wr);
            prog.pop_back();
        }
    }
}

vector<tuple<int,int,program,int>> work;
void worker() {
    workresult wr;
    while (1) {
        tuple<int,int,program,int> w;
        {
            lock_guard guard(work_mutex);
            if (work.empty()) {
                for (int i=0; i<final_wr.cnt.size(); i++) {
                    final_wr.cnt.at(i)+=wr.cnt.at(i);
                }
                return;
            }
            w=work.back();
            work.pop_back();
        }
        enumerate(get<0>(w),get<1>(w),get<2>(w),get<3>(w),wr);
    }
}

// newcol = number of new primes added (except 2 and 3 are not new primes)
void enumerate2(int sz_max,int sz,program& prog,int newcol,int countdown) {
    // check for easy returns
    if (sz+(newcol>0?newcol+1:0)>sz_max) return; // if newcol>0, need a new row with these primes
    if (sz_max==sz) {
        solve(prog,sz_max-sz,final_wr);
        return;
    }
    if (countdown==0) {
        work.push_back({sz_max,sz,prog,newcol});
        return;
    }
    // add to num
    if (prog.back().back()<=0) {
        prog.back().back()--;
        enumerate2(sz_max,sz+1,prog,newcol,countdown-1);
        prog.back().back()++;
    }
    if (prog.back().back()>=0) {
        prog.back().back()++;
        enumerate2(sz_max,sz+1,prog,newcol,countdown-1);
        prog.back().back()--;
    }
    // add new num
    if (prog.back().size()<(prog.size()==1?2:prog.at(prog.size()-2).size())) {
        prog.back().push_back(0);
        enumerate2(sz_max,sz,prog,0,countdown-1);
        prog.back().pop_back();
    }
    else {
        prog.back().push_back(-1);
        enumerate2(sz_max,sz+1,prog,newcol+1,countdown-1);
        prog.back().back()=1;
        enumerate2(sz_max,sz+1,prog,newcol+1,countdown-1);
        prog.back().pop_back();
        if (!solve(prog,sz_max-sz,final_wr)) {
            prog.push_back({0});
            enumerate2(sz_max,sz+1,prog,0,countdown-1);
            prog.pop_back();
        }
    }
}

int main() {
    freopen("fractran.txt","w",stdout);
    for (int sz=1; sz<=LIM; sz++) {
        fprintf(stderr,"sz %d\n",sz);
        printf("\n");
        work.clear();
        final_wr=workresult();
        program v{{0}};
        ll t0=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        enumerate2(sz,1,v,0,10);
        ll t1=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        printf("sz=%d work_units=%d (time %lld)\n",sz,work.size(),t1-t0);
        fflush(stdout);
        vector<thread> tt;
        for (int i=0; i<THREADS; i++) tt.emplace_back(worker);
        for (auto& t:tt) t.join();
        ll t2=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        printf("sz=%d steps=%lld (time %lld) (cnt benchmarks",sz,final_wr.busy,t2-t1);
        for (ll i:final_wr.cnt) {
            if (!i) break;
            printf(" %lld",i);
        }
        printf(")\n");
        printf("%d champions\n",final_wr.champions.size());
        sort(final_wr.champions.begin(),final_wr.champions.end());
        for (auto& p:final_wr.champions) printf("  CHAMPION %s\n",program_str(p).c_str());
        fflush(stdout);
    }
}
