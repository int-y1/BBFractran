// register machine enumeration

#include <bits/stdc++.h>
using namespace std;

const int LIM=8; // max sz to enumerate
const bool USE_RESULTS=1; // use the fact that MBB(7) = 231 (TODO: improve the deciders so that MBB(7) has no holdouts)
const bool EXPAND_HOLDOUT=0; // expand holdouts? (use 1 for completeness. use 0 if you're ok with halters making the holdouts list inaccurate)

// instructions are numbered 1 (A), 2 (B), 3 (C), ...
// instruction 0 represents undefined
// registers are numbered 0, 1, 2, ...
typedef long long ll;
typedef tuple<int,int> instruction_inc; // [c,n]
typedef tuple<int,int,int> instruction_dec; // [c,n,m]
typedef variant<instruction_inc,instruction_dec> instruction;
typedef vector<instruction> program;
typedef pair<int,vector<ll>> fullstate; // {state, registers}

// for visit()
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };

string program_str(const program& prog) {
    string out="";
    for (auto& inst:prog) {
        if (!out.empty()) out.push_back('_');
        visit(overloaded{
            [&out](instruction_inc inst) {
                auto [c,n]=inst;
                out.push_back('0'+c);
                out.push_back('+');
                out.push_back(n?'A'+n-1:'*');
            },
            [&out](instruction_dec inst) {
                auto [c,n,m]=inst;
                out.push_back('0'+c);
                out.push_back('-');
                out.push_back(n?'A'+n-1:'*');
                out.push_back(m?'A'+m-1:'*');
            }
        },inst);
    }
    return out;
}

vector<program> expand_tnf(const program& prog1,pair<int,int> transition,int maxreg) {
    auto [n1,i1]=transition;
    vector<program> out;
    for (int n=1; n<=prog1.size()+1; n++) {
        program prog2=prog1;
        if (i1==0) get<1>(get<instruction_inc>(prog2.at(n1-1)))=n;
        else if (i1==1) get<1>(get<instruction_dec>(prog2.at(n1-1)))=n;
        else if (i1==2) get<2>(get<instruction_dec>(prog2.at(n1-1)))=n;
        else assert(0); // shouldn't happen
        if (n<=prog1.size()) out.push_back(prog2);
        else {
            for (int reg=0; reg<=maxreg+1; reg++) {
                program prog3=prog2;
                prog3.push_back(instruction_inc{reg,0});
                out.push_back(prog3);
            }
            for (int reg=0; reg<=maxreg+1; reg++) {
                program prog3=prog2;
                prog3.push_back(instruction_dec{reg,0,0});
                out.push_back(prog3);
            }
        }
    }
    return out;
}

// 1 = cycle detected. 0 = unsure.
bool translated_cycle(const program& prog,fullstate s0,fullstate s1,fullstate s2) {
    if (s0.first!=s1.first || s1.first!=s2.first) return 0; // different state
    for (int i=0; i<s0.second.size(); i++) {
        if (s0.second[i]+s2.second[i]!=s1.second[i]+s1.second[i]) return 0; // not linear
    }
    vector<ll> k=s2.second;
    for (int i=0; i<s0.second.size(); i++) {
        k[i]-=s1.second[i];
        if (k[i]<0) return 0; // k has negative component
    }
    bool bad=0;
    while (s1!=s2) {
        visit(overloaded{
            [&s1](instruction_inc inst) {
                auto [c,n]=inst;
                s1.second[c]++;
                s1.first=n;
            },
            [&s1,&k,&bad](instruction_dec inst) {
                auto [c,n,m]=inst;
                // check that s1.second[c] and s1.second[c]+k[c] behave the same way
                if ((s1.second[c]>0)!=(s1.second[c]+k[c]>0)) bad=1;
                if (s1.second[c]) {
                    s1.second[c]--;
                    s1.first=n;
                }
                else {
                    s1.first=m;
                }
            }
        },prog.at(s1.first-1));
        if (bad) return 0;
    }
    return 1;
}

/*
1 = cannot halt. 0 = unsure.
idea of graph_plm (similar to fractran's "power limit mod")

* LIM is the register limit
* do a graph search, but limit the registers to 2*LIM different groups
  * split into 2 groups, <LIM and >=LIM
  * split into LIM groups, the groups are mod LIM
  * (the code uses the numbers 0,1,...,2*LIM-1 to represent these groups)
* if halting never occurs, the program runs forever

*/
bool graph_plm(const program& prog,int maxreg,int lim) {
    vector<fullstate> q;
    set<fullstate> vis;
    {
        fullstate s{1,vector<ll>(maxreg+1)};
        q.push_back(s);
        vis.insert(s);
    }
    // note: fractran's "guarantee that the same inst is always used" doesn't apply
    assert(lim>=1);
    while (!q.empty()) {
        fullstate s=q.back();
        q.pop_back();
        bool found=0; // found halt state?
        vector<fullstate> ss{}; // next states
        visit(overloaded{
            [&s,&found,&lim,&ss](instruction_inc inst) {
                auto [c,n]=inst;
                if (n==0) found=1;
                else {
                    fullstate t{n,s.second};
                    t.second[c]++;
                    if (t.second[c]==2*lim) t.second[c]=lim;
                    ss.push_back(t);
                }
            },
            [&s,&found,&lim,&ss](instruction_dec inst) {
                auto [c,n,m]=inst;
                if (s.second[c]) {
                    if (n==0) found=1;
                    else {
                        fullstate t{n,s.second};
                        t.second[c]--;
                        ss.push_back(t);
                        if (t.second[c]==lim-1) {
                            t.second[c]+=lim;
                            ss.push_back(t);
                        }
                    }
                }
                else {
                    if (m==0) found=1;
                    else ss.push_back(fullstate{m,s.second});
                }
            }
        },prog.at(s.first-1));
        if (found) return 0;
        for (auto& t:ss) {
            if (vis.count(t)) continue;
            vis.insert(t);
            q.push_back(t);
        }
    }
    return 1;
}

// returns programs that are worth exploring further
vector<ll> cnt;
ll busy1=0; // steps
ll busy2=0; // max register
vector<program> champions1;
vector<program> champions2;
vector<program> solve(int sz_max,const program& prog) {
    int cntstep=0;
    // check if undefined instruction exists
    cnt[cntstep++]++;
    int maxreg=0;
    bool has_undefined=0;
    for (auto& inst:prog) {
        visit(overloaded{
            [&maxreg,&has_undefined](instruction_inc inst) {
                auto [c,n]=inst;
                maxreg=max(maxreg,c);
                if (n==0) has_undefined=1;
            },
            [&maxreg,&has_undefined](instruction_dec inst) {
                auto [c,n,m]=inst;
                maxreg=max(maxreg,c);
                if (n==0) has_undefined=1;
                if (m==0) has_undefined=1;
            }
        },inst);
    }
    if (!has_undefined) return {}; // nonhalt
    // decider: translated cycler + direct simulation
    cnt[cntstep++]++;
    fullstate s{1,vector<ll>(maxreg+1)};
    vector<fullstate> history;
    pair<int,int> last_transition;
    for (ll steps=0; steps<10000;) {
        history.push_back(s);
        if (steps>=3) {
            if (translated_cycle(prog,history[steps-steps/3-steps/3],history[steps-steps/3],s)) {
                return {}; // nonhalt
            }
        }
        visit(overloaded{
            [&s,&last_transition](instruction_inc inst) {
                auto [c,n]=inst;
                last_transition={s.first,0};
                s.second[c]++;
                s.first=n;
            },
            [&s,&last_transition](instruction_dec inst) {
                auto [c,n,m]=inst;
                if (s.second[c]) {
                    last_transition={s.first,1};
                    s.second[c]--;
                    s.first=n;
                }
                else {
                    last_transition={s.first,2};
                    s.first=m;
                }
            }
        },prog.at(s.first-1));
        steps++;
        if (USE_RESULTS && steps==231+1 && prog.size()<=7) return {}; // nonhalt
        if (s.first==0) { // halted
            if (busy1<steps) {
                fprintf(stderr,"  NEW CHAMPION STEPS=%lld %s\n",steps,program_str(prog).c_str());
                fflush(stdout);
                busy1=steps;
                champions1.clear();
            }
            if (busy1==steps) {
                champions1.push_back(prog);
            }
            for (ll i:s.second) {
                if (busy2<i) {
                    fprintf(stderr,"  NEW CHAMPION REG=%lld %s\n",i,program_str(prog).c_str());
                    fflush(stdout);
                    busy2=i;
                    champions2.clear();
                }
                if (busy2==i) {
                    champions2.push_back(prog);
                }
            }
            return expand_tnf(prog,last_transition,maxreg);
        }
    }
    // decider: graph_plm
    cnt[cntstep++]++;
    for (int lim=5; lim<=8; lim++) {
        if (graph_plm(prog,maxreg,lim)) return {}; // nonhalt
    }
    // hard program
    cnt[cntstep++]++;
    vector<program> out;
    printf("  HOLDOUT %s\n",program_str(prog).c_str());
    //fflush(stdout);
    if (EXPAND_HOLDOUT) {
        for (int i=1; i<=prog.size(); i++) {
            visit(overloaded{
                [&out,&prog,&i,&maxreg](instruction_inc inst) {
                    auto [c,n]=inst;
                    if (n==0) {
                        for (auto& prog2:expand_tnf(prog,{i,0},maxreg)) out.push_back(prog2);
                    }
                },
                [&out,&prog,&i,&maxreg](instruction_dec inst) {
                    auto [c,n,m]=inst;
                    if (n==0) {
                        for (auto& prog2:expand_tnf(prog,{i,1},maxreg)) out.push_back(prog2);
                    }
                    if (m==0) {
                        for (auto& prog2:expand_tnf(prog,{i,2},maxreg)) out.push_back(prog2);
                    }
                }
            },prog.at(i-1));
        }
    }
    return out;
}

void enumerate(int sz_max,program& prog) {
    if (sz_max<prog.size()) return;
    for (auto& prog2:solve(sz_max,prog)) {
        enumerate(sz_max,prog2);
    }
}

int main() {
    freopen("tmp.txt","w",stdout);
    for (int sz=1; sz<=LIM; sz++) {
        fprintf(stderr,"sz %d\n",sz);
        printf("\n");
        cnt={}; for (int i=0; i<50; i++) cnt.push_back(0);
        //busy1=busy2=0;
        champions1.clear();
        champions2.clear();
        program v1{instruction_inc{0,0}};
        program v2{instruction_dec{0,0,0}};
        int t0=time(0);
        enumerate(sz,v1);
        enumerate(sz,v2);
        int t1=time(0);
        printf("sz=%d steps=%lld reg=%lld (time %d) (cnt benchmarks",sz,busy1,busy2,t1-t0);
        for (ll i:cnt) {
            if (!i) break;
            printf(" %lld",i);
        }
        printf(")\n");
        printf("%d champions1 (steps)\n",champions1.size());
        for (auto& p:champions1) printf("  CHAMPION1 (steps) %s\n",program_str(p).c_str());
        printf("%d champions2 (reg)\n",champions2.size());
        for (auto& p:champions2) printf("  CHAMPION2 (reg) %s\n",program_str(p).c_str());
        fflush(stdout);
    }
}
