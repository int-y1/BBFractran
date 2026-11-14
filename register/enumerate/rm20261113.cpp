// register machine enumeration

#include <bits/stdc++.h>
using namespace std;

const int LIM=8; // sz to enumerate. limited to 1 size to keep the enumerator simple.
// use existing MBB(n) results?
// note: using MBB(8) = 3394 is ok but sketchy. MBB(8) has 6 holdouts, but if any holdout halts, the holdouts list for MBB(9) will be incomplete.
//const optional<pair<int,int>> USE_RESULTS=nullopt;
const optional<pair<int,int>> USE_RESULTS={{7,231}}; // use the fact that MBB(7) = 231
const bool EXPAND_HOLDOUT=1; // expand holdouts? (use 1 for completeness. use 0 if you're ok with halters making the holdouts list inaccurate)
const int CHAMPION_CNT=100; // number of champions to print
const bool CHAMPION_SORT=0; // 0 = sort by steps. 1 = sort by max register.

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
        if (s0.second.at(i)+s2.second.at(i)!=s1.second.at(i)+s1.second.at(i)) return 0; // not linear
    }
    vector<ll> k=s2.second;
    for (int i=0; i<s0.second.size(); i++) {
        k.at(i)-=s1.second.at(i);
        if (k.at(i)<0) return 0; // k has negative component
    }
    bool bad=0;
    while (s1!=s2) {
        visit(overloaded{
            [&s1](instruction_inc inst) {
                auto [c,n]=inst;
                s1.second.at(c)++;
                s1.first=n;
            },
            [&s1,&k,&bad](instruction_dec inst) {
                auto [c,n,m]=inst;
                // check that s1.second[c] and s1.second[c]+k[c] behave the same way
                if ((s1.second.at(c)>0)!=(s1.second.at(c)+k.at(c)>0)) bad=1;
                if (s1.second.at(c)) {
                    s1.second.at(c)--;
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
graph_plm is similar to fractran's "power limit mod"
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
                    t.second.at(c)++;
                    if (t.second.at(c)==2*lim) t.second.at(c)=lim;
                    ss.push_back(t);
                }
            },
            [&s,&found,&lim,&ss](instruction_dec inst) {
                auto [c,n,m]=inst;
                if (s.second.at(c)) {
                    if (n==0) found=1;
                    else {
                        fullstate t{n,s.second};
                        t.second.at(c)--;
                        ss.push_back(t);
                        if (t.second.at(c)==lim-1) {
                            t.second.at(c)+=lim;
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

/*
1 = cannot halt. 0 = unsure.
graph_pdlm is similar to fractran's "power difference limit mod"
*/
bool graph_pdlm(const program& prog,int maxreg,int lim) {
    assert(lim>=3); // max_e = 1, min_e = -1
    typedef pair<int,vector<pair<int,int>>> pdlmstate;
    vector<pdlmstate> q;
    set<pdlmstate> vis;
    {
        pdlmstate u0{1,{}};
        for (int i=0; i<=maxreg; i++) u0.second.push_back({0,i});
        q.push_back(u0);
        vis.insert(u0);
    }
    while (!q.empty()) {
        pdlmstate uu=q.back();
        q.pop_back();
        // get representatives of uu=compress_n(u)
        vector<pdlmstate> all_u0={uu};
        for (int i=0; i<=maxreg; i++) {
            if (uu.second.at(i).first>=lim) {
                vector<pdlmstate> tmp=all_u0;
                for (auto& u0:tmp) u0.second.at(i).first+=lim;
                for (auto& u0:tmp) all_u0.push_back(u0);
            }
        }
        for (auto& u1:all_u0) {
            fullstate u{u1.first,vector<ll>(maxreg+1)};
            u.second.at(u1.second.at(0).second)=u1.second.at(0).first;
            for (int i=1; i<=maxreg; i++) {
                u.second.at(u1.second.at(i).second)=u.second.at(u1.second.at(i-1).second)+u1.second.at(i).first;
            }
            // u is a representative of uu
            visit(overloaded{
                [&u](instruction_inc inst) {
                    auto [c,n]=inst;
                    u.second.at(c)++;
                    u.first=n;
                },
                [&u](instruction_dec inst) {
                    auto [c,n,m]=inst;
                    if (u.second.at(c)) {
                        u.second.at(c)--;
                        u.first=n;
                    }
                    else u.first=m;
                }
            },prog.at(u.first-1));
            if (u.first==0) return 0; // found a path from compress_n(u_0) to halt
            pdlmstate vv{u.first,{}}; // find vv=compress_n(v)
            int value0=0;
            vector<pair<int,int>> tmp_p;
            for (int i=0; i<=maxreg; i++) tmp_p.push_back({u.second.at(i),i});
            sort(tmp_p.begin(),tmp_p.end());
            for (auto& p:tmp_p) {
                auto [value1,i]=p;
                int tmp=value1-value0;
                while (tmp>=2*lim) tmp-=lim;
                vv.second.push_back({tmp,i});
                value0=value1;
            }
            if (!vis.count(vv)) {
                vis.insert(vv);
                q.push_back(vv);
            }
        }
    }
    return 1;
}

// returns programs that are worth exploring further
vector<ll> cnt;
vector<tuple<ll,vector<ll>,program>> champions; // {step count, registers, program}
tuple<ll,ll,string> best_champ{0,0,""},worst_champ{0,0,""};

tuple<ll,ll,string> champion_score(const tuple<ll,vector<ll>,program>& t) {
    ll regsum=0,regmax=0;
    for (ll i:get<1>(t)) {
        regsum+=i;
        regmax=max(regmax,i);
    }
    if (!CHAMPION_SORT) return {get<0>(t),regsum,program_str(get<2>(t))}; // sort by steps
    return {regmax,regsum,program_str(get<2>(t))}; // sort by max register
}

void reduce_champions() {
    stable_sort(champions.begin(),champions.end(),[](const tuple<ll,vector<ll>,program>& t1,const tuple<ll,vector<ll>,program>& t2) {
        return champion_score(t1)>champion_score(t2);
    });
    if (champions.size()>CHAMPION_CNT) champions.resize(CHAMPION_CNT);
    // logs
    if (best_champ!=champion_score(champions.front())) {
        best_champ=champion_score(champions.front());
        fprintf(stderr,"  CHAMPION 1 STEPS=%lld %s\n",
            get<0>(champions.front()),program_str(get<2>(champions.front())).c_str());
    }
    if (worst_champ!=champion_score(champions.back())) {
        worst_champ=champion_score(champions.back());
        fprintf(stderr,"  CHAMPION %d STEPS=%lld %s\n",champions.size(),
            get<0>(champions.back()),program_str(get<2>(champions.back())).c_str());
    }
}

vector<program> solve(int sz_max,const program& prog) {
    int cntstep=0;
    // check if undefined instruction exists
    cnt.at(cntstep++)++;
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
    cnt.at(cntstep++)++;
    fullstate s{1,vector<ll>(maxreg+1)};
    vector<fullstate> history;
    pair<int,int> last_transition;
    for (ll steps=0; steps<10000;) {
        history.push_back(s);
        if (steps>=3) {
            if (translated_cycle(prog,history.at(steps-steps/3-steps/3),history.at(steps-steps/3),s)) {
                return {}; // nonhalt
            }
        }
        visit(overloaded{
            [&s,&last_transition](instruction_inc inst) {
                auto [c,n]=inst;
                last_transition={s.first,0};
                s.second.at(c)++;
                s.first=n;
            },
            [&s,&last_transition](instruction_dec inst) {
                auto [c,n,m]=inst;
                if (s.second.at(c)) {
                    last_transition={s.first,1};
                    s.second.at(c)--;
                    s.first=n;
                }
                else {
                    last_transition={s.first,2};
                    s.first=m;
                }
            }
        },prog.at(s.first-1));
        steps++;
        if (USE_RESULTS && steps==USE_RESULTS->second+1 && prog.size()<=USE_RESULTS->first) return {}; // nonhalt
        if (s.first==0) { // halted
            if (0) { // check for bugs in the deciders
                for (int lim=5; lim<=8; lim++) assert(!graph_plm(prog,maxreg,lim));
                for (int lim=3; lim<=6; lim++) assert(!graph_pdlm(prog,maxreg,lim));
            }
            if (champions.size()<CHAMPION_CNT || champion_score(champions.at(CHAMPION_CNT-1))<=champion_score({steps,s.second,prog})) {
                champions.push_back({steps,s.second,prog});
                if (champions.size()>=CHAMPION_CNT*2) reduce_champions();
            }
            return expand_tnf(prog,last_transition,maxreg);
        }
    }
    // decider: graph_plm. this decider is confirmed correct up to MBB(8)
    cnt.at(cntstep++)++;
    for (int lim=5; lim<=8; lim++) {
        if (graph_plm(prog,maxreg,lim)) return {}; // nonhalt
    }
    // decider: graph_pdlm. this decider is confirmed correct up to MBB(8)
    cnt.at(cntstep++)++;
    for (int lim=3; lim<=6; lim++) {
        if (graph_pdlm(prog,maxreg,lim)) return {}; // nonhalt
    }
    // hard program
    cnt.at(cntstep++)++;
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
    for (int sz=LIM; sz<=LIM; sz++) {
        fprintf(stderr,"sz %d\n",sz);
        printf("\n");
        cnt={}; for (int i=0; i<50; i++) cnt.push_back(0);
        champions.clear();
        program v1{instruction_inc{0,0}};
        program v2{instruction_dec{0,0,0}};
        int t0=time(0);
        enumerate(sz,v1);
        enumerate(sz,v2);
        reduce_champions();
        int t1=time(0);
        printf("sz=%d (time %d) (cnt benchmarks",sz,t1-t0);
        for (ll i:cnt) {
            if (!i) break;
            printf(" %lld",i);
        }
        printf(")\n");
        string champ_file="tmp_sz";
        champ_file+=to_string(sz);
        if (!CHAMPION_SORT) champ_file+="_step.txt";
        else champ_file+="_reg.txt";
        FILE* f=fopen(champ_file.c_str(),"w");
        for (auto& p:champions) {
            fprintf(f,"%s %lld:",program_str(get<2>(p)).c_str(),get<0>(p));
            for (ll i:get<1>(p)) fprintf(f," %lld",i);
            fprintf(f,"\n");
        }
        fclose(f);
        printf("top %d champions saved to %s\n",champions.size(),champ_file.c_str());
        fflush(stdout);
    }
}
