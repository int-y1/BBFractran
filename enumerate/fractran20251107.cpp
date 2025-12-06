// fractran enumeration, run to size 19 finished on nov 7
// HARDEST TC 551 [9/20, 375/7, 2/3, 49/2]

#include <gmpxx.h>
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;

const int LIM=40; // max sz to enumerate
vector<mpz_class> primes;

string program_str(const vector<mpz_class>& fracs) {
    assert(fracs.size()%2==0);
    string out="[";
    for (int i=0; i<fracs.size(); i+=2) {
        if (i>0) out+=", ";
        out+=fracs[i].get_str();
        out+="/";
        out+=fracs[i+1].get_str();
    }
    out+="]";
    return out;
}

// find a subset of fractions s.t. at least 1 fraction is always active.
// true = nonhalt. false = undecided.
bool active_subset(const vector<mpz_class>& fracs) {
    // precompute
    mpz_class tmp;
    vector<bool> start;
    for (int i=1; i<fracs.size(); i+=2) start.push_back(2%fracs[i]==0);
    vector<vector<bool>> activate_nd;
    vector<vector<bool>> coprime_dd;
    for (int i=1; i<fracs.size(); i+=2) {
        activate_nd.push_back({});
        coprime_dd.push_back({});
        for (int j=1; j<fracs.size(); j+=2) {
            activate_nd.back().push_back(fracs[i-1]%fracs[j]==0);
            mpz_gcd(tmp.get_mpz_t(),fracs[i].get_mpz_t(),fracs[j].get_mpz_t());
            coprime_dd.back().push_back(tmp==1);
        }
    }
    // find a good subset
    for (int m=(1<<start.size())-1; m>0; m--) {
        // start value 2 is ok
        bool ok=0;
        for (int i=0; i<start.size(); i++) {
            if (start[i] && (m&(1<<i))) {
                ok=1;
                break;
            }
        }
        if (!ok) continue;
        // preserve active
        for (int i=0; i<start.size(); i++) {
            bool activate=0,coprime=1;
            for (int j=0; j<start.size(); j++) {
                if (activate_nd[i][j] && (m&(1<<j))) activate=1;
                if (!coprime_dd[i][j] && (m&(1<<j))) coprime=0;
            }
            if (!activate && !coprime) {
                ok=0;
                break;
            }
        }
        if (ok) {
            //printf("  active_subset %s : ",program_str(fracs).c_str());
            //for (int i=0; i<start.size(); i++) printf("%c",(m&1<<i)?'1':'0');
            //printf("\n");
            return 1;
        }
    }
    return 0;
}

bool translated_cycle(const vector<mpz_class>& fracs,mpz_class n,mpz_class n2) {
    mpz_class k=n2/n,rem,tmp;
    while (n!=n2) {
        for (int i=1; i<fracs.size(); i+=2) {
            if (n%fracs[i]==0) {
                n=n/fracs[i]*fracs[i-1];
                break;
            }
            else {
                // check that n*l^inf doesn't work
                rem=fracs[i];
                mpz_gcd(tmp.get_mpz_t(),n.get_mpz_t(),rem.get_mpz_t());
                rem/=tmp;
                while (1) {
                    mpz_gcd(tmp.get_mpz_t(),k.get_mpz_t(),rem.get_mpz_t());
                    if (tmp==1) break;
                    rem/=tmp;
                }
                if (rem==1) return 0;
            }
        }
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
vector<vector<mpz_class>> champions;
bool solve(const vector<vector<int>>& nums,int rem) {
    cnt[0]++;
    {
        bool has_neg=0;
        for (int i:nums.back()) {
            if (i<0) has_neg=1;
        }
        if (!has_neg) return 1; // x/1, nonhalt
    }
    // check for needed primes
    cnt[1]++;
    {
        int need_pos=0,need_neg=0;
        for (int i=1; i<nums.back().size(); i++) {
            bool has_pos=0,has_neg=0;
            for (int j=0; j<nums.size() && i<nums[j].size(); j++) {
                if (nums[j][i]>0) has_pos=1;
                if (nums[j][i]<0) has_neg=1;
            }
            if (!has_pos && has_neg) need_pos++; // need to add primes[i] later
            if (has_pos && !has_neg) need_neg++; // need to add primes[i] later
        }
        bool denom2=0; // contains x/2
        for (int j=0; j<nums.size(); j++) {
            if (nums[j][0]!=-1) continue;
            bool ok=1;
            for (int i=1; i<nums[j].size(); i++) {
                if (nums[j][i]<0) ok=0;
            }
            if (ok) denom2=1;
        }
        int needed;
        if (denom2) {
            if (need_pos || need_neg) needed=need_pos+need_neg+1; // 1 more fraction
            else needed=0; // already done
        }
        else if (need_neg) needed=need_pos+need_neg+2+1; // 2 more fractions
        else needed=need_pos+1+1; // 1 more fraction
        if (needed>rem) return 1; // pruned, too inefficient with primes
    }
    // handle the interchanging primes
    cnt[2]++;
    {
        vector<vector<int>> primeorder;
        // start at i=1 (prime number 3), because all primes >=3 are equal.
        // leave out prime number 2, because it's the starting number.
        for (int i=1; i<nums.back().size(); i++) { // i = prime idx
            vector<int> tmp;
            for (int j=0; j<nums.size(); j++) {
                tmp.push_back(i<nums[j].size()?int_ordering(nums[j][i]):0);
            }
            primeorder.push_back(tmp);
        }
        for (int i=1; i<primeorder.size(); i++) {
            if (primeorder[i-1]<primeorder[i]) return 1; // redundant
        }
    }
    // convert to numbers
    cnt[3]++;
    vector<mpz_class> fracs;
    {
        mpz_class tmp,tmp2;
        for (auto& n:nums) {
            tmp=1; tmp2=1;
            for (int i=0; i<n.size(); i++) {
                for (int j=1; j<=n[i]; j++) tmp*=primes[i];
                for (int j=1; j<=-n[i]; j++) tmp2*=primes[i];
            }
            fracs.push_back(tmp);
            fracs.push_back(tmp2);
        }
    }
    for (int i=1; i+2<fracs.size(); i+=2) {
        if (fracs.back()%fracs[i]==0) return 1; // covered fraction, i.e. unused fraction
    }
    // decider: translated cycler + direct simulation
    print0++;
    if (print0>=print1) {
        print1=print1*21/20;
        fprintf(stderr,"sample %lld %s\n",print0,program_str(fracs).c_str());
    }
    cnt[4]++;
    mpz_class n=2;
    vector<mpz_class> history;
    for (ll steps=0; steps<10000; steps++) {
        history.push_back(n);
        if (steps>=2 && n%history[steps/2]==0) {
            if (translated_cycle(fracs,history[steps/2],n)) {
                if (tc_record<steps) {
                    tc_record=steps;
                    fprintf(stderr,"  HARDEST TC %lld %s\n",tc_record,program_str(fracs).c_str());
                }
                return 1; // nonhalt
            }
        }
        bool found=0;
        for (int i=1; i<fracs.size(); i+=2) {
            if (n%fracs[i]==0) {
                n=n/fracs[i]*fracs[i-1];
                found=1;
                break;
            }
        }
        if (!found) { // halted
            if (busy<steps) {
                fprintf(stderr,"  NEW CHAMPION %lld %s\n",steps,program_str(fracs).c_str());
                fflush(stdout);
                busy=steps;
                champions.clear();
            }
            if (busy==steps) {
                champions.push_back(fracs);
            }
            if (n==1) return 1; // halted, don't expand more (x/1 is unusable)
            return 0; // halted, can expand more
        }
    }
    // decider: active subset
    cnt[5]++;
    if (active_subset(fracs)) return 1; // nonhalt
    // hard program
    printf("  HOLDOUT %s\n",program_str(fracs).c_str());
    fflush(stdout);
    return 0; // expand more
}

void enumerate(int sz_max,int sz,vector<vector<int>>& nums) {
    // check for easy returns
    if (sz_max<sz) return;
    if (sz_max==sz) {
        solve(nums,sz_max-sz);
        return;
    }
    // add to num
    if (nums.back().back()<=0) {
        nums.back().back()--;
        enumerate(sz_max,sz+1,nums);
        nums.back().back()++;
    }
    if (nums.back().back()>=0) {
        nums.back().back()++;
        enumerate(sz_max,sz+1,nums);
        nums.back().back()--;
    }
    // add new num
    if (nums.back().back() || nums.back().size()<(nums.size()==1?2:nums[nums.size()-2].size())) {
        nums.back().push_back(0);
        enumerate(sz_max,sz,nums);
        nums.back().pop_back();
    }
    else if (!solve(nums,sz_max-sz)) {
        nums.push_back({0});
        enumerate(sz_max,sz+1,nums);
        nums.pop_back();
    }
}

int main() {
    freopen("fractran.txt","w",stdout);
    for (mpz_class p=2; primes.size()<LIM+5;) {
        primes.push_back(p);
        mpz_nextprime(p.get_mpz_t(),p.get_mpz_t());
    }
    for (int sz=0; sz<=LIM; sz++) {
        fprintf(stderr,"sz %d\n",sz);
        printf("\n");
        cnt={0,0,0,0,0,0};
        champions.clear();
        vector<vector<int>> v{{0}};
        int t0=time(0);
        enumerate(sz,1,v);
        int t1=time(0);
        printf("sz=%d steps=%lld (cnt benchmarks %lld %lld %lld %lld %lld %lld) (time %d)\n",sz,busy,cnt[0],cnt[1],cnt[2],cnt[3],cnt[4],cnt[5],t1-t0);
        for (auto& p:champions) printf("  CHAMPION %s\n",program_str(p).c_str());
        fflush(stdout);
    }
}
