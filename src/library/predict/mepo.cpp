#include <algorithm>
#include "predictor.cpp"

inline double sq(const double& x) { return x * x; }

double cosine(const LDMap &syms1, const LVec &syms2,
              const Tfidf &tfidf){
  double sig = 0, sig1 = 0, sig2 = 0;
  for (auto s : syms1)
    sig1 += sq(tfidf.get(s.first)) * sq(s.second);
  for (auto s : syms2) {
    const double tw = tfidf.get(s);
    sig2 += sq(tw);
    auto got = syms1.find(s);
    if (got != syms1.end())
      sig += sq(tw) * got->second;
  }
  return (sq(sig) / (sig1 * sig2));
  // for jaccard use:
  // return (sig / (sig1 + sig2 + sig));
  
}

double euclid(const LDMap &syms1, const LVec &syms2, const Tfidf &tfidf) {
  double sig = 0;

  for (auto s : syms2)
    if (syms1.find(s) == syms1.end())
      sig += sq(tfidf.get(s));
  for (const auto s : syms1)
    if (find(syms2.begin(), syms2.end(), s.first) == syms2.end())
      sig += sq(tfidf.get(s.first)) * sq(s.second);

  return (1 / (1 + sig));
}



class MePo : public Predictor {
  public:
    MePo(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num);

    void learn(long from, long to);

  protected:
    LDPairVec predict(const LVec& csyms, long maxth, long no_adv) const;

  private:
    Tfidf tfidf;
    const static int mepo_incr = 100;
    
};

MePo::MePo(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num)
: Predictor(deps, syms, sym_ths, sym_num), tfidf(sym_num) {
}

void MePo::learn(long from, long to) {
  for (unsigned i = from; i < to; ++i)
    tfidf.add(syms[i]);
}


LDPairVec MePo::predict(const LVec& csyms, long maxth, long no_adv) const {
  // theorem importance matrix
  LDPairVec ans = LDPairVec(maxth, make_pair(0, 0));
  for (long i = 0; i < maxth; ++i)
    ans[i].first = i;

  LDMap nsyms;
  for (auto s : csyms)
    nsyms[s] = 1.0;

  for (long sofar = 0; sofar < no_adv; sofar += mepo_incr) {
    for (long i = sofar; i < maxth; ++i)
      ans[i].second = cosine(nsyms, syms[ans[i].first], tfidf);

    long until = min(sofar + mepo_incr, no_adv);

    partial_sort(ans.begin() + sofar, ans.begin() + until, ans.begin() + maxth, sortfun);

    if (until >= maxth) return ans;

    for (long i = sofar; i < until; i++)
      for (auto s : syms[ans[i].first])
        nsyms[s] = max(nsyms[s], ans[i].second);
  }

  return ans;
}
