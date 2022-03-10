#include "knn.cpp"
#include "mepo.cpp"
#include "nbayes.cpp"
#include "rforest.cpp"
#include "library/predict/predict.h"

predictor::predictor(
        predictor_type type,
        std::vector<std::vector<long>> const & dependencies,
        std::vector<std::vector<long>> const & symbols) {
    std::vector<std::vector<long>> symThms;
    for (size_t i = 0; i < symbols.size(); i++) {
        for (long sym : symbols[i]) {
            if (static_cast<size_t>(sym) >= symThms.size()) {
                symThms.resize(sym+1);
            }
            symThms[sym].push_back(i);
        }
    }
    m_num_thm = symbols.size();
    long symNum = symThms.size();
    switch (type) {
        case predictor_type::MEPO:
            m_predictor.reset(new MePo(dependencies, symbols, symThms, symNum));
            break;
        case predictor_type::BAYES:
            m_predictor.reset(new NaiveBayes(dependencies, symbols, symThms, symNum));
            break;
        case predictor_type::KNN:
        default:
            m_predictor.reset(new kNN(dependencies, symbols, symThms, symNum));
            break;
    }
}

predictor::~predictor() {}

void predictor::learn_until(long thm_idx) {
    m_predictor->learn(0, thm_idx);
}

std::vector<std::pair<long, double>> predictor::predict(std::vector<long> symbols, long num_results, long until_thm) {
    auto res = m_predictor->predict(symbols, until_thm, std::min(m_num_thm, num_results));
    if (res.size() > static_cast<size_t>(num_results)) {
        res.resize(num_results);
    }
    return res;
}