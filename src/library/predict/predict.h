#include <memory>
#include <vector>

class Predictor;

enum class predictor_type {
    KNN,
    MEPO,
    BAYES,
};

struct predictor {
    std::unique_ptr<Predictor> m_predictor;
    long m_num_thm;

    predictor(
        predictor_type type,
        std::vector<std::vector<long>> const & dependencies,
        std::vector<std::vector<long>> const & symbols);
    virtual ~predictor();

    void learn_until(long thm_idx);
    void learn_all() { learn_until(m_num_thm); }

    std::vector<std::pair<long, double>> predict(std::vector<long> symbols, long num_results, long until_thm);

    std::vector<std::pair<long, double>> predict(std::vector<long> symbols, long num_results) {
        return predict(symbols, num_results, m_num_thm);
    }
};

