#include "nlsat/nlsat_caching_system.h"
#include "nlsat/nlsat_solver.h"

namespace nlsat {
    struct nlsat_caching_system::imp {
        interval_set_manager &        m_ism;
        atom_vector            const &m_atoms;
        clause_vector          const &m_clauses;
        unsigned                      num_vars;

        interval_set_vector    m_atom_caching_set;
        pmanager               & m_pm;
        bool_vector            m_atom_caching_enabled;
        // var -> atom
        vector<var_vector>     m_second_var_atoms;
        // atom -> vars
        vector<var_vector>     m_atom_vars;
        solver                  & m_solver;

        imp(solver & s, interval_set_manager & ism, pmanager & pm, atom_vector const &ats, clause_vector const &cls): m_ism(ism), m_pm(pm), m_atoms(ats), m_clauses(cls) , m_solver(s)
        {
            // std::cout << "init imp done" << std::endl;
        }

        void clear() {
            m_atom_caching_enabled.clear();
            m_atom_caching_set.clear();
            m_atom_caching_enabled.resize(m_atoms.size(), false);
            m_atom_caching_set.resize(m_atoms.size(), nullptr);
            m_second_var_atoms.clear();
            m_second_var_atoms.resize(num_vars, var_vector());
            m_atom_vars.clear();
            collect_var_atoms();
        }

        void init_vars(unsigned x) {
            num_vars = x;
        }

        void collect_atom_vars(atom const *a, var_vector &vec, var &second_var) {
            second_var = null_var;
            vec.clear();
            if(a == nullptr) {
                return;
            }
            if(a->is_root_atom()) {
                m_pm.vars(to_root_atom(a)->p(), vec);
                if(!vec.contains(to_root_atom(a)->x())) {
                    vec.push_back(to_root_atom(a)->x());
                }
            } else {
                for(unsigned j = 0; j < to_ineq_atom(a)->size(); j++) {
                    var_vector vec2;
                    m_pm.vars(to_ineq_atom(a)->p(j), vec2);
                    for(var v: vec2) {
                        if(!vec.contains(v)) {
                            vec.push_back(v);
                        }
                    }
                }
            }
            if(vec.size() <= 1) {
                return;
            }
            var first_var = std::max(vec[0], vec[1]);
            second_var = std::min(vec[0], vec[1]);
            for(unsigned i = 2; i < vec.size(); i++) {
                if(vec[i] > first_var) {
                    second_var = first_var;
                    first_var = vec[i];
                } else if(vec[i] > second_var) {
                    second_var = vec[i];
                }
            }
        }

        void collect_var_atoms() {
            m_second_var_atoms.resize(num_vars);
            m_atom_vars.resize(m_atoms.size());
            for (unsigned i = 0; i < m_atoms.size(); ++i) {
                atom * a = m_atoms[i];
                var_vector vec;
                var second_var;
                collect_atom_vars(a, vec, second_var);
                m_atom_vars[i] = vec;
                if(second_var != null_var) {
                    m_second_var_atoms[second_var].push_back(i);
                }
            }
        }

        void disable_second_var_atoms(var v) {
            // DTRACE(std::cout << "disable second var " << v << std::endl;);
            for (unsigned i = 0; i < m_second_var_atoms[v].size(); ++i) {
                disable_atom(m_second_var_atoms[v][i]);
            }
        }

        void cache_atom_set(bool_var b, interval_set *s) {
            m_atom_caching_enabled[b] = true;
            m_ism.dec_ref(m_atom_caching_set[b]);
            m_ism.inc_ref(s);
            m_atom_caching_set[b] = s;
        }

        void disable_atom(bool_var b) {
            // DTRACE(std::cout << "disable atom " << b << std::endl;);
            enlarge_atom(b);
            m_atom_caching_enabled[b] = false;
        }

        bool is_atom_enabled(bool_var b) const {
            return b >= m_atom_caching_enabled.size() ? false : m_atom_caching_enabled[b];
            // return false;
        }

        void delete_atom(bool_var b) {
            disable_atom(b);
        }

        interval_set * get_atom_set(bool_var b) const {
            return b >= m_atom_caching_set.size() ? nullptr : m_atom_caching_set[b];
        }

        void enlarge_atom(bool_var b) {
            while (m_atom_caching_set.size() <= b) {
                m_atom_caching_set.push_back(nullptr);
                m_atom_caching_enabled.push_back(false);
                m_atom_vars.push_back(var_vector());
            }
        }

        void register_atom(bool_var b) {
            // DTRACE(std::cout << "register atom " << b << std::endl;
            //     m_solver.display(std::cout, b) << std::endl;
            // );
            enlarge_atom(b);
            var_vector vec;
            var second_var;
            collect_atom_vars(m_atoms[b], vec, second_var);
            m_atom_vars[b] = vec;
            if(second_var != null_var) {
                DTRACE(std::cout << "second var is " << second_var << std::endl;);
                m_second_var_atoms[second_var].push_back(b);
            }
            // DTRACE(std::cout << "done register atom " << b << std::endl;);
        }

        ~imp() {}
    };

    nlsat_caching_system::nlsat_caching_system(solver &s, interval_set_manager &ism, pmanager &pm, atom_vector const &as, clause_vector const &cs) {
        m_imp = new imp(s, ism, pm, as, cs);
    }

    nlsat_caching_system::~nlsat_caching_system() {
        dealloc(m_imp);
    }

    void nlsat_caching_system::init() {
        m_imp->clear();
    }

    bool nlsat_caching_system::is_atom_enabled(bool_var b) const {
        return m_imp->is_atom_enabled(b);
    }

    void nlsat_caching_system::disable_atom(bool_var b) {
        m_imp->disable_atom(b);
    }

    interval_set * nlsat_caching_system::get_atom_set(bool_var b) const {
        return m_imp->get_atom_set(b);
    }

    void nlsat_caching_system::cache_atom_set(bool_var b, interval_set * s) {
        m_imp->cache_atom_set(b, s);
    }

    void nlsat_caching_system::register_atom(bool_var b) {
        m_imp->register_atom(b);
    }

    void nlsat_caching_system::init_vars(unsigned x) {
        m_imp->init_vars(x);
    }

    void nlsat_caching_system::disable_second_var_atoms(var v) {
        m_imp->disable_second_var_atoms(v);
    }

    void nlsat_caching_system::delete_atom(bool_var b) {
        m_imp->delete_atom(b);
    }
};