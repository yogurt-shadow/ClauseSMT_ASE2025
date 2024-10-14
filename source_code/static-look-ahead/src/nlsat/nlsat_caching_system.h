#pragma once

#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_interval_set.h"

namespace nlsat {
    class nlsat_caching_system {
    public:
        struct imp;
    private:
        imp   *m_imp;
    
    public:
        nlsat_caching_system(solver& ,interval_set_manager &ism, pmanager &pm, atom_vector const &_atoms, clause_vector const &_clauses);
        ~nlsat_caching_system();
        void init();
        void init_vars(unsigned);
        bool is_atom_enabled(bool_var) const;
        void disable_atom(bool_var);
        interval_set* get_atom_set(bool_var) const;
        void cache_atom_set(bool_var, interval_set *);
        void register_atom(bool_var);
        void disable_second_var_atoms(var);
        void delete_atom(bool_var);
    };
};