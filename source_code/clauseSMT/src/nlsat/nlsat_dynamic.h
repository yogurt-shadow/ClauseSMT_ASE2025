#pragma once

#include "nlsat/nlsat_advanced_types.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_evaluator.h"
#include "nlsat/nlsat_solver.h"

/**
 * @brief Dynamic Manager for nlsat
 */

// #define _DTRACE

#ifdef _DTRACE
    #define DTRACE(CODE) { CODE } ((void) 0)
    #define DCTRACE(COND, CODE) if(COND) { CODE } ((void) 0)
#else
    #define DTRACE(CODE) ((void) 0)
    #define DCTRACE(COND, CODE) ((void) 0)
#endif

namespace nlsat {
    /**
     * Branching Heuristic for Dynamic Nlsat
     * * 1. ORIGIN_STATIC_BOOL_FIRST_MODE
     * ~ bool first, theory next, static order
     * * 2. BOOL_FIRST_VSIDS
     * ~ bool first, theory next, vsids order
     * * 3. THEORY_FIRST_VSIDS
     * ~ theory first, bool next, vsids order
     * * 4. UNIFORM_VSIDS
     * ~ bool and theory vsids order
     * * 5. RANDOM_ORDER
     * ~ random pick next bool/theory var
    */
    #define                                                 UNIFORM_VSIDS                          1
    #define                                                 BOOL_FIRST_VSIDS                       2
    #define                                                 THEORY_FIRST_VSIDS                     3
    #define                                                 ORIGIN_STATIC_BOOL_FIRST_MODE          4
    #define                                                 RANDOM_MODE                            5

    // * choose dynamic order
    #define DYNAMIC_MODE                                    UNIFORM_VSIDS

    /**
     * ^ BOOL: search bool var
     * ^ ARITH: search arith var
     * ^ INIT: search begin
     * ^ FINISH: search finish
     * ^ switch: search from arith to bool, new stage
    */
    enum search_mode {
        BOOL, ARITH, INIT, FINISH, SWITCH
    };

    /**
     * @brief manager of dynamic nlsat
    */
    class Dynamic_manager {
    public:
        struct imp;
    private:
        imp * m_imp;
    public:
        Dynamic_manager(nlsat_clause_vector & nlsat_clauses, nlsat_atom_vector & nlsat_atoms, anum_manager & am, pmanager & pm, assignment & ass, evaluator & eva, interval_set_manager & ism, svector<lbool> const & bvalues, bool_var_vector const & pure_bool_vars, bool_var_vector const & pure_bool_convert, solver & s, clause_vector const & clauses, clause_vector & learned, 
        atom_vector const & atoms, unsigned & restart, unsigned & deleted, unsigned rand_seed);
        ~Dynamic_manager();

        // set number of arith vars
        void set_arith_num(unsigned x);
        // initialize search
        void init_search();

        void init_learnt_management();
        void update_learnt_management();
        void init_nof_conflicts();
        void minimize_learned();

        void reset_curr_conflicts();
        void inc_curr_conflicts();
        void reset_curr_literal_assign();
        void inc_curr_literal_assign();
        bool check_restart_requirement();

        hybrid_var get_last_assigned_hybrid_var(bool & is_bool) const;
        var get_last_assigned_arith_var() const;
        bool_var get_last_assigned_bool_var() const;
        bool last_assigned_bool() const;
        unsigned assigned_size() const;
        unsigned assigned_arith_size() const;
        unsigned assigned_bool_size() const;

        // is_bool: push bool var or arith var
        // for bool var: push pure bool index
        // for airth var: push arith index
        void push_assigned_var(hybrid_var x, bool is_bool);
        

        hybrid_var get_stage_var(stage_var x) const;
        void pop_last_var();

        var heap_select(bool & is_bool);
        void bump_conflict_hybrid_vars();
        void bump_conflict_literals();

        void hybrid_decay_act();
        void literal_decay_act();

        double get_literal_activity(literal l);

        // for bool var: atom index
        void do_watched_clauses(hybrid_var x, bool is_bool);
        // for bool var: atom index
        void undo_watched_clauses(hybrid_var x, bool is_bool);

        void find_next_process_clauses(var x, bool_var b, clause_vector & clauses, search_mode m_search_mode);

        void del_bool(bool_var b);
        void del_clauses();
        void register_atom(atom * a);

        void clause_bump_act(clause & cls);
        void clause_decay_act();

        void reset_conflict_vars();
        void reset_conflict_literals();
        void insert_conflict_from_bool(bool_var b);
        void insert_conflict_from_literals(unsigned sz, literal const * ls);
        void insert_conflict_literal(literal l);
        void insert_conflict_literals(unsigned sz, literal const * ls);

        var find_stage(hybrid_var x, bool is_bool) const;
        var max_stage_literal(literal l) const;
        var max_stage_lts(unsigned sz, literal const * cls) const;
        bool all_assigned_bool_arith(bool_var b) const;
        bool same_stage_bool(bool_var b, stage_var x) const;
        bool same_stage_literal(literal l, stage_var x) const;
        var max_stage_var(atom const * a) const;
        var max_stage_poly(poly const * p) const;
        var max_stage_var_poly(poly const * p) const;
        var max_stage_or_unassigned_ps(polynomial_ref_vector const & ps) const;
        var max_stage_or_unassigned_literals(unsigned num, literal const * ls) const;
        var max_stage_or_unassigned_atom(atom const * a) const;
        
        hybrid_var max_assigned_var(unsigned sz, literal const * ls, bool & is_bool, stage_var & max_stage) const;

        var all_assigned_or_left_literal(bool_var b) const;
        void erase_from_heap(hybrid_var v, bool is_bool);
        bool finish_status() const;

        bool_var get_unit_bool_var() const;

        std::ostream & display_assigned_vars(std::ostream & out) const;
        std::ostream & display_var_stage(std::ostream &) const;
        std::ostream & display_hybrid_activity(std::ostream &) const;
        std::ostream & display_literal_activity(std::ostream &);
    };
};