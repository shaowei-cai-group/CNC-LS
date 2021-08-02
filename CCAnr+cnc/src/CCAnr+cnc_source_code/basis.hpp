#ifndef _BASIS_H_
#define _BASIS_H_

/* limits on the size of the problem. */
#define MAX_VARS    5000010
#define MAX_CLAUSES 20000000

extern bool shouldPrint;

// Define a data structure for a literal in the SAT problem.
struct lit {
	unsigned char sense:1;	//is 1 for true literals, 0 for false literals.
	int clause_num:31;		//clause num, begin with 0
	int var_num;			//variable num, begin with 1

	struct lit& operator^=(const struct lit &l) {
		sense ^= l.sense;
		clause_num ^= l.clause_num;
		var_num ^= l.var_num;
		return *this;
	}

	void reset(void) {
		sense = 0;
		clause_num = 0;
		var_num = 0;
	}

	bool operator==(const struct lit &l) const {
		return sense == l.sense && clause_num == l.clause_num && var_num == l.var_num;
	}

	bool operator!=(const struct lit &l) const {
		return !(*this == l);
	}
};

/*parameters of the instance*/
extern int num_vars;	//var index from 1 to num_vars
extern int num_clauses;	//clause index from 0 to num_clauses-1

/* literal arrays */
extern lit*	var_lit[MAX_VARS];				//var_lit[i][j] means the j'th literal of var i.
extern int  var_lit_count[MAX_VARS];        //amount of literals of each var
extern lit* clause_lit[MAX_CLAUSES];		//clause_lit[i][j] means the j'th literal of clause i.
extern int  clause_lit_count[MAX_CLAUSES]; 	// amount of literals in each clause

// Used by CNC, but since it is hard to update, just put it here...
extern lit clause_xor_org[MAX_CLAUSES];

extern int score1[MAX_VARS];
extern int score0[MAX_VARS];

extern int tries;
extern int cutoff_time;

struct _the_best_s {
	int *soln;
	int opt_unsat;
	double opt_time;
	int opt_try;
	int source;
};
extern struct _the_best_s the_best;

int build_instance(const char *filename);
void print_best_solution(void);
void update_best_soln(const int opt, const int *soln, const int source);
void update_best_value(const int opt);

bool verify_sol(void);

void record_runtime(void);
double get_runtime(void);

#endif
