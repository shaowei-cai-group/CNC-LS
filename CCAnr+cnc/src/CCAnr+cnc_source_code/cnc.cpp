#include "cnc.hpp"
#include "basis.hpp"
#include "indusLS.hpp"
#include <assert.h>
#include <algorithm>
#include <cstdlib>
#include <iostream>
using std::rand;
using std::swap;
using std::cout;
using std::endl;

static inline bool with_prob(double p) {
	return (rand() % 10000000) * 0.0000001 < p;
}

static lit org_unitclause_queue[MAX_VARS];
static int org_unitclause_count;

static lit unitclause_queue[MAX_VARS];
static char sense_in_queue[MAX_VARS];
static int  unitclause_queue_beg_pointer, unitclause_queue_end_pointer;
static char clause_delete[MAX_CLAUSES];
static int cp_clause_lit_count[MAX_CLAUSES];
static lit clause_xor[MAX_CLAUSES];
static int fix_soln[MAX_VARS];

static int unassigned_var[MAX_VARS];
static int index_in_unassigned_var[MAX_VARS];
static int unassigned_count;

static int clause_delete_count;
static int conflict;

static float prob;

static void (* unit_propagation) ();
static bool (* choose_sense) (int);

double cnc_unit_last;

static long long cnc_slot_age; // reset on the beginning of the slot

static long long cnc_age;
static long long vage[MAX_VARS], vage_pos[MAX_VARS], vage_cnt[MAX_VARS];
static inline void vage_touch(int v, bool sense) {
	vage[v] = cnc_age * num_vars + unassigned_count;
	vage_pos[v] += sense;
	vage_cnt[v]++;
}



struct _canbest_s {
	int opt_unsat;
	int *soln;
};

static struct _canbest_s *canbest;
static int canbest_cap;
static int canbest_count = 0;
static int canbest_max_opt;

static void canbest_make_space(void) {
	if (canbest_count < canbest_cap)
		return;

	for (int i = canbest_count - 1; i >= 0; --i) {
		if (canbest[i].opt_unsat == canbest_max_opt) {
			swap(canbest[i], canbest[--canbest_count]);
			return;
		}
	}

	assert(0);
}

static void canbest_update_max_opt(void) {
	if (canbest_count < canbest_cap) {
		canbest_max_opt = num_clauses;
	} else {
		canbest_max_opt = 0;
		for (int i = 0; i < canbest_count; ++i)
			if (canbest_max_opt < canbest[i].opt_unsat)
				canbest_max_opt = canbest[i].opt_unsat;
	}
}

void cnc_init(int cb_cap) {
	for (int c = 0; c < num_clauses; ++c)
		if (1 == clause_lit_count[c])
			org_unitclause_queue[org_unitclause_count++] = clause_lit[c][0];

	canbest_cap = cb_cap;
	canbest = new _canbest_s[canbest_cap];
	for (int i = 0; i < canbest_cap; ++i)
		canbest[i].soln = new int[num_vars + 1];
	canbest_max_opt = num_clauses;
}

static inline void remove_unassigned_var(int var)
{
	int index, last_unassigned_var;

	last_unassigned_var = unassigned_var[--unassigned_count];
	index = index_in_unassigned_var[var];
	unassigned_var[index] = last_unassigned_var;
	index_in_unassigned_var[last_unassigned_var]=index;
}

static void assign(int var, bool sense)
{
	assert(var > 0 && var <= num_vars);
	assert(1 == sense || 0 == sense);

	int c;
	int i;
	lit cur;

	vage_touch(var, sense);

	fix_soln[var] = sense;

	remove_unassigned_var(var);

	for(i = 0; i<var_lit_count[var]; ++i)
	{
		cur = var_lit[var][i];
		c = cur.clause_num;

		if(clause_delete[c]==1) continue;

		if(cur.sense == sense)//then remove the clause from the formula (by marking it as deleted).
		{
			clause_delete[c]=1; clause_delete_count++;
		}
		else
		{
			if (cp_clause_lit_count[c]==1)//then it becomes an empty clause
			{
				clause_delete[c]=1;
				clause_delete_count++;
				conflict++;
				cp_clause_lit_count[c]=0;
			}
			else
			{
				--cp_clause_lit_count[c];
				clause_xor[c] ^= cur;

				if (cp_clause_lit_count[c]==1)//newly generated unit clause
				{
					lit tmplit = clause_xor[c];

					/*
					   { // Check if clause_xor is point to the only unit literal
					   bool found = false;
					   for(int j=0; j<clause_lit_count[c]; ++j) {
					// if fix_soln[v]==-2, v must be in unit queue
					// we won't reach here if the unit clause is being assigning
					if(fix_soln[clause_lit[c][j].var_num] < 0) {
					if (found || clause_xor[c] != clause_lit[c][j]) {
					cout << "error: xor value is invalid" << endl;
					abort();
					}
					found = true;
					}
					}
					if (!found) {
					cout << "error: xor value is point to unknown literal" << endl;
					abort();
					}
					}
					*/

					int tmpvar=tmplit.var_num;

					if (sense_in_queue[tmpvar] == -1)
					{
						unitclause_queue[unitclause_queue_end_pointer++] = tmplit;
						sense_in_queue[tmpvar] = tmplit.sense;
					}
					else
					{
						if (sense_in_queue[tmpvar]!=tmplit.sense)
						{
							fix_soln[tmpvar]=-2;//mark this var as a conflicting var
							//clause_delete[c]=1; clause_delete_count++;
						}
					}
				}

			}
		}
	}

}




void unit_propagation_order()
{
	lit uc_lit;
	int uc_var;
	bool uc_sense;

	//while (unitclause_queue_beg_pointer < unitclause_queue_end_pointer)
	//{

	uc_lit = unitclause_queue[unitclause_queue_beg_pointer++];

	uc_var = uc_lit.var_num;
	uc_sense = uc_lit.sense;

	if(fix_soln[uc_var]==0 || fix_soln[uc_var]==1) return;

	if (fix_soln[uc_var]==-2) {
		choose_sense(uc_var);
	}

	assign(uc_var, uc_sense);
	//}
}

void unit_propagation_random()
{
	lit uc_lit;
	int uc_var;
	bool uc_sense;
	int index;

	//while (unitclause_queue_beg_pointer < unitclause_queue_end_pointer)
	//{

	if(unitclause_queue_end_pointer==unitclause_queue_beg_pointer+1)
	{
		uc_lit = unitclause_queue[--unitclause_queue_end_pointer];
	}
	else{
		//index = unitclause_queue_beg_pointer+rand()%(unitclause_queue_end_pointer-unitclause_queue_beg_pointer);
		index = rand()%unitclause_queue_end_pointer;
		uc_lit = unitclause_queue[index];
		unitclause_queue[index] = unitclause_queue[--unitclause_queue_end_pointer];
	}

	//uc_lit = unitclause_queue[unitclause_queue_beg_pointer++];

	uc_var = uc_lit.var_num;
	uc_sense = uc_lit.sense;

	if(fix_soln[uc_var]==0 || fix_soln[uc_var]==1) return;

	if (fix_soln[uc_var]==-2) {
		uc_sense = choose_sense(uc_var);
	}

	assign(uc_var, uc_sense);
	//}
}



void unit_propagation_vers_order()
{
	lit uc_lit;
	int uc_var;
	bool uc_sense;

	//while (unitclause_queue_beg_pointer < unitclause_queue_end_pointer)
	//{

	uc_lit = unitclause_queue[--unitclause_queue_end_pointer];

	uc_var = uc_lit.var_num;
	uc_sense = uc_lit.sense;

	if(fix_soln[uc_var]==0 || fix_soln[uc_var]==1) return;

	if (fix_soln[uc_var]==-2) {
		choose_sense(uc_var);
	}

	assign(uc_var, uc_sense);
	//}
}

bool choose_greedy_sense0(int var)
{

	if(score1[var]>score0[var]) return 1;
	else if(score0[var]>score1[var]) return 0;
	else return rand()%2;
}

//greedy
bool choose_greedy_sense(int var)
{
	int i,c;
	lit cur;

	int count1=0, count0=0;

	for(i = 0; i<var_lit_count[var]; ++i)
	{
		cur = var_lit[var][i];
		c = cur.clause_num;

		if(clause_delete[c]==1) continue;

		if(cur.sense == 1)
			count1++;
		else
			count0++;
	}

	if(count1>count0) return 1;
	else if(count1<count0) return 0;
	else return rand()%2;
}

//weighted greedy
bool choose_greedy_sense2(int var)
{
	int i,c;
	lit cur;

	int count1=0, count0=0;
	int large_number=100;

	for(i = 0; i<var_lit_count[var]; ++i)
	{
		cur = var_lit[var][i];
		c = cur.clause_num;

		if(clause_delete[c]==1) continue;

		if(cur.sense == 1)
			count1 += large_number/cp_clause_lit_count[c];
		//count1++;
		else
			count0 += large_number/cp_clause_lit_count[c];
		//count0++;
	}

	if(count1>count0) return 1;
	else if(count1<count0) return 0;
	else return rand()%2;
}


//random
bool choose_random_sense(int var)
{
	(void) var;
	return rand()%2;
}



bool choose_sense_prob0(int var)
{
	if (with_prob(prob))
		return choose_random_sense(var);
	else return choose_greedy_sense0(var);

}

bool choose_sense_prob(int var)
{
	if (with_prob(prob))
		return choose_random_sense(var);
	else return choose_greedy_sense(var);

}


bool choose_sense_prob2(int var)
{
	if (with_prob(prob))
		return choose_random_sense(var);
	else return choose_greedy_sense2(var);

}

int vage_window;
void unit_propagation_age()
{
	lit uc_lit;
	int uc_var;
	bool uc_sense;

	// don't go through all var in queue, its too slow.
	const int unitlen = unitclause_queue_end_pointer - unitclause_queue_beg_pointer;
	int besti = (rand() % unitlen) + unitclause_queue_beg_pointer;
	for (int j = 0; j < vage_window; j++) {
		int i = (rand() % unitlen) + unitclause_queue_beg_pointer;
		if (vage[unitclause_queue[i].var_num] < vage[unitclause_queue[besti].var_num]) {
			besti = i;
		}
	}

	uc_lit = unitclause_queue[besti];
	uc_var = uc_lit.var_num;
	uc_sense = uc_lit.sense;

	unitclause_queue[besti] = unitclause_queue[--unitclause_queue_end_pointer];

	if(fix_soln[uc_var]==0 || fix_soln[uc_var]==1) return;

	if (fix_soln[uc_var]==-2) {
		uc_sense = choose_sense(uc_var);
	}

	assign(uc_var, uc_sense);
}

double lb_last_prob;
static bool choose_sense_lb(int var) {
	if (with_prob(lb_last_prob))
		return lb_get_last(var);
	else
		return lb_get_prob(var);
}

static void set_functions(void)
{
	// int rand_res = rand() % 3;
	// if (0 == rand_res) unit_propagation = unit_propagation_order; //ord
	// else if (1 == rand_res) unit_propagation = unit_propagation_vers_order;//ver
	// else unit_propagation = unit_propagation_random;//random

	// Rand can take 1% lower wrong ratio than others
	//unit_propagation = unit_propagation_order;
	//unit_propagation = unit_propagation_vers_order;
	//unit_propagation = unit_propagation_random;
	unit_propagation = unit_propagation_age;


	//choose_sense = choose_greedy_sense;
	//choose_sense = choose_greedy_sense2;
	//choose_sense = choose_random_sense;
	choose_sense = choose_sense_lb;

}

static void cnc_process_one(void)
{
	int 	as_var;
	bool 	as_sense;

	int 	c,v,i;

	++cnc_slot_age;
	++cnc_age;
	set_functions();

	for (i=0; i<num_vars; ++i)
	{
		v=i+1;
		unassigned_var[i]=v;
		index_in_unassigned_var[v]=i;

		fix_soln[v]=-1;
		sense_in_queue[v]=-1;
	}
	unassigned_count = num_vars;

	for (c = 0; c < num_clauses; c++)
	{
		cp_clause_lit_count[c] = clause_lit_count[c];
		clause_delete[c]=0;
		clause_xor[c] = clause_xor_org[c];
	}

	clause_delete_count=0;
	conflict=0;


	unitclause_queue_beg_pointer=0;
	unitclause_queue_end_pointer=0;
	for(i = 0; i<org_unitclause_count; ++i)
	{
		lit tmplit = org_unitclause_queue[i];
		int tmpvar = tmplit.var_num;

		if (sense_in_queue[tmpvar] == -1)
		{
			sense_in_queue[tmpvar] = tmplit.sense;
			unitclause_queue[unitclause_queue_end_pointer++] = tmplit;
		}
		else
		{
			if (sense_in_queue[tmpvar]!=tmplit.sense)
				fix_soln[tmpvar]=-2;//mark this var as conflicting
		}
	}

	/*
	if (tries > 1 && with_prob(cnc_unit_last)) {
		int var;
		for (int i = 0; i < unitclause_queue_end_pointer; ++i) {
			if (unitclause_queue[i].sense != lb_get_last(unitclause_queue[i].var_num)) {
				unitclause_queue[i].sense = 1 - unitclause_queue[i].sense;
				var = unitclause_queue[i].var_num;
				sense_in_queue[var] = unitclause_queue[i].sense;
				assert(unitclause_queue[i].sense == lb_get_last(unitclause_queue[i].var_num));
			}
		}
	}
	*/



	while (unassigned_count>0)
	{
		if (clause_delete_count==num_clauses)
		{
			for (int i=0; i<unassigned_count; ++i)
				fix_soln[unassigned_var[i]]=rand()%2;

			unassigned_count=0;

			break;
		}

		if (unitclause_queue_beg_pointer < unitclause_queue_end_pointer)
		{
			unit_propagation();
		}
		else {
			as_var = unassigned_var[rand()%unassigned_count];
			as_sense = choose_sense(as_var);
			assign(as_var, as_sense);
		}

		if (conflict >= canbest_max_opt) break;
	}

	if (conflict < canbest_max_opt) {
		if (the_best.opt_try != tries && conflict < the_best.opt_unsat) {
			// Best solution has been searched by LS, or init
			update_best_soln(conflict, fix_soln, 1);
			//cout << "c CNC_UPDATE_AT\t" << cnc_slot_age << "\t" << cnc_age << "\t" << tries << endl;
		} else if (the_best.opt_try == tries && conflict < the_best.opt_unsat) {
			// We have updated the best soln in this time slot
			// We found a better soln than the_best, and this the_best has not been searched by LS.
			// So move the_best to canbest, and update the_best by this new soln
			canbest_make_space();
			swap(the_best.soln, canbest[canbest_count].soln);
			canbest[canbest_count].opt_unsat = the_best.opt_unsat;
			canbest_count++;

			update_best_soln(conflict, fix_soln, 1);
			//cout << "c CNC_UPDATE_AT\t" << cnc_slot_age << "\t" << cnc_age << "\t" << tries << endl;
		} else {
			canbest_make_space();
			canbest[canbest_count].opt_unsat = conflict;
			for (int v = 1; v <= num_vars; ++v)
				canbest[canbest_count].soln[v] = fix_soln[v];
			canbest_count++;
		}

		canbest_update_max_opt();
	}
}

bool cnc_get_canbest(const int* &soln, int &opt) {
	if (0 == canbest_count)
		return false;

	opt = canbest[0].opt_unsat;
	int pos = 0;
	for (int i = 1; i < canbest_count; ++i) {
		if (opt > canbest[i].opt_unsat) {
			opt = canbest[i].opt_unsat;
			pos = i;
		}
	}
	soln = canbest[pos].soln;
	swap(canbest[pos], canbest[--canbest_count]);
	canbest_update_max_opt();

	return true;
}

void cnc_process(long long step_num) {
	cnc_slot_age = 0;

	++step_num;
	while (--step_num) {
		cnc_process_one();
	}
}
