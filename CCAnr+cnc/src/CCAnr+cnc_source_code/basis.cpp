#include "basis.hpp"
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>
#include <sys/times.h> //these two h files are for linux
#include <unistd.h>
#include "cnc.hpp" // cnc_unit_last

using namespace std;


int cutoff_time;

bool shouldPrint = false;

/*parameters of the instance*/
int num_vars;
int num_clauses;

/* literal arrays */
lit* var_lit[MAX_VARS];
int	 var_lit_count[MAX_VARS];
lit* clause_lit[MAX_CLAUSES];
int	 clause_lit_count[MAX_CLAUSES];

lit clause_xor_org[MAX_CLAUSES];

int score1[MAX_VARS];
int score0[MAX_VARS];

int tries;
struct _the_best_s the_best;

static struct tms start;
double get_runtime(void) {
	struct tms stop;
	times(&stop);
	return (double) (stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
}
void record_runtime(void) {
	times(&start);
}



/*
 * Read in the problem.
 */
int build_instance(const char *filename)
{
	char *line = new char[1000000];
	int  *temp_lit = new int[MAX_VARS];
	char    tempstr1[10];
	char    tempstr2[10];


	int     cur_lit;
	int     i;
	int		v,c;//var, clause

	ifstream infile(filename);
	if(!infile)
		return 0;


	/*** build problem data structures of the instance ***/
	infile.getline(line,1000000);
	while (line[0] != 'p')
		infile.getline(line,1000000);


	sscanf(line, "%s %s %d %d", tempstr1, tempstr2, &num_vars, &num_clauses);

	//cout << num_vars << '\t' << num_clauses << "\n";

	if(num_vars>=MAX_VARS || num_clauses>=MAX_CLAUSES)
	{
		//cout<<"c the size of instance exceeds out limitation, please enlarge MAX_VARS and (or) MAX_CLAUSES."<<endl;
		exit(1);
	}

	for (c = 0; c < num_clauses; c++)
	{
		clause_lit_count[c] = 0;
		clause_lit[c]=NULL;
	}


	for (v=1; v<=num_vars; ++v)
	{
		var_lit_count[v] = 0;
		var_lit[v]=NULL;
	}


	//Now, read the clauses, one at a time.
	int lit_redundent, clause_redundent;
	int redundent_clause_count = 0;
	for (c = 0; c < num_clauses; )
	{
		clause_redundent = 0;
		clause_lit_count[c] = 0;

		infile>>cur_lit;
		while (cur_lit != 0) {
			lit_redundent = 0;
			for(int p = 0; p < clause_lit_count[c]; p++)
			{
				if(cur_lit == temp_lit[p]){
					//cout << "c " << filename << ": WARNING! literal " << cur_lit << " redundent in clause " << c + redundent_clause_count << endl;
					lit_redundent = 1;
					break;
				}
				else if(cur_lit == -temp_lit[p]){
					//cout << "c " << filename << ": WARNING! conflict variable " << abs(cur_lit) << " detected in the clause " << c + redundent_clause_count << endl;
					clause_redundent = 1;
					break;
				}
			}

			if(lit_redundent == 0)
			{
				temp_lit[clause_lit_count[c]] = cur_lit;
				clause_lit_count[c]++;
			}

			infile>>cur_lit;
		}

		if(clause_redundent == 0)
		{
			clause_lit[c] = new lit[clause_lit_count[c]+1];

			clause_xor_org[c].reset();
			for(i=0; i<clause_lit_count[c]; ++i)
			{

				clause_lit[c][i].clause_num = c;
				clause_lit[c][i].var_num = abs(temp_lit[i]);
				if (temp_lit[i] > 0) clause_lit[c][i].sense = 1;
				else clause_lit[c][i].sense = 0;

				clause_xor_org[c] ^= clause_lit[c][i];

				var_lit_count[clause_lit[c][i].var_num]++;
			}
			clause_lit[c][i].var_num=0;
			clause_lit[c][i].clause_num = -1;

			c++;
		}
		else
		{
			num_clauses--;
			clause_lit_count[c] = 0;
			redundent_clause_count++;
		}
	}


	//creat var literal arrays
	for (v=1; v<=num_vars; ++v)
	{
		var_lit[v] = new lit[var_lit_count[v] + 1];
		var_lit_count[v] = 0;	//reset to 0, for build up the array
	}

	
	//scan all clauses to build up var literal arrays
	for (c = 0; c < num_clauses; ++c)
	{
		for(i=0; i<clause_lit_count[c]; ++i)
		{
			v = clause_lit[c][i].var_num;
			var_lit[v][var_lit_count[v]] = clause_lit[c][i];
			++var_lit_count[v];

			if(clause_lit[c][i].sense==1) score1[v]++;
			else score0[v]++;
		}
	}

	for (v=1; v<=num_vars; ++v) //set boundary
		var_lit[v][var_lit_count[v]].clause_num=-1;

	the_best.soln      = new int[num_vars + 1];
	the_best.opt_unsat = num_clauses;
	the_best.opt_time  = -1;
	the_best.opt_try   = 0;
	the_best.source    = 0;


	delete [] temp_lit;
	delete [] line;
	
	return 1;
}

void update_best_soln(const int opt, const int *soln, const int source) {
	for(int v = 1; v <= num_vars; v++)
		the_best.soln[v] = soln[v];

	//if (!shouldPrint)
	//	cout << "o " << opt << endl;

	the_best.opt_unsat = opt;
	the_best.opt_time = get_runtime();
	the_best.opt_try = tries;
	the_best.source = source;

	//cout << "c optInfo\t" << opt << "\t" << the_best.opt_time << "\t" << tries << "\t" << source << endl;
}


void update_best_value(const int opt) {
	
	//if (!shouldPrint)
	//	cout << "o " << opt << endl;

	the_best.opt_unsat = opt;
	
}


void print_best_solution(void) {
	//cout << "c SOLN_BEGIN\t" << get_runtime() << endl;;
	cout << "v";
	for (int i = 1; i <= num_vars; i++) {
		cout << " " << i * ((the_best.soln[i] << 1) - 1);
	}
	cout << endl;
	//cout << "c SOLN_END\t" << get_runtime() << endl;
	cout << flush;
}

bool verify_sol(void) {
	int c, j;
	int flag;


	for (c = 0; c < num_clauses; ++c) {
		flag = 0;
		for(j = 0; j < clause_lit_count[c]; ++j) {
			if (the_best.soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {
				flag = 1;
				break;
			}
		}

		if(flag ==0){

			cout<<"c Error: the assignment is not a solution."<<endl;
			return false;
		}
	}
	
	return true;

	/*if (verify_unsat == the_best.opt_unsat) {
		return 1;
	} else {
		cout << "c ERROR: find opt=" << the_best.opt_unsat << ", but verified opt=" << verify_unsat << endl;
		cout << "o " << verify_unsat << endl;
		the_best.opt_unsat = verify_unsat;
		return 0;
	}*/
}

