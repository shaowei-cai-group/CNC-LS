#include "basis.hpp"
#include <cerrno>
#include <cstdlib>
#include <iostream>
#include <assert.h>

using namespace std;

#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item

#define sigscore	ave_weight   //significant score needed for aspiration

/* Information about the variables. */
static int score[MAX_VARS];
static int conf_change[MAX_VARS];
static long long time_stamp[MAX_VARS];

static int* var_neighbor[MAX_VARS];

/* Information about the clauses */
static int clause_weight[MAX_CLAUSES];
static int sat_count[MAX_CLAUSES];
static int sat_var[MAX_CLAUSES];

//unsat clauses stack
static int unsat_stack[MAX_CLAUSES];		//store the unsat clause number
static int unsat_stack_fill_pointer;  // NEED TO UPDATE IN RESTART PROCEDURE
static int index_in_unsat_stack[MAX_CLAUSES];//which position is a clause in the unsat_stack

//variables in unsat clauses
static int unsatvar_stack[MAX_VARS];
static int unsatvar_stack_fill_pointer;  // NEED TO UPDATE IN RESTART PROCEDURE
static int index_in_unsatvar_stack[MAX_VARS];
static int unsat_app_count[MAX_VARS];		//a varible appears in how many unsat clauses

//configuration changed decreasing variables (score>0 and confchange=1)
static int goodvar_stack[MAX_VARS];
static int goodvar_stack_fill_pointer;  // NEED TO UPDATE IN RESTART PROCEDURE
static int already_in_goodvar_stack[MAX_VARS];

/* Information about solution */
static int cur_soln[MAX_VARS];	//the current solution, with 1's for True variables, and 0's for False variables

//cutoff
static long long step; // LS私有step，每次init之后置为零

int balancePar;

bool aspiration_active;




// local search local best
// which is the best soln in this time slot
static int lb_soln[MAX_VARS];
static int lb_opt;
static void lb_copy(void) {
	for (int v = 1; v <= num_vars; v++)
		lb_soln[v] = cur_soln[v];
}
static int lb_pos[MAX_VARS], lb_neg[MAX_VARS];
static void lb_update(int mut) {
	for (int v = 1; v <= num_vars; v++) {
		assert(0 == lb_soln[v] || 1 == lb_soln[v]);
		lb_pos[v] += lb_soln[v] * mut;
		lb_neg[v] += !lb_soln[v] * mut;
	}
}
bool lb_get_prob(int v) {
	int sum = lb_pos[v] + lb_neg[v];
	if (0 == sum) {
		//return lb_soln[v];
		return rand() & 1;
	} else {
		return (rand() % sum) < lb_pos[v];
	}
}
bool lb_get_last(int v) {
	if (lb_neg[v] + lb_pos[v])
		return lb_soln[v];
	else
		return rand() & 1;
}




void build_neighbor_relation(void)
{
	int *neighbor_flag = new int[MAX_VARS];
	int *temp_neighbor = new int[MAX_VARS];

	int temp_neighbor_count;
	int	i,j,count;
	int v,c,n;

	for(v=1; v<=num_vars; ++v)
	{
		//if(fix[v]==1) continue;

		neighbor_flag[v] = 1;
		temp_neighbor_count = 0;

		for(i=0; i<var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			//if(clause_delete[c]==1) continue;

			for(j=0; j<clause_lit_count[c]; ++j)
			{
				n=clause_lit[c][j].var_num;
				if(neighbor_flag[n]!=1)
				{
					neighbor_flag[n] = 1;
					temp_neighbor[temp_neighbor_count++] = n;
				}
			}
		}

		neighbor_flag[v] = 0;

		var_neighbor[v] = new int[temp_neighbor_count+1];

		count = 0;
		for(i=0; i<temp_neighbor_count; i++)
		{
			var_neighbor[v][count++] = temp_neighbor[i];
			neighbor_flag[temp_neighbor[i]] = 0;
		}

		var_neighbor[v][count]=0;
	}

	delete [] neighbor_flag;
	delete [] temp_neighbor;
}

static inline void ls_update_best_soln(void) {
	update_best_soln(unsat_stack_fill_pointer, cur_soln, 2);
	//cout << "c LS_UPDATE_AT\t" << step << "\t" << tries << endl;
}

static inline void unsat(int clause)
{
	index_in_unsat_stack[clause] = unsat_stack_fill_pointer;
	push(clause,unsat_stack);

	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v;
	for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
	{
		unsat_app_count[v]++;
		if(unsat_app_count[v]==1)
		{
			index_in_unsatvar_stack[v] = unsatvar_stack_fill_pointer;
			push(v,unsatvar_stack);
		}
	}
}

static inline void sat(int clause)
{
	int index,last_unsat_clause;

	//since the clause is satisfied, its position can be reused to store the last_unsat_clause
	last_unsat_clause = pop(unsat_stack);
	index = index_in_unsat_stack[clause];
	unsat_stack[index] = last_unsat_clause;
	index_in_unsat_stack[last_unsat_clause] = index;

	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v,last_unsat_var;
	for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
	{
		unsat_app_count[v]--;
		if(unsat_app_count[v]==0)
		{
			last_unsat_var = pop(unsatvar_stack);
			index = index_in_unsatvar_stack[v];
			unsatvar_stack[index] = last_unsat_var;
			index_in_unsatvar_stack[last_unsat_var] = index;
		}
	}
}

static void flip(int flipvar)
{
	cur_soln[flipvar] = 1 - cur_soln[flipvar];

	int v,c;

	lit* clause_c;

	int org_flipvar_score = score[flipvar];

	//update related clauses and neighbor vars
	for(lit *q = var_lit[flipvar]; (c=q->clause_num)>=0; q++)
	{
		clause_c = clause_lit[c];
		if(cur_soln[flipvar] == q->sense)
		{
			++sat_count[c];

			if (sat_count[c] == 2) //sat_count from 1 to 2
				score[sat_var[c]] += clause_weight[c];
			else if (sat_count[c] == 1) // sat_count from 0 to 1
			{
				sat_var[c] = flipvar;//record the only true lit's var
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] -= clause_weight[c];

				sat(c);
			}
		}
		else // cur_soln[flipvar] != cur_lit.sense
		{
			--sat_count[c];
			if (sat_count[c] == 1) //sat_count from 2 to 1
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++)
				{
					if(p->sense == cur_soln[v] )
					{
						score[v] -= clause_weight[c];
						sat_var[c] = v;
						break;
					}
				}
			}
			else if (sat_count[c] == 0) //sat_count from 1 to 0
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] += clause_weight[c];
				unsat(c);
			}//end else if

		}//end else
	}

	score[flipvar] = -org_flipvar_score;

	/*update CCD */
	int index;

	conf_change[flipvar] = 0;
	//remove the vars no longer goodvar in goodvar stack
	for(index=goodvar_stack_fill_pointer-1; index>=0; index--)
	{
		v = goodvar_stack[index];
		if(score[v]<=0)
		{
			goodvar_stack[index] = pop(goodvar_stack);
			already_in_goodvar_stack[v] = 0;
		}
	}

	//update all flipvar's neighbor's conf_change to be 1, add goodvar
	int* p;
	for(p=var_neighbor[flipvar]; (v=*p)!=0; p++)
	{
		conf_change[v] = 1;

		if(score[v]>0 && already_in_goodvar_stack[v] ==0)
		{
			push(v,goodvar_stack);
			already_in_goodvar_stack[v] = 1;
		}
	}
}


/*************weighting ************************************************/

// swt
static int   ave_weight=1;
static int   delta_total_weight=0;
int   threshold;
float p_scale;//w=w*p+ave_w*q
float q_scale;
int   scale_ave;//scale_ave==ave_weight*q_scale


static void smooth_clause_weights_swt(void)
{
	int j,c,v;
	int new_total_weight=0;

	for (v=1; v<=num_vars; ++v)
		score[v] = 0;

	//smooth clause score and update score of variables
	for (c = 0; c<num_clauses; ++c)
	{
		clause_weight[c] = clause_weight[c]*p_scale+scale_ave;
		if(clause_weight[c]<1) clause_weight[c] = 1;

		new_total_weight+=clause_weight[c];

		//update score of variables in this clause
		if (sat_count[c]==0)
		{
			for(j=0; j<clause_lit_count[c]; ++j)
			{
				score[clause_lit[c][j].var_num] += clause_weight[c];
			}
		}
		else  if(sat_count[c]==1)
			score[sat_var[c]]-=clause_weight[c];
	}
	
	
	goodvar_stack_fill_pointer = 0;
	for (v = 1; v <= num_vars; v++) {
		if(score[v]>0 &&  conf_change[v]==1) {
			already_in_goodvar_stack[v] = 1;
			push(v,goodvar_stack);
		} else {
			already_in_goodvar_stack[v] = 0;
		}
	}

	ave_weight=new_total_weight/num_clauses;
}

static void weighting_swt(void)
{
	int i,v;

	for(i=0; i < unsat_stack_fill_pointer; ++i)
		clause_weight[unsat_stack[i]]++;

	for(i=0; i<unsatvar_stack_fill_pointer; ++i)
	{
		v = unsatvar_stack[i];
		score[v] += unsat_app_count[v];
		//if(score[v]>0 &&  conf_change[v]==1 && already_in_goodvar_stack[v] ==0)
		if(score[v]>0 && already_in_goodvar_stack[v] ==0)
		{
			push(v,goodvar_stack);
			already_in_goodvar_stack[v] =1;
		}
	}

	delta_total_weight+=unsat_stack_fill_pointer;
	if(delta_total_weight>=num_clauses)
	{
		ave_weight+=1;
		delta_total_weight -= num_clauses;

		//smooth weights
		if(ave_weight>threshold)
			smooth_clause_weights_swt();
	}
}




/**********************************PAWS weighting*************************************************/
const int	  dec_weight =1;
const float       MY_RAND_MAX_FLOAT = 10000000.0;
const int   	  MY_RAND_MAX_INT =   10000000;
const float 	BASIC_SCALE = 0.0000001; //1.0f/MY_RAND_MAX_FLOAT;
float  smooth_probability;
int    large_clause_count_threshold;

//for PAWS (for large ksat)
int            large_weight_clauses[MAX_CLAUSES];
int            large_weight_clauses_count=0;	


void inc_clause_weights_paws()
{
	int i, j, c, v;
	
	for(i=0; i < unsat_stack_fill_pointer; ++i)
	{
		c = unsat_stack[i];
		clause_weight[c]++;
		if(clause_weight[c] == 2)
		{
			large_weight_clauses[large_weight_clauses_count++] = c;
		}
	}
	
	for(i=0; i<unsatvar_stack_fill_pointer; ++i)
	{
		v = unsatvar_stack[i];
		score[v] += unsat_app_count[v];
		if(score[v]>0 &&  conf_change[v]>0  && already_in_goodvar_stack[v] ==0)//
		{
			push(v,goodvar_stack);
			already_in_goodvar_stack[v] =1;
		}
	}

}

void smooth_clause_weights_paws()
{
	int i, j,clause, var;
	for(i=0; i<large_weight_clauses_count; i++)
	{
		clause = large_weight_clauses[i];
		if(sat_count[clause]>0)
		{
			clause_weight[clause]-=dec_weight;
				
			if(clause_weight[clause]==1)
			{
				large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count];
				i--;
			}
			if(sat_count[clause] == 1)
			{
				var = sat_var[clause];
				score[var]+=dec_weight;
				if(score[var]>0 &&  conf_change[var]>0  && already_in_goodvar_stack[var]==0)
				{
					push(var,goodvar_stack);
					already_in_goodvar_stack[var]=1;
				}
			}
		}
	}
	
}

void weighting_paws()
{
	if( ((rand()%MY_RAND_MAX_INT)*BASIC_SCALE)<smooth_probability && large_weight_clauses_count>large_clause_count_threshold )
		smooth_clause_weights_paws();
	else 
		inc_clause_weights_paws();
}

/**************************setting clause weighting scheme***********************/

void (* update_clause_weights)();

void default_clause_weighting(int weighting_type)
{
	if(weighting_type==1)
	{
		//swt
		update_clause_weights = weighting_swt;
		threshold=50;//560; // 500
		p_scale=0.3;//0.52;
		q_scale=0.7;//0.42;
		scale_ave=(threshold+1)*q_scale;
	}
	else
	{
		//paws
		update_clause_weights = weighting_paws;
		smooth_probability = 0.1;
		large_clause_count_threshold = 10;//do we need this parameter?
	}
	
}

/********************************************end weighting************************************/

static int pick_var(void)
{
	int         i,k,c,v;
	int         best_var;
	lit*		clause_c;

	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(goodvar_stack_fill_pointer>0)
	{

		//if(goodvar_stack_fill_pointer<balancePar)
		//{
			best_var = goodvar_stack[0];
			for(i=1; i<goodvar_stack_fill_pointer; ++i)
			{
				v=goodvar_stack[i];
				if(score[v]>score[best_var]) best_var = v;
				else if(score[v]==score[best_var])
				{
					//if(unsat_app_count[v]>unsat_app_count[best_var]) best_var = v;
					//else if(unsat_app_count[v]==unsat_app_count[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
					
					if(time_stamp[v]<time_stamp[best_var]) best_var = v;
				}
			}
			return best_var;
		//}
		/*else
		{
			best_var = goodvar_stack[rand()%goodvar_stack_fill_pointer];
			for(int j=1;j<balancePar;++j)
			{
				v = goodvar_stack[rand()%goodvar_stack_fill_pointer];
				if(score[v]>score[best_var]) best_var = v;
				else if(score[v]==score[best_var])
				{
					//if(unsat_app_count[v]>unsat_app_count[best_var]) best_var = v;
					//else if(unsat_app_count[v]==unsat_app_count[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
					if(time_stamp[v]<time_stamp[best_var]) best_var = v;
				}
			}
			return best_var;
		}*/
	}
	
	
	/*aspiration*/
	if (aspiration_active)
	{
		best_var = 0;
		for(i=0; i<unsatvar_stack_fill_pointer; ++i)
		{
			if(score[unsatvar_stack[i]]>ave_weight) 
			{
				best_var = unsatvar_stack[i];
				break;
			}
		}

		for(++i; i<unsatvar_stack_fill_pointer; ++i)
		{
			v=unsatvar_stack[i];
			if(score[v]>score[best_var]) best_var = v;
			else if(score[v]==score[best_var] && time_stamp[v]<time_stamp[best_var]) best_var = v;
		}
		
		if(best_var!=0) return best_var;
	}
	/*****end aspiration*******************/

	update_clause_weights();

	/*focused random walk*/

	c = unsat_stack[rand()%unsat_stack_fill_pointer];
	clause_c = clause_lit[c];
	best_var = clause_c[0].var_num;
	for(k=1; k<clause_lit_count[c]; ++k)
	{
		v=clause_c[k].var_num;
		
		//using score
		//if(score[v]>score[best_var]) best_var = v;
		//else if(score[v]==score[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
		
		//using unweighted make
		if(unsat_app_count[v]>unsat_app_count[best_var]) best_var = v;
		//else if(unsat_app_count[v]==unsat_app_count[best_var] && time_stamp[v]<time_stamp[best_var]) best_var = v;
		else if(unsat_app_count[v]==unsat_app_count[best_var])
		{
			if(score[v]>score[best_var]) best_var = v;
			else if(score[v]==score[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
		}
	}

	return best_var;
}


//set functions in the algorithm

void ls_init(void) {
	build_neighbor_relation();
}

void ls_restart(const int *soln, const int opt) {
	int v, c, i;
	for (c = 0; c<num_clauses; c++)
		clause_weight[c] = 1;
	for (v = 1; v <= num_vars; ++v) {
		assert(0 == soln[v] || 1 == soln[v]);
		cur_soln[v] = soln[v];
	}

	unsat_stack_fill_pointer = 0;
	unsatvar_stack_fill_pointer = 0;

	step = 0;

	for (v = 1; v <= num_vars; v++) {
		time_stamp[v] = 0;
		conf_change[v] = 1;
		unsat_app_count[v] = 0;
	}

	/* figure out sat_count, and init unsat_stack */
	for (c = 0; c < num_clauses; ++c) {
		sat_count[c] = 0;
		for(i = 0; i < clause_lit_count[c]; ++i) {
			if (cur_soln[clause_lit[c][i].var_num] == clause_lit[c][i].sense) {
				sat_count[c]++;
				sat_var[c] = clause_lit[c][i].var_num;
			}
		}
		if (sat_count[c] == 0)
			unsat(c);
	}

	/*figure out var score*/
	int lit_count;
	for (v = 1; v <= num_vars; v++) {
		score[v] = 0;
		lit_count = var_lit_count[v];

		for(i = 0; i < lit_count; ++i) {
			c = var_lit[v][i].clause_num;
			if (sat_count[c] == 0)
				score[v]++;
			else if (sat_count[c] == 1 && var_lit[v][i].sense == cur_soln[v])
				score[v]--;
		}
	}

	//init goodvars stack
	goodvar_stack_fill_pointer = 0;
	for (v = 1; v <= num_vars; v++) {
		if(score[v]>0) {
			already_in_goodvar_stack[v] = 1;
			push(v,goodvar_stack);
		} else {
			already_in_goodvar_stack[v] = 0;
		}
	}

	//setting for the virtual var 0
	time_stamp[0] = 0;

	lb_opt = opt;
	lb_copy();
	
	
}

int lb_update_reduce;
void ls_process(long long no_improv_times) {
	int flipvar;
	long long notime = 1 + no_improv_times;
	while (--notime) {
		step++;

		flipvar = pick_var();
		flip(flipvar);
		time_stamp[flipvar] = step;

		if (unsat_stack_fill_pointer < lb_opt) {
			lb_opt = unsat_stack_fill_pointer;
			lb_copy();
			notime = 1 + no_improv_times;
		}

		if (unsat_stack_fill_pointer < the_best.opt_unsat) {
			update_best_value(unsat_stack_fill_pointer);
			lb_update(tries);
			
			if(the_best.opt_unsat==0) {
				ls_update_best_soln();
				return;
			}
		}
		
		if (get_runtime() >= cutoff_time) {
			return;
		}

	}

	int b = tries / lb_update_reduce;
	if (0 == b)
		b = 1;
	lb_update(b);
}

