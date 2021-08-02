#include "basis.hpp"
#include "cnc.hpp"
#include "indusLS.hpp"
#include <sstream>
#include <cstdlib>
#include <iostream>
#include <stdio.h>
#include<string.h>
#include "indusLS.hpp"
using namespace std;

static void doLS_dynamic(void);
static void doLS_static(void);

char * inst;
int seed;

static int cnc_times, ls_no_improv_times;
static int cb_cap;
static void (*doLS) (void);

int weighting_type;

static void default_settings(void) {
	ios::sync_with_stdio(false);

	cnc_times = 5;
	ls_no_improv_times = 50000000;
	doLS = doLS_dynamic;
	
	cb_cap = 50;
	balancePar = 40;// no use;
	lb_last_prob = 1;
	lb_update_reduce = 1;
	vage_window = 10;
	
	aspiration_active = false;
	
	weighting_type = 1; //1->SWT; 2->PAWS
	default_clause_weighting(weighting_type);
	
	seed = 1;
	cutoff_time = 3600;
}

static void doLsRestartToCanBest(void) {
	const int *soln;
	int opt;
	if (cnc_get_canbest(soln, opt)) {
		//cout << "c LS force restart to opt=" << opt << " at " << get_runtime() << endl;
		ls_restart(soln, opt);
	}
}

static void doLsRestartToBest(void) {
	ls_restart(the_best.soln, the_best.opt_unsat);
}


static void doCNC(void) {
	cnc_process(cnc_times);
	//if (the_best.opt_try == tries)
	//	cout << "c CNC update: " << the_best.opt_unsat << " at " << the_best.opt_time << endl;
}


int max_no_improv_times=20000000;
static void doLS_dynamic(void) {
	if (ls_no_improv_times*tries<max_no_improv_times)
		ls_process(ls_no_improv_times*tries);
	else
		ls_process(max_no_improv_times);
}

static void doLS_static(void) {
	ls_process(ls_no_improv_times);
}

/*
 * About shouldPrint:
 *
 * At the beginning, shouldPrint = false. o line is printed immediately by update_best_soln() in basis.cpp, while v line is not printed.
 * When there's 90s left, shouldPrint = true. o line will not be printed in update_best_soln(). These lines should be printed by main().
 * The reason is that, v line takes too much time. If doLS() updates solution too frequently, doLS() may take so much time on printing and left an incomplete v line.
 *
 * In conclusion, v line has to be printed by main() in any situation, and o line will be printed immediately in first 210s by update_best_soln().
 * In last 90s, update_best_soln() does not print o line, and which should be printed by main().
 * */
 


bool parse_arguments(int argc, char ** argv)
{

	bool flag_inst = false;
	default_settings();
	
	for (int i=1; i<argc; i++)
	{
		if(strcmp(argv[i],"-inst")==0)
		{
			i++;
			if(i>=argc) return false;
			inst = argv[i];
			flag_inst = true;
			continue;
		}
		else if(strcmp(argv[i],"-seed")==0)
		{
			i++;
			if(i>=argc) return false;
			sscanf(argv[i], "%d", &seed);
			continue;
		}
		else if(strcmp(argv[i],"-cutoff_time")==0)
		{
			i++;
			if(i>=argc) return false;
			sscanf(argv[i], "%d", &cutoff_time);
			continue;
		}
		
		
		else if(strcmp(argv[i],"-aspiration")==0)
		{
			i++;
			if(i>=argc) return false;
			int tmp;
			sscanf(argv[i], "%d", &tmp);
			if (tmp==1)
				aspiration_active = true;
			else 	aspiration_active = false;
			continue;
		}
		
		else if(strcmp(argv[i],"-swt_threshold")==0)
		{
			i++;
			if(i>=argc) return false;
			sscanf(argv[i], "%d", &threshold);
			continue;
		}
		else if(strcmp(argv[i],"-swt_p")==0)
		{
			i++;
			if(i>=argc) return false;
			sscanf(argv[i], "%f", &p_scale);
			continue;
		}
		else if(strcmp(argv[i],"-swt_q")==0)
		{
			i++;
			if(i>=argc) return false;
			sscanf(argv[i], "%f", &q_scale);
			continue;
		}
		
		
		else if(strcmp(argv[i],"-dynamic")==0)
		{
			i++;
			if(i>=argc) return false;
			if(strcmp(argv[i], "0")==0)
			{
				doLS = doLS_static;
				continue;
			}
			else if(strcmp(argv[i], "1")==0)
			{
				doLS = doLS_dynamic;
				continue;
			}
			else return false;
		}
		else if(strcmp(argv[i],"-cnctimes")==0)
		{
			i++;
			if(i>=argc) return false;
			sscanf(argv[i], "%d", &cnc_times);
			continue;
		}
		else if(strcmp(argv[i],"-ls_no_improv_steps")==0){
			i++;
			if(i>=argc) return false;
			sscanf(argv[i], "%d", &ls_no_improv_times);
			continue;
		}
		else return false;
		
	}
	
	if (flag_inst) return true;
	else return false;

}

int main(int argc, char* argv[]) {

	int ret;
	
	ret = parse_arguments(argc, argv);
	if(!ret) {cout<<"c Arguments Error!"<<endl; return -1;}
	
	ret = build_instance(inst);
	if (0 == ret) {
		cout << "c Invalid filename: " << argv[1] << endl;
		return 1;
	}
	
	
	record_runtime();


	cnc_init(cb_cap);
	ls_init();

	srand(seed);

	for (tries = 1; ; tries++) {
		doCNC();

		/*if (shouldPrint && the_best.opt_try == tries) {
			cout << "o " << the_best.opt_unsat << endl;
			print_best_solution();
		}*/
		
		if(the_best.opt_unsat==0) break;

		if (the_best.opt_try == tries)
			doLsRestartToBest();
		else
			doLsRestartToCanBest();

		doLS();
		
		if(the_best.opt_unsat==0) break;

		/*if (shouldPrint && the_best.opt_try == tries && 2 == the_best.source) {
			cout << "o " << the_best.opt_unsat << endl;
			print_best_solution();
		}

		if (!shouldPrint) {
			if (get_runtime() >= cutoff_time - 90) {
				shouldPrint = true;
				print_best_solution();
			}
		} else {
			const double now = get_runtime();
			double left = 2 * now / tries; // the time needed for two `CNC-LS' rounds
			if (left < 10.0)
				left = 10.0;
			// 6s to 10s are left.
			if (now >= cutoff_time - left) {
				break;
			}
		}*/
		const double now = get_runtime();
		if (now >= cutoff_time) {
			break;
		}
	}


	//cout << "c TotalTry=" << tries << endl;
	//cout << "c Finished at " << get_runtime() << endl;
	//cout << "c " << inst << "\t" << the_best.opt_unsat << '\t' << the_best.opt_time << endl;
	
	cout<<"s ";
	if (0==the_best.opt_unsat && verify_sol() ) {
		cout<<"SATISFIABLE"<<endl;
		print_best_solution();
	}
	else cout<<"UNKNOWN"<<endl;
	

    return 0;
}
