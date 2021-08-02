#ifndef _CNC_H_
#define _CNC_H_

extern double cnc_unit_last;
extern double lb_last_prob;
extern double refer_gbest_prob;
extern int vage_window;

void cnc_init(int cb_cap);
void cnc_process(const long long step_num);
bool cnc_get_canbest(const int* &soln, int &opt);

#endif
