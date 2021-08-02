#ifndef _INDUSLS_HPP_
#define _INDUSLS_HPP_

extern int balancePar;
extern int lb_update_reduce;
extern bool aspiration_active;

extern int   threshold;
extern float p_scale;//w=w*p+ave_w*q
extern float q_scale;

void ls_init(void);
void ls_process(long long no_improv_times);
void ls_restart(const int *soln, const int opt);

void default_clause_weighting(int weighting_type);

bool lb_get_prob(int v);
bool lb_get_last(int v);

#endif
