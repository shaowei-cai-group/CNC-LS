Instructions about how to compile and run CCAnr+cnc:

Compile CCAnr+cnc:
    make

Run CCAnr+cnc:
    ./CCAnr+cnc
        -inst <cnf_instance>
        -seed <seed>
        -cutoff_time <cutoff_time>
        -dynamic {0,1}   ##0 indicates performing non-dynamic method; 1 indicates performing dynamic method
        -cnctimes <cnc_times>   ##indicate the value of cnc_times underlying CCAnr+cnc
        -ls_no_improv_steps <MaxNoImprSteps>   ##indicate the value of MaxNoImprSteps underlying CCAnr+cnc
        -swt_p <\rho>   ##indicate the value of \rho underlying CCAnr
        -swt_q <q>   ##indicate the value of q underlying CCAnr
        -swt_threshold <\gamma>   ##indicate the value of \gamma underlying CCAnr
