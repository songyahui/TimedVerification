#include "primitives.c"

void send (int n) 
    /*
    require TRUE/\ emp 
    ensure TRUE /\ [ Done, _ , {} ] . [ emp, _ , {x} ] . [ emp, x < 10, {} ]
    */
{

    event ("Done");
    reset (x);
    ddl (x < 10);
} 
