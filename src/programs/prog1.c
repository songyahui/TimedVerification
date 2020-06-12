#include "primitives.c"

/*
song <a, b > = TRUE/\ emp 
*/


void send (int n) 
    /*
    require song <a, b>
    ensure (TRUE /\ [ Done, _ , {} ] . [ emp, _ , {x} ] . [ emp, x < 10, {} ])
    */
{

    event ("Done");
    reset (x);
    ddl (x < 10);
} 
