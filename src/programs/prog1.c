#include "primitives.c"

/*
song <a> = TRUE /\ [ a, _ , {} ] . [ emp, _ , {x} ] . [ emp, x < 10, {} ]
*/


void send (int n) 
    /*
    require (TRUE/\ emp )
    ensure song <Done> 
    */
{
    if (n==0) {
    event ("Done");
    reset (x);
    ddl (x < 10);
    }
    else {

    delay (1);
    }
} 
