#include "primitives.c"

/*
finally <ev> = TRUE /\ (_^*) . [ ev, x<5 , {x} ] 
*/


void send (int n) 
    /*
    require (TRUE/\ emp )
    ensure finally <Done> 
    */
{

    event ("Ready1");
    event ("Ready2");
    event ("Ready3");
    triple ("Done", x < 5, x );

} 
