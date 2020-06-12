#include "primitives.c"

/*
until <a, b> = TRUE /\ ([ a, _ , {} ]^*) . [ b, x<3 , {x} ] 
*/


void send (int n) 
    /*
    require (TRUE/\ emp )
    ensure until <Ready, Done> 
    */
{

    event ("Ready");
    triple ("Done", x < 3, x );

} 
