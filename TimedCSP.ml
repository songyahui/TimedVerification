open Ast
open Printf
open Askz3
open String
open Pretty

let a = Event "A";;
let test = EventPre ("A", Stop);;
let testltl = Until (a, 5, a);;
let testltl1 = Finally (5, a);;


let main = 
 print_string (string_of_process test^"\n");
 print_string (string_of_mltl testltl1^"\n") ;