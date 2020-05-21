type terms = Var of string
           | Number of int
           | Plus of terms * terms
           | Minus of terms * terms 

type event = Str of string | TOCK
(*Arithimetic pure formulae*)
type pure = TRUE
          | FALSE
          | Gt of terms * terms
          | Lt of terms * terms
          | GtEq of terms * terms
          | LtEq of terms * terms
          | Eq of terms * terms
          | PureOr of pure * pure
          | PureAnd of pure * pure
          | Neg of pure

type process = 
          Stop
        | Skip
        | EventPre of event * process
        | Choice of process * process
        | Follow of process * process
        | Parallel of process * process
        | Wait of int
        | Interrupt of process * int * process
        | Deadline of process * int

type mltl = 
        | Event of event
        | Neg of mltl 
        | OrLTL of mltl * mltl 
        | AndLTL of mltl * mltl
        | Until of mltl * int * mltl
        | Finally of int *  mltl


