type terms = Var of string
           | Number of int
           | Plus of terms * terms
           | Minus of terms * terms 

type event = Str of string | TOCK | Any | NotStr of string
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

(*Event sequence *)
and es = Bot 
        | Emp 
        | Event of event * int option 
        | Cons of es * es
        | ESOr of es * es
        | ESAnd of es * es
        | Ttimes of es * terms
        | Kleene of es
        | Omega of es
        | Range of (es list)
        | Not of es
        | Underline

type timed_effect = Effects of (pure * es) list


  

(*
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
*)
(*
type mltl = 
          Bot
        | Emp
        | Event of event
        | Neg of event 
        | OrLTL of mltl * mltl 
        | AndLTL of mltl * mltl
        | Until of mltl * int * mltl
        | Finally of int *  mltl
        | Next of mltl
*)