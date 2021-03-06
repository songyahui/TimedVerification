type terms = Var of string
           | Number of int
           | Plus of terms * terms
           | Minus of terms * terms 

(* We use a string to represent an single event *)
type event =  string 
type mn = string
type var = string 

(*Event sequence *)
type es = Bot 
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

(*Effects*)
type effect = 
            Effect of pure * es
          | Disj of effect * effect


type entilment = EE of effect * effect


type hypotheses = (effect * effect) list


type _type = INT | FLOAT | BOOL | VOID


(**********************************************)

type clock = string

type cocon = CCTop 
          | CCBot 
          | CCLT of clock * int 
          | CCLTEQ  of clock * int 
          | CCGT of clock * int 
          | CCGTEQ of clock * int 
          | CCAND of cocon * cocon

type t_ev = EV of event | TEmp

type t_trans  = (t_ev * cocon * (clock list))
(*Event sequence *)
type t_es = Nil 
        | ESEMP
        | Single of t_trans
        | TCons of t_es * t_es
        | TOr of t_es * t_es
        | TNtimes of t_es * terms
        | TKleene of t_es
        | TNot of t_es
        | TAny

type t_effect = TEff of pure * t_es | TDisj of t_effect * t_effect
                

type t_entilment =  (t_effect * t_effect)

type t_hypotheses = (t_effect * t_effect) list

type expression = Unit 
          | Return
          | Integer of int
          | Bool of bool
          | Float of float
          | String of string
          | Variable of var
          | LocalDel of _type * var * expression 
          | Call of mn * expression list 
          | Assign of var * expression
          | Seq of expression * expression
          | EventRaise of (event*int option)
          | IfElse of expression * expression * expression
          | Cond of expression * expression * string
          | BinOp of expression * expression * string
          | Assertion of effect
          | TAssertion of t_effect
          | Deadline of cocon 
          | Reset of (clock list)
          | Delay of int 
          | Triple of (event * cocon * (clock list))



type spec = PEFF of t_effect | EFFCALL of mn * (event list)

type prepost = spec * spec

type param  = (_type * var) list

type meth = _type * mn * param * prepost * expression

type pred = (mn * (var list) * t_effect)

type declare = Include of string | Method of meth | Predicate of pred

type program = declare list
