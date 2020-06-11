%{ open Ast %}
%{ open List %}

%token <string> EVENT
%token <string> VAR
%token <int> INTE
%token <string> STRING
%token <bool> TRUEE  
%token <bool> FALSEE
%token EMPTY ASSERTKEY EVENTKEY CHOICE LPAR RPAR CONCAT OMEGA POWER PLUS MINUS TRUE FALSE DISJ CONJ   ENTIL INTT BOOLT VOIDT 
%token LBRACK RBRACK COMMA SIMI  IF ELSE REQUIRE ENSURE LSPEC RSPEC RETURN LBrackets  RBrackets
%token EOF GT LT EQ GTEQ LTEQ INCLUDE SHARP EQEQ UNDERLINE KLEENE NEGATION DEADLINE RESET TASSERTKEY

(*%token FUTURE GLOBAL IMPLY LTLNOT NEXT UNTIL LILAND LILOR*)

%left CHOICE
%left CONCAT
%left DISJ
%left CONJ

%start prog ee es_p  t_entailment_p
%type <(Ast.entilment) list > ee
%type <Ast.program> prog
%type <Ast.es> es_p
%type <(Ast.t_entilment) list> t_entailment_p


%%

ee: 
| EOF {[]}
| a = entailment SIMI r = ee { append [a] r }


es_p: r = es EOF { r }


t_entailment_p: 
| EOF {[]}
| a = t_entailment SIMI r = t_entailment_p { append [a] r }


type_: 
| INTT {INT}
| BOOLT {BOOL}
| VOIDT {VOID}

singleP: t = type_   var = VAR {[(t, var)]}

param:
| {[]}
| p = singleP {p}
| p1 = singleP  COMMA  p2 = param {append p1 p2 }

real_singleP: e = expres {[e]}

real_param:
| p = real_singleP {p}
| p1 = real_singleP  COMMA  p2 = real_param {append p1 p2 }

expres_help : 
| {Unit}
| RETURN {Return}
| t = INTE {Integer t}
| b =  TRUEE {Bool b }
| b =  FALSEE {Bool b }
| v = VAR {Variable v}
| s = STRING {String s}
| t = type_ name = VAR EQ e = expres_help {LocalDel (t, name, e)}
| name = VAR LPAR vlist = real_param RPAR {Call (name, vlist)}
| v = VAR EQ e = expres_help{Assign (v, e)}
| EVENTKEY LPAR ev = STRING p=parm RPAR {EventRaise (ev,p)}
| ASSERTKEY LPAR eff = effect RPAR {Assertion eff}
| TASSERTKEY LPAR eff = t_effect RPAR {TAssertion eff}

| DEADLINE LPAR c = cocon RPAR {Deadline c}
| RESET LPAR re = existVar RPAR {Reset re}

cond:
| e1 = expres_help  EQEQ e2 = expres_help {Cond (e1, e2 ,"==")}
| e1 = expres_help  LTEQ e2 = expres_help {Cond (e1, e2 ,"<=")}
| e1 = expres_help  GTEQ e2 = expres_help {Cond (e1, e2 ,">=")}
| e1 = expres_help  GT e2 = expres_help {Cond (e1, e2 ,">")}
| e1 = expres_help  LT e2 = expres_help {Cond (e1, e2 ,"<")}


expres:
| e = expres_help {e } 
| e1 = expres_help SIMI e2 = expres {Seq (e1, e2)}
| IF LPAR e1 = cond RPAR LBRACK e2 = expres RBRACK ELSE LBRACK e3 = expres RBRACK {IfElse (e1, e2, e3)}
| e1 = expres_help PLUS e2 = expres_help {BinOp(e1, e2,"+" )}
| e1 = expres_help MINUS e2 = expres_help {BinOp(e1, e2,"-" )}

meth : t = type_   name = VAR   LPAR p = param RPAR s = spec LBRACK e = expres RBRACK {Method (Meth (t , name, p, s, e))}
head : SHARP INCLUDE str= STRING {Include str} 


prog_rest:
| EOF {[]}
| tl = prog hd = prog_rest  {append tl hd}

prog:
| me =  meth p = prog_rest {append [me] p}
| hd =head  p = prog_rest {append [hd] p}

spec: LSPEC REQUIRE e1 = t_effect  ENSURE e2 = t_effect RSPEC {PrePost(e1, e2)}

term:
| str = VAR { Var str }
| n = INTE {Number n}
| LPAR r = term RPAR { r }
| a = term b = INTE {Minus (a, Number (0 -  b))}

| LPAR a = term MINUS b = term RPAR {Minus (a, b )}

| LPAR a = term PLUS b = term RPAR {Plus (a, b)}



pure:
| TRUE {TRUE}
| FALSE {FALSE}
| NEGATION LPAR a = pure RPAR {Neg a}
| LPAR r = pure RPAR { r }
| a = term GT b = term {Gt (a, b)}
| a = term LT b = term {Lt (a, b)}
| a = term GTEQ b = term {GtEq (a, b)}
| a = term LTEQ b = term {LtEq (a, b)}
| a = term EQ b = term {Eq (a, b)}
| a = pure CONJ b = pure {PureAnd (a, b)}
| a = pure DISJ b = pure {PureOr (a, b)}

es_range :
| single = es {[single]}
| e = es_range COMMA eddd = es {append e [eddd]}

parm:
| {None}
| LPAR i=INTE RPAR {Some i}


es:
| EMPTY { Emp }
| str = EVENT p=parm { Event ( str, p) }
| LPAR r = es RPAR { r }
| a = es CHOICE b = es { ESOr(a, b) }
| a = es CONJ b = es { ESAnd(a, b) }
| LPAR r = es POWER t = term RPAR { Ttimes(r, t )}
| LPAR r = es POWER OMEGA RPAR{ Omega r }
| UNDERLINE {Underline}
| a = es CONCAT b = es { Cons(a, b) } 
| LPAR a = es POWER KLEENE RPAR{Kleene a}
| LBRACK a = es_range RBRACK {Range a}
| NEGATION LPAR a = es RPAR {Not a}



singleVAR: var = VAR {[var]}

existVar:
| {[]}
| p = singleVAR {p}
| p1 = singleVAR  COMMA  p2 = existVar {append p1 p2 }


effect:
| LPAR r = effect RPAR { r }
| a = pure  CONJ  b= es  {Effect (a, b)}
| a = effect  DISJ  b=effect  {Disj (a,b)}
| LPAR LBrackets nn= existVar RBrackets  eff= effect RPAR{
  let rec helper (eff:effect) :effect = 
  (match eff with 
    Effect (p, es) -> Effect (p, es) 
  | Disj (eff1, eff2) ->  Disj (helper eff1, helper eff2)  
  )
  in 
  helper eff}

entailment:
| lhs = effect   ENTIL   rhs = effect {EE (lhs, rhs)}

cocon:
| UNDERLINE {CCTop} 
| FALSE {CCBot} 
| clock = VAR LT n = INTE {CCLT (clock, n) }
| clock = VAR LTEQ n = INTE {CCLTEQ (clock, n) }
| clock = VAR GT n = INTE {CCGT (clock, n) }
| clock = VAR GTEQ n = INTE {CCGTEQ (clock, n) }
| c1 = cocon CONJ c2 = cocon {CCAND (c1, c2)}



transition: 
| LBrackets EMPTY COMMA cc =cocon COMMA LBRACK re = existVar RBRACK RBrackets {  (TEmp, cc , re)}
| LBrackets ev= EVENT COMMA cc =cocon COMMA LBRACK re = existVar RBRACK RBrackets {  (EV ev, cc , re)}


t_es:
| EMPTY { ESEMP }
| tran = transition { Single tran }
| UNDERLINE {TAny}
| a = t_es CONCAT b = t_es { TCons(a, b) } 
| a = t_es CHOICE b = t_es { TOr(a, b) }
| LPAR a = t_es POWER KLEENE RPAR{TKleene a}
| LPAR r = t_es POWER t = term RPAR { TNtimes(r, t )}



t_effect:
| a = pure  CONJ  b= t_es  {TEff (a, b)}
| a = t_effect  DISJ  b=t_effect  {TDisj (a, b) }
| LPAR r = t_effect RPAR { r }


t_entailment:
| lhs = t_effect   ENTIL   rhs = t_effect { (lhs, rhs)}
 

