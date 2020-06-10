(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open String
open List
open Ast
open Printf
open Askz3
open Int32


exception Foo of string


(*used to generate the free veriables, for subsititution*)
let freeVar = ["t1"; "t2"; "t3"; "t4";"t5";"t6";"t7";"t8";"t9";"t10"
              ;"t11"; "t12"; "t13"; "t14";"t15";"t16";"t17";"t18";"t19";"t20"
              ;"t21"; "t22"; "t23"; "t24";"t25";"t26";"t27";"t28";"t29";"t30"];;



let rec getAfreeVar (varList:string list):string  =
  let rec findOne li = 
    match li with 
        [] -> raise ( Foo "freeVar list too small exception!")
      | x :: xs -> if (exists (fun a -> String.compare a x == 0) varList) == true then findOne xs else x
  in
  findOne freeVar
;;

let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl

let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└── "
      else
        "├── "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, li) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ((<>) Leaf) li;;

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"

  ;;

let rec string_of_cocons (con:cocon) : string = 
  match con with 
    CCTop -> "T"
  | CCBot -> "_|_"
  | CCLT (clock, n) -> clock ^ " < " ^ string_of_int n 
  | CCLTEQ  (clock, n) -> clock ^ " <= " ^ string_of_int n 
  | CCGT (clock, n) -> clock ^ " > " ^ string_of_int n 
  | CCGTEQ (clock, n) -> clock ^ " >= " ^ string_of_int n 
  | CCAND (co1, co2) -> string_of_cocons  co1 ^ " /\\ " ^ string_of_cocons co2


let rec string_of_transition ((a, b, c):t_trans)  : string = 

      let temp  = List.fold_left (fun acc a -> acc ^ " "^ a) "" c in 
      let aa = (match a with 
                EV str -> str
              | TEmp -> "emp"
      ) in 
      "[" ^ aa ^", " ^ string_of_cocons b ^", "^ "(" ^temp ^")" ^"]"
 
  ;;

(*To pretty print terms*)
let rec showTerms (t:terms):string = 
  match t with
    Var name -> name
  | Number n -> string_of_int n
  | Plus (t1, t2) -> (showTerms t1) ^ ("+") ^ (showTerms t2)
  | Minus (t1, t2) -> (showTerms t1) ^ ("-") ^ (showTerms t2)

  ;;

(*To pretty print pure formulea*)
let rec showPure (p:pure):string = 
  match p with
    TRUE -> "true"
  | FALSE -> "false"
  | Gt (t1, t2) -> (showTerms t1) ^ ">" ^ (showTerms t2)
  | Lt (t1, t2) -> (showTerms t1) ^ "<" ^ (showTerms t2)
  | GtEq (t1, t2) -> (showTerms t1) ^ ">=" ^ (showTerms t2)
  | LtEq (t1, t2) -> (showTerms t1) ^ "<=" ^ (showTerms t2)
  | Eq (t1, t2) -> (showTerms t1) ^ "=" ^ (showTerms t2)
  | PureOr (p1, p2) -> "("^showPure p1 ^ "\\/" ^ showPure p2^")"
  | PureAnd (p1, p2) -> "("^showPure p1 ^ "/\\" ^ showPure p2^")"
  | Neg p -> "(!" ^ "(" ^ showPure p^"))"
  ;; 

let rec string_of_timedES (tes:t_es):string = 
  match tes with 
    Nil -> "Tbot"
  | ESEMP -> "emp"
  | Single tran -> string_of_transition tran 
  | TCons (tes1, tes2) -> string_of_timedES tes1 ^" . " ^ string_of_timedES tes2 
  | TOr (tes1, tes2) -> string_of_timedES tes1 ^" | " ^ string_of_timedES tes2 
  | TNtimes (tesIn, t) -> "("^(string_of_timedES tesIn) ^ "^" ^ (showTerms t)^")"
  | TKleene esIn -> "(" ^ (string_of_timedES esIn) ^ "^" ^ "*"^")"
  | TAny -> "_"
  | TNot esIn -> "!"^ string_of_timedES esIn
  ;;

let rec string_of_timedEff (effL :t_effect): string = 
  match effL with 
  | TEff (p, t_es)  -> showPure p  ^ "/\\" ^ string_of_timedES t_es
  | TDisj (eff1, eff2) -> string_of_timedEff eff1 ^ "\\/" ^ string_of_timedEff eff2

    ;;

let string_of_TimedEntailmentEff lhs rhs :string = 
  string_of_timedEff lhs ^ " |- " ^ string_of_timedEff rhs 
  ;;

(*
let compareEv ev1 ev2 : bool =
  match (ev1, ev2) with 
    (Str s1, Str s2) -> String.compare s1 s2 == 0
  | (TOCK, TOCK) -> true
  | (Any, Any) -> true
  | _ -> false
  ;; 

let string_of_event ev : string = 
  match ev with 
    Str s -> s 
  | TOCK -> "tock"
  | Any -> "_"
  ;;

let rec string_of_process p :string = 
  match p with 
    Stop -> "Stop"
  | Skip -> "Skip"
  | EventPre (ev, pIn) ->  
      (match ev with 
    | Str str -> str ^ " -> " ^ string_of_process pIn
    | TOCK -> "tock" ^ " -> " ^ string_of_process pIn
    | Any -> "_"
    )
  | Choice (p1, p2) -> string_of_process p1 ^ " | " ^ string_of_process p1
  | Follow (p1, p2) -> string_of_process p1 ^ "; " ^ string_of_process p1
  | Parallel (p1, p2) -> string_of_process p1 ^ " || " ^ string_of_process p1
  | Wait t -> "Wait " ^ string_of_int t
  | Interrupt (p1, t , p2) -> string_of_process p1 ^ " |> {" ^ string_of_int t ^ "} " ^ string_of_process p1
  | Deadline (pIn, t) -> string_of_process pIn ^ "ddl " ^ string_of_int t
;;

let rec string_of_mltl ltl : string = 
  match ltl with 
    Bot -> "_|_"
  | Emp -> "emp"
  | Event ev ->string_of_event ev
  | Neg ev  -> "!" ^string_of_event ev
  | OrLTL (mltl1, mltl2) ->  string_of_mltl mltl1  ^" or " ^   string_of_mltl mltl2
  | AndLTL (mltl1, mltl2) ->  string_of_mltl mltl1  ^" and " ^   string_of_mltl mltl2
  | Until (mltl1,t, mltl2) ->  string_of_mltl mltl1  ^" U_"^string_of_int t ^" " ^   string_of_mltl mltl2
  | Finally (t, mltlIn) ->  "F_"^string_of_int t ^" " ^   string_of_mltl mltlIn
  | Next mltlIn -> "X " ^string_of_mltl mltlIn
  ;;

let rec nullable_process (p:process) : bool =
   match p with 
    Stop -> false
  | Skip -> true
  | EventPre (ev, pIn) ->  false
  | Choice (p1, p2) -> nullable_process p1 || nullable_process p1
  | Follow (p1, p2) -> nullable_process p1 && nullable_process p1
  | Parallel (p1, p2) -> nullable_process p1 && nullable_process p1
  | Wait t -> if t >0 then false else true
  | Interrupt (p1, t , p2) -> 
    if t > 0 then false else nullable_process p2
  | Deadline (pIn, t) -> nullable_process pIn
;;

let rec fst_process (p:process) : event list = 
    match p with 
    Stop -> []
  | Skip -> []
  | EventPre (ev, pIn) ->  [ev] 
  | Choice (p1, p2) -> List.append (fst_process p1) (fst_process p1)
  | Follow (p1, p2) -> if nullable_process p1 then List.append (fst_process p1) (fst_process p1) else fst_process p1
  | Parallel (p1, p2) -> List.append (fst_process p1) (fst_process p1)
  | Wait t -> [TOCK]
  | Interrupt (p1, t , p2) -> if t > 0 then fst_process p1 else List.append (fst_process p1) (fst_process p2)
  | Deadline (pIn, t) -> fst_process pIn 
;;

let rec derivative_process (p:process) (evP:event): process = 
  match p with 
    Stop -> Stop
  | Skip -> Stop
  | EventPre (ev, pIn) ->  
    if compareEv ev evP then Skip else Stop
  | Choice (p1, p2) -> Choice (derivative_process p1 evP, derivative_process p2 evP)
  | Follow (p1, p2) -> 
    let left = Follow (derivative_process p1 evP, p2) in 
    if nullable_process p1 then Choice (left, derivative_process p2 evP) else left
  | Parallel (p1, p2) -> 
    let fromLeft = Parallel (derivative_process p1 evP, p2) in
    let fromRight = Parallel (p1, derivative_process p2 evP) in
    Choice (fromLeft, fromRight)
  | Wait t -> if compareEv TOCK evP then Wait (t-1) else Stop
  | Interrupt (p1, t , p2) -> 
    let noTimeElapse = Interrupt (derivative_process p1 evP , t, p2) in 
    let timeElapse = Interrupt (derivative_process p1 evP , t-1 , p2) in 
    if t > 0 then Choice(noTimeElapse, timeElapse) else derivative_process p2 evP
  | Deadline (pIn, t) -> 
    let noTimeElapse = Deadline (derivative_process pIn evP , t) in 
    let timeElapse = Deadline (derivative_process pIn evP , t-1) in 
    Choice(noTimeElapse, timeElapse)
;;

let rec intersect l1 l2 =
  match l1 with [] -> []
  | h1::t1 -> (
  match l2 with [] -> []
  | h2::t2 when h1 < h2 -> intersect t1 l2
  | h2::t2 when h1 > h2 -> intersect l1 t2
  | h2::t2 -> (
  match intersect t1 t2 with [] -> [h1]
  | h3::t3 as l when h3 = h1 -> l
  | h3::t3 as l -> h1::l
  )
  );;

let rec fst_mltl (ltl:mltl): event list = 
  match ltl with 
    Bot -> []
  | Emp -> []
  | Event ev ->
    (match ev with 
    | Str str -> [ev] 
    | _ -> print_string (string_of_mltl ltl) ; raise (Foo "error here!");
    ) 
  | Neg ev  -> 
    match ev with 
      Str s -> [NotStr ev]
    | 
    | 
  | OrLTL (mltl1, mltl2) ->  List.append (fst_mltl mltl1) (fst_mltl mltl2)
  | AndLTL (mltl1, mltl2) ->  intersect (fst_mltl mltl1) (fst_mltl mltl2)
  | Until (mltl1,t, mltl2) ->  List.append (fst_mltl mltl1) (fst_mltl mltl2)
  | Finally (t, mltlIn) ->  List.append ([Any]) (fst_mltl mltlIn)
  | Next mltlIn -> fst_mltl mltlIn
  ;;

let rec derivative_mltl (ltl:mltl) (evP:event): mltl = 
  match ltl with 
    Bot -> Bot
  | Emp -> Bot
  | Event ev -> if compareEv ev evP then Emp else Bot
  | Neg ltlIn  -> raise (Foo "I do not know how to do here yet ltl");
  | OrLTL (mltl1, mltl2) ->  OrLTL (derivative_mltl evP mltl1, derivative_mltl evP mltl2)
  | AndLTL (mltl1, mltl2) ->  AndLTL (derivative_mltl evP mltl1, derivative_mltl evP mltl2)
  | Until (mltl1,t, mltl2) ->  List.append (fst_mltl mltl1) (fst_mltl mltl2)
  | Finally (t, mltlIn) ->  List.append ([Any]) (fst_mltl mltlIn)
  ;;
*)