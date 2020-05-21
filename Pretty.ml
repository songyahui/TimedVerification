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


