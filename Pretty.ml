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

let rec string_of_process p :string = 
  match p with 
    Stop -> "Stop"
  | Skip -> "Skip"
  | EventPre (ev, pIn) ->  
      (match ev with 
    | Str str -> str ^ " -> " ^ string_of_process pIn
    | TOCK -> "tock" ^ " -> " ^ string_of_process pIn
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
    Event ev ->
    (match ev with 
    | Str str -> str 
    | TOCK -> "tock" 
    ) 
  | Neg ltlIn  -> "!" ^string_of_mltl ltlIn 
  | OrLTL (mltl1, mltl2) ->  string_of_mltl mltl1  ^" or " ^   string_of_mltl mltl2
  | AndLTL (mltl1, mltl2) ->  string_of_mltl mltl1  ^" and " ^   string_of_mltl mltl2
  | Until (mltl1,t, mltl2) ->  string_of_mltl mltl1  ^" U_"^string_of_int t ^" " ^   string_of_mltl mltl2
  | Finally (t, mltlIn) ->  "F_"^string_of_int t ^" " ^   string_of_mltl mltlIn
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

