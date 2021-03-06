open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open TimedRewriting 
open Sys


let rec printType (ty:_type) :string =
  match ty with
    INT -> "int "
  | FLOAT -> "float "
  | BOOL  -> "bool "
  | VOID  -> "void ";;


let rec printParam (params: param):string = 
  match params with 
    [] -> ""
  | [(t, v)] -> printType t ^ v
  | (t, v)::xs ->  printType t ^ v ^ "," ^ printParam xs ;;


let rec print_real_Param (params: expression list):string = 
  let rec printarg v = (match v with
    Unit  -> "unit"
  | Integer num -> string_of_int num
  | Bool b -> string_of_bool b 
  | Float f -> string_of_float f
  | Variable v -> v 
  | Call (name, elist) -> name ^ "(" ^ print_real_Param elist ^ ")"
  | BinOp (e1, e2, str) -> printarg e1 ^ str ^ printarg e2 
  | _ -> "undefined"
  ) in 
  match params with 
    [] -> ""
  | [v] ->  printarg v
    
  | v::xs ->  
    let pre = printarg v in 
    pre ^ "," ^ print_real_Param xs ;;


let rec printExpr (expr: expression):string = 
  match expr with 
    Unit  -> "unit"
  | Return  -> "return"
  | Integer num -> string_of_int num
  | Bool b -> string_of_bool b 
  | Float f -> string_of_float f
  | String s -> "\"" ^ s^"\""
  | Variable v -> v 
  | LocalDel (t, v, e)->  printType t ^ v ^ " = " ^ printExpr e
  | Call (name, elist) -> name ^ "(" ^ print_real_Param elist ^ ")"
  | Assign (v, e) -> v ^ " = " ^ printExpr e
  | Seq (e1, e2) -> printExpr e1 ^ ";" ^ printExpr e2
  | EventRaise (ev,None) -> ev
  | EventRaise (ev,Some n) -> ev ^"(" ^string_of_int n ^")"

  | IfElse (e1, e2, e3) -> "if " ^ printExpr e1 ^ " then " ^ printExpr e2 ^ " else " ^ printExpr e3 
  | Cond (e1, e2, str) -> printExpr e1 ^ str ^ printExpr e2 
  | BinOp (e1, e2, str) -> printExpr e1 ^ str ^ printExpr e2 
  | Assertion eff -> "Assert: " ^ "string_of_timedEff eff "

  | TAssertion tEff -> "Timed Assert: " ^ string_of_timedEff tEff
  | Deadline constrains -> "Deadline: " ^ string_of_cocons constrains
  | Reset c ->  "Reset: " ^ List.fold_left (fun acc a -> acc ^ " "^ a) "" c 
  | Delay n -> "Delay " ^ string_of_int n
  | Triple (a, b, c) -> "Triple: <" ^ a ^"," ^string_of_cocons b ^"," ^ List.fold_left (fun acc a -> acc ^ " "^ a) "" c ^">"

  ;;


let rec printSpec (s:prepost ) :string = 
  let helper (sp:spec) : string =  
    match sp with 
      PEFF eff -> string_of_timedEff eff 
    | EFFCALL (mn, c)->  mn ^ List.fold_left (fun acc a -> acc ^ " "^ a) "" c 
  in 
  match s with 
  (e1, e2) -> "\n[Pre: " ^ helper e1 ^ "]\n[Post:"^ helper e2 ^"]\n"
 
 ;;


let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"
;;

let rec concatEffEs (eff:t_effect) (es:t_es) : t_effect = 
  match eff with 
    TEff (p,e) -> TEff (p, TCons (e, es))
  | TDisj (eff1, eff2) -> TDisj ((concatEffEs eff1 es), (concatEffEs eff2 es))
  ;; 
 

let rec concatEffEff (eff1:t_effect) (eff2:t_effect) : t_effect = 
  match eff1 with 
    TEff (p1,e1) -> 
      (match eff2 with
        TEff (p2,e2) -> TEff (PureAnd(p1,p2) , TCons(e1, e2))
      | TDisj (ef1, ef2) -> TDisj ((concatEffEff eff1 ef1), (concatEffEff eff1 ef2))
      )
  | TDisj (ef1, ef2) -> 
      (match eff2 with
        TEff (p2,e2) -> TDisj ((concatEffEff ef1 eff2), (concatEffEff ef2 eff2))
      | TDisj (_, _ ) -> TDisj ((concatEffEff ef1 eff2), (concatEffEff ef2 eff2))
      
      )


      ;;

let rec searMeth (prog: program) (name:string) : meth option= 
  match prog with 
    [] -> None
  | x::xs -> 
    (match x with 
      Include str -> searMeth xs name
    | Method ( t, mn , list_parm,  (pre, post), expression) -> 
      if mn = name then Some ( t, mn , list_parm,  (pre, post), expression)
      else searMeth xs name 
    | Predicate _ -> searMeth xs name
    )
    ;;



let rec substitutePureWithAgr (pi:pure) (realArg:expression) (formalArg: var):pure = 
  match pi with 
    TRUE -> pi 
  | FALSE ->pi
  | Gt (term, n) ->  Gt (substituteTermWithAgr term realArg formalArg, n)
  | Lt (term, n) ->  Lt (substituteTermWithAgr term realArg formalArg, n)
  | GtEq (term, n) ->  GtEq (substituteTermWithAgr term realArg formalArg, n)
  | LtEq (term, n) ->  LtEq (substituteTermWithAgr term realArg formalArg, n)
  | Eq (term, n) ->  Eq (substituteTermWithAgr term realArg formalArg, n)
  | PureOr (p1, p2) -> PureOr (substitutePureWithAgr p1 realArg formalArg, substitutePureWithAgr p2 realArg formalArg)
  | PureAnd (p1, p2) -> PureAnd (substitutePureWithAgr p1 realArg formalArg, substitutePureWithAgr p2 realArg formalArg)
  | Neg p -> Neg (substitutePureWithAgr p realArg formalArg)
  ;;


let rec substituteEffWithAgr (eff:t_effect) (realArg:expression) (formalArg: var):t_effect = 
  match eff with 
    TEff (pi, es) -> TEff (substitutePureWithAgr pi realArg formalArg, t_substituteESWithAgr es realArg formalArg)
  | TDisj (eff1, eff2) -> TDisj (substituteEffWithAgr eff1 realArg formalArg, substituteEffWithAgr eff2 realArg formalArg)
  ;;

let substituteEffWithAgrs (eff:t_effect) (realArgs: expression list) (formal: (_type * var) list ) =
  let realArgs' = List.filter (fun x -> 
                                match x with 
                                Unit -> false 
                              | _-> true ) realArgs in 

  let formalArgs = List.map (fun (a, b) -> b) formal in 
  let pairs = List.combine realArgs' formalArgs in 
  let rec subArgOnebyOne (eff:t_effect) (pairs:(expression * var ) list): t_effect = 
    (match pairs with 
      [] -> eff 
    | (realArg, formalArg):: xs  -> 
      let subThisPair = substituteEffWithAgr eff realArg formalArg in
      subArgOnebyOne subThisPair xs 
    )
  in subArgOnebyOne eff pairs;;



(*n >0 /\ A^n  -> n = 2 /\ n > 0 /\ A^n
let substituteEffWithPure (eff:t_effect) (realArgs: expression list) (formal: (_type * var) list ) =
    let exprToTerm (ex:expression):terms = 
      match ex with 
        Integer num -> Number num
      | _ -> print_string (printExpr ex^"\n");
      raise (Foo "substituteEffWithPure");
    in 
    let realArgs' = List.filter (fun x -> 
                                match x with 
                                Unit -> false 
                              | _-> true ) realArgs in 
    let formalArgs = List.map (fun (a, b) -> b) formal in 
    let pairs = List.combine realArgs' formalArgs in 
    let constrains = List.map (fun (a, b) -> Eq (Var b, exprToTerm a )) pairs in 

    let consNew = List.fold_right (fun con acc -> PureAnd (acc, con ) ) (constrains) TRUE in 
    t_addConstrain eff consNew
    ;;

*)

let checkPrecondition (state:t_effect) (pre:t_effect)  = 
  let reverseState =  (t_reverseEff state) in
  let reversePre =  (t_reverseEff pre) in 
  (*check containment*)
  let (result_tree, result, states, hypo) =  printReportHelper reverseState reversePre false in 
  let tree = Node (string_of_TimedEntailmentEff reverseState reversePre, [result_tree]) in

  if result == false then 
  let printTree = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  print_string printTree;
  (result, tree)

  else 
  
  (result, tree);;

let condToPure (expr :expression) :pure = 
  match expr with 
    Cond (Variable v, Integer n, "==")  -> Eq (Var v, Number n)
  | Cond (Variable v, Integer n, "<=")  -> PureOr(Eq (Var v, Number n),Lt (Var v, Number n))
  | Cond (Variable v, Integer n, ">=")  -> PureOr(Eq (Var v, Number n),Gt (Var v, Number n))
  | Cond (Variable v, Integer n, ">")  -> Gt (Var v, Number n)
  | Cond (Variable v, Integer n, "<")  -> Lt (Var v, Number n)
  | _ -> raise (Foo "exception in condToPure")
  ;;

let rec verifier (caller:string) (expr:expression) (state_H:t_effect) (state_C:t_effect) (prog: program): t_effect = 
  match expr with 
    EventRaise (ev,p) -> concatEffEs state_C (Single (EV ev, CCTop,  []))
  | Deadline cocon  -> concatEffEs state_C (Single (TEmp, cocon,  []))
  | Delay n -> raise (Foo "delay.........\n")

  | Reset c ->  concatEffEs state_C (Single (TEmp, CCTop,  c))
  | Triple (a, b, c)  -> concatEffEs state_C (Single (EV a, b,  c))

  | Seq (e1, e2) -> 
    let state_C' = verifier caller e1 state_H state_C prog in 
    verifier caller e2 state_H state_C' prog
  | Assign (v, e) -> verifier caller e state_H state_C prog 
  | LocalDel (t, v , e) ->   verifier caller e state_H state_C prog      
  | IfElse (e1, e2, e3) -> 
    let condIf = condToPure e1 in 
    let condElse = Neg condIf in 
    let state_C_IF  = t_addConstrain state_C condIf in 
    let state_C_ELSE  = t_addConstrain state_C condElse in 
    TDisj ((verifier caller e2 state_H state_C_IF prog), (verifier caller e3 state_H state_C_ELSE prog))
  | TAssertion eff ->   
    let his_cur =  (concatEffEff state_H state_C) in 
    let (result, tree) = checkPrecondition (his_cur) eff in 
    if result == true then state_C 
    else raise (Foo ("TimedAssertion " ^ string_of_timedEff eff ^" does not hold!"))
            
  | Call (name, exprList) -> 
    (match searMeth prog name with 
      None -> 
       if (String.compare name "printf" == 0) then state_C
       else raise (Foo ("Method: "^ name ^" not defined!"))
    | Some me -> 
      (

        match me with 
         (t, mn , list_parm, (PEFF pre, PEFF post), expression) -> 
          
            let subPre = substituteEffWithAgrs pre exprList list_parm in 
            let subPost = substituteEffWithAgrs post exprList list_parm in 
            (*
            let subPre = substituteEffWithPure pre exprList list_parm in 
            let subPost = substituteEffWithPure post exprList list_parm in 
*)
            let his_cur =  (concatEffEff state_H state_C) in 

            let (result, tree) = checkPrecondition (his_cur) subPre in 
            (*print_string ((printTree ~line_prefix:"* " ~get_name ~get_children tree));*)
            
            if result == true then 
              (
                (*print_string ("[Precondition holds] when " ^caller ^" is calling " ^ mn ^"\n\n");*)
              let newState = ( (concatEffEff ( state_C) ( subPost))) in
              newState)
            else 
            
            raise (Foo ("PreCondition does not hold when " ^ caller^" is calling: "^ name ^"!"))
            
        | _ -> raise (Foo "verifier: should replce the effects call! \n")
      )
    )
  | _ -> state_C
    ;;

let rec extracPureFromPrecondition (eff:t_effect) :t_effect = 
  match eff with 
    TEff (pi, es) -> TEff (pi, ESEMP)
  | TDisj (eff1, eff2) -> TDisj (extracPureFromPrecondition eff1, extracPureFromPrecondition eff2)
  ;;



let substituteEffectCallAgr eff formalArgs realArgs: t_effect = 
  let rec subTESwithEvent (es:t_es) (f) (r) :t_es = 
    match es with 
    | Single (ev, b, c) ->
    (
      match ev with 
      TEmp -> es 
    | EV str -> if String.compare str f == 0 then Single (EV r, b, c) else es

    )
    | TCons (es1, es2) -> TCons (subTESwithEvent es1 f r, subTESwithEvent es2 f r)
    | TOr (es1, es2) -> TOr (subTESwithEvent es1 f r, subTESwithEvent es2 f r)
    | TNtimes (es1, t) -> TNtimes (subTESwithEvent es1 f r, t)
    | TKleene (es1) -> TKleene (subTESwithEvent es1 f r)
    | TNot (es1) -> TNot (subTESwithEvent es1 f r)
    | _ -> es 
  in

  let rec helper (acc:t_effect) (formal) (real) :t_effect = 
    match acc with 
      TEff (pi, es) ->  TEff (pi, subTESwithEvent es formal real)
    | TDisj (eff1, eff2) -> TDisj (helper eff1 formal real, helper eff2 formal real)  
  in 
  let pairs = List.combine formalArgs realArgs in 
  List.fold_left (fun acc (f, r) -> helper acc f r) eff pairs

;;


let rec substituteEffectCall (mn, cList) (prog: program):t_effect = 
    match prog with 
      [] -> raise (Foo ("predicate "^ mn ^" is not defined!\n"))
    | x ::xs  -> 
    (
      match x with 
        Predicate (name, varL, eff) ->
          if String.compare name mn == 0 then   
            substituteEffectCallAgr eff varL cList
            
          else substituteEffectCall (mn, cList)  xs 
      | _ -> substituteEffectCall (mn, cList)  xs 
    )
  ;;

let rec verification (decl:(bool * declare)) (prog: program) : string = 
  let (isIn, dec) = decl in 
  if isIn == false then ""
  else 
  let startTimeStamp = Sys.time() in
  match dec with 
    Include str -> ""
  | Predicate _ -> ""
  | Method  (t, mn , list_parm, (PEFF pre, PEFF post), expression) -> 
    let head = "[Verification for method: "^mn^"]\n"in 
    let precon = "[Precondition: "^(string_of_timedEff ( pre)) ^ "]\n" in
    let postcon = "[Postcondition: "^ (string_of_timedEff ( post)) ^ "]\n" in 
    let acc =  (verifier mn expression (pre) (extracPureFromPrecondition pre) prog) in 
    
    let accumulated = "[Real TEff: " ^(string_of_timedEff ( normalTimedEffect acc )) ^ "]\n" in 
    (*print_string((showEntailmentEff acc post) ^ "\n") ;*)
    
    (*let varList = (*append*) (getAllVarFromEff acc) (*(getAllVarFromEff post)*) in  
    *)
    let (result_tree, result, states, hypos) =  printReportHelper acc post false in 
    let result = "[Result: "^ (if result then "Succeed" else "Fail") ^"]\n" in 
    let states = "[Explored "^ string_of_int (states+1)  ^ " States]\n" in 
    let verification_time = "[Verification Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in
    let printTree = printTree ~line_prefix:"* " ~get_name ~get_children result_tree in
    "=======================\n"^ head ^ precon ^ accumulated ^ postcon ^ result ^ states ^verification_time^ "\n" ^ printTree ^ "\n" 
  | Method  (t, mn , list_parm, (EFFCALL (name, cList), post), expression) -> 
    let temp = substituteEffectCall (name, cList) prog in 
    verification (isIn, Method  (t, mn , list_parm, (PEFF temp, post), expression)) prog

  | Method  (t, mn , list_parm, (pre, EFFCALL (name, cList)), expression) -> 
    let temp = substituteEffectCall (name, cList) prog in 
    verification (isIn, Method  (t, mn , list_parm, (pre, PEFF temp), expression)) prog

 ;;

let rec printMeth (me:meth) :string = 
  match me with 
   (t, mn , list_parm, (pre, post), expression) -> 
    let p = printType t ^ mn^ "(" ^ printParam list_parm ^ ") "^ printSpec ( (pre, post))^"{"^ printExpr expression ^"}\n" in
    p 
    ;;

let rec printProg (pram: declare list) :string =
  match pram with 
    [] -> ""
  | x::xs -> 
    let str = (match x with 
              Include str -> str ^ "\n" 
            | Method me -> printMeth me 
            | Predicate (name, (varList), t_eff) ->  
              let parms = List.fold_left (fun acc a -> acc ^ ","^ a) "" varList  in 
              name ^ " (" ^ parms ^") = " ^ string_of_timedEff  t_eff
              )in 
          
    str ^ printProg xs ;;

let getIncl (d:declare) :bool = 
  match d with 
    Include str -> (String.compare str "primitives.c") != 0
  | _ -> false 
  ;;



let rec getIncludedFiles (p:(bool * declare) list) :(bool * declare) list = 
  let readFromFile (name:string):(bool * declare) list  = 
    let currentP = split_on_char '/' (Sys.getcwd ()) in 
    let serverOrNot = List.exists (fun a -> String.compare a "cgi-bin" == 0) currentP in 

    let inputfile = if serverOrNot then (Sys.getcwd () ^ "/../src/program/" ^ name) 
                    else (Sys.getcwd () ^ "/src/program/" ^ name) 
    in
    let ic = open_in inputfile in
    try 
      let lines =  (input_lines ic ) in  
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in 
      let raw_prog = List.map (fun a -> (false, a)) (Parser.prog Lexer.token (Lexing.from_string line)) in
      let prog = getIncludedFiles raw_prog in 
  
      close_in ic;                  (* 关闭输入通道 *) 
      prog
    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)
  in 
  let incl = List.filter (fun (ind, x) -> getIncl x) (p) in 
  let getName:(string list ) = List.map (fun (ind, x) -> 
                              match x with 
                              Include str -> str
                            | _ -> "") incl in
  let appendUp  = List.fold_right (fun (x) acc -> append (readFromFile x) acc ) (getName) p in 
 
  appendUp;;


let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let raw_prog = List.map (fun a -> (true, a)) (Parser.prog Lexer.token (Lexing.from_string line)) in
      let prog = getIncludedFiles raw_prog in

      (*
      let testprintProg = printProg (List.map (fun (a, b) -> b ) prog) in 
      print_string testprintProg;
*)
      
      let evn = List.map (fun (ind, a) -> a) prog in
      let verification_re = List.fold_right (fun dec acc -> acc ^ (verification dec evn)) prog ""  in
      
      (*let oc = open_out outputfile in    (* 新建或修改文件,返回通道 *)
      (*      let startTimeStamp = Sys.time() in*)
      (*fprintf oc "%s\n" verification_re;   (* 写一些东西 *)*)
      print_string (verification_re ^"\n");
      (*print_string (string_of_float(Sys.time() -. startTimeStamp)^"\n" );*)
      close_out oc;                (* 写入并关闭通道 *)
      *)
      print_string (verification_re ^"\n");
      
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
