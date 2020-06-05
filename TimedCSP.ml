open Ast
open Printf
open Askz3
open String
open Pretty

(*
let a = Event (Str "A");;
let test = EventPre (Str "A", Stop);;
let testltl = Until (a, 5, a);;
let testltl1 = Finally (5, a);;
*)

let rec t_containment (effL:t_effect) (effR:t_effect) (delta:t_hypotheses) (mode:bool) : (binary_tree * bool * int * t_hypotheses) = 
  (*
    print_string (string_of_int (List.length delta)^"\n");
  let startTimeStamp = Sys.time() in



  let normalFormL = normalEffect effL 0 in 
  let normalFormR = normalEffect effR 0 in

  let verification_time = "[normalEffect Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in

  print_string (verification_time);
  
  
  let varList = getAllVarFromEff normalFormL in 
  let showEntail  = (*showEntailmentEff effL effR ^ " ->>>> " ^*) showEntailmentEff normalFormL normalFormR in 

in 
*)
(Node ("TESTING",[] ), true, 1, delta) 
;;

let printReportHelper lhs rhs (mode:bool): (binary_tree * bool * int * t_hypotheses) = 
  (*
  let delta = getProductHypo lhs rhs in 
    let varList = append (getAllVarFromEff lhs) (getAllVarFromEff rhs) in  
  let varList = getAllVarFromEff lhs in  

  *)

  t_containment lhs rhs [] mode
  ;;





let printReport lhs rhs (mode:bool):string =
  let startTimeStamp = Sys.time() in
  let (tree, re, states, hypo) =  printReportHelper lhs rhs mode in
  let verification_time = "[Verification Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let states = "[Explored "^ string_of_int (states) ^ " States]\n" in 
  let buffur = ( "===================================="^"\n" ^(string_of_TimedEntailmentEff lhs rhs)^"\n[Result] " ^(if re then "Succeed\n" else "Fail\n") ^ states ^verification_time^" \n\n"^ result)
  in buffur
  ;;

let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let raw_prog = Parser.t_entailment_p Lexer.token (Lexing.from_string line) in

      let prove_re = List.fold_right (fun (lhs, rhs) acc -> acc ^ (printReport lhs rhs false)) raw_prog ""  in
      (*let oc = open_out outputfile in    (* 新建或修改文件,返回通道 *)
      (*      let startTimeStamp = Sys.time() in*)
      (*fprintf oc "%s\n" verification_re;   (* 写一些东西 *)*)
      print_string (verification_re ^"\n");
      (*print_string (string_of_float(Sys.time() -. startTimeStamp)^"\n" );*)
      close_out oc;                (* 写入并关闭通道 *)
      *)
      print_string (prove_re ^"\n");
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;