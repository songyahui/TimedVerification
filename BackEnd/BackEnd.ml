open Ast
open Printf
open Askz3
open String
open Pretty
open TimedRewriting 
open List





let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) ((*List.rev*) lines) "" in
      let raw_prog = Parser.t_entailment_p Lexer.token (Lexing.from_string line) in

      let prove_re = List.fold_right (fun (lhs, rhs) acc -> acc ^ (printReport lhs rhs false)) raw_prog ""  in
      (*let oc = open_out outputfile in    (* 新建或修改文件,返回通道 *)
      (*      let starTNtimestamp = Sys.time() in*)
      (*fprintf oc "%s\n" verification_re;   (* 写一些东西 *)*)
      print_string (verification_re ^"\n");
      (*print_string (string_of_float(Sys.time() -. starTNtimestamp)^"\n" );*)
      close_out oc;                (* 写入并关闭通道 *)
      *)
      print_string (prove_re ^"\n");
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;