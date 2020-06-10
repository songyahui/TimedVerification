open Ast
open Printf
open Askz3
open String
open Pretty
open List


let rec getAllVarFromTerm term = 
  match term with 
    Var str -> [str]
  | Number _ -> []
  | Plus (t1, t2) -> List.append (getAllVarFromTerm t1) (getAllVarFromTerm t2)
  | Minus (t1, t2) -> List.append (getAllVarFromTerm t1) (getAllVarFromTerm t2)
  ;;

let rec getAllVarFromPi (pi:pure): string list  = 
    match pi with 
      TRUE -> []
    | FALSE -> []
    | Gt (t1, t2) -> List.append (getAllVarFromTerm t1) (getAllVarFromTerm t2)
    | Lt (t1, t2) -> List.append (getAllVarFromTerm t1) (getAllVarFromTerm t2)
    | GtEq (t1, t2) -> List.append (getAllVarFromTerm t1) (getAllVarFromTerm t2)
    | LtEq (t1, t2) -> List.append (getAllVarFromTerm t1) (getAllVarFromTerm t2)
    | Eq (t1, t2) -> List.append (getAllVarFromTerm t1) (getAllVarFromTerm t2)
    | PureOr (p1, p2) -> List.append (getAllVarFromPi p1) (getAllVarFromPi p2)
    | PureAnd (p1, p2) -> List.append (getAllVarFromPi p1) (getAllVarFromPi p2)
    | Neg p1 -> getAllVarFromPi p1
;;


let rec getAllVarFromTimedES (tes:t_es) = 
  match tes with
  | TNtimes (_, Var s) -> [s]
  | TNtimes (_, Plus (Var s, _ )) -> [s]
  | TNtimes (_, Minus (Var s, _ )) -> [s]
  | TCons (es1, es2) -> List.append (getAllVarFromTimedES es1 ) (getAllVarFromTimedES es2 ) 
  | TOr (es1, es2) -> List.append (getAllVarFromTimedES es1 ) (getAllVarFromTimedES es2 ) 
  | TKleene (esIn) -> getAllVarFromTimedES esIn
  | _ -> []
  ;;

let rec getAllVarFromTimedEff (eff:t_effect): string list = 
  match eff with 
  | TEff (pi, es) -> getAllVarFromTimedES es
  | TDisj (eff1, eff2) -> List.append (getAllVarFromTimedEff eff1) (getAllVarFromTimedEff eff2)
;;

let rec t_splitDisj (p:pure) (es:t_es):t_effect =
  match p with 
    PureOr (p1, p2) -> TDisj (t_splitDisj p1 es , t_splitDisj p2 es ) 
  | _ -> TEff (p, es) 
  ;;

let rec normalPureToDisj (p:pure):pure = 
  match p with 
    PureAnd (p1, PureOr(pIn1, pIn2)) ->  
      let dealP1 = normalPureToDisj p1 in
      let temp1 = normalPureToDisj (PureAnd(dealP1, pIn1)) in 
      let temp2 = normalPureToDisj (PureAnd(dealP1, pIn2)) in 
      PureOr (temp1 , temp2 )
  | PureAnd (PureOr(pIn1, pIn2), p2) ->  
      let dealP2 = normalPureToDisj p2 in
      let temp1 = normalPureToDisj (PureAnd(dealP2, pIn1)) in 
      let temp2 = normalPureToDisj (PureAnd(dealP2, pIn2)) in 
      PureOr (temp1 , temp2 )
  | Neg pi -> Neg (normalPureToDisj pi)
  | _ -> p
  ;;

let rec deletePureOrInTEff (eff:t_effect):t_effect = 
  match eff with 
    TEff (pi, es) -> 
      let disjPure = normalPureToDisj pi in
      t_splitDisj disjPure es 
  | TDisj (eff1, eff2) -> TDisj ((deletePureOrInTEff eff1), (deletePureOrInTEff eff2))
  ;;

let rec stricTcompareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> String.compare s1 s2 == 0
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | _ -> false 
  ;;

let rec comparePure (pi1:pure) (pi2:pure):bool = 
  match (pi1 , pi2) with 
    (TRUE, TRUE) -> true
  | (FALSE, FALSE) -> true 
  | (Gt (t1, t11), Gt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Lt (t1, t11), Lt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (GtEq (t1, t11), GtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (LtEq (t1, t11), LtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Eq (t1, t11), Eq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (PureOr (p1, p2), PureOr (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (PureAnd (p1, p2), PureAnd (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (Neg p1, Neg p2) -> comparePure p1 p2
  | _ -> false
  ;;

let rec getAllPi piIn acc= 
    (match piIn with 
      PureAnd (pi1, pi2) -> List.append (getAllPi pi1 acc ) (getAllPi pi2 acc )
    | _ -> List.append acc [piIn]
    )
    ;;

let rec existPi pi li = 
    (match li with 
      [] -> false 
    | x :: xs -> if comparePure pi x then true else existPi pi xs 
    )
    ;;

let rec coconToPure (co:cocon) :pure = 
  match co with 
    CCTop -> TRUE
  | CCBot -> FALSE
  | CCLT (clock, num) -> Lt (Var clock, Number num)
  | CCLTEQ (clock, num) -> LtEq (Var clock, Number num)
  | CCGT (clock, num) -> Gt (Var clock, Number num)
  | CCGTEQ (clock, num) -> GtEq (Var clock, Number num)
  | CCAND (cocon1, cocon2) -> PureAnd (coconToPure cocon1, coconToPure cocon2)
  ;;

let entailConstrains pi1 pi2 = 

  let sat = not (askZ3 (Neg (PureOr (Neg pi1, pi2)))) in
  (*
  print_string (showPure pi1 ^" -> " ^ showPure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat;;

let rec normalPure (pi:pure):pure = 
  let allPi = getAllPi pi [] in
  let rec clear_Pi pi li = 
    (match li with 
      [] -> [pi]
    | x :: xs -> if existPi pi li then clear_Pi x xs else List.append [pi] (clear_Pi x xs)
    )in 
  let finalPi = clear_Pi TRUE allPi in
  let rec connectPi li acc = 
    (match li with 
      [] -> acc 
    | x :: xs -> if entailConstrains TRUE x then (connectPi xs acc) else PureAnd (x, (connectPi xs acc)) 
    ) in 
  let filte_true = List.filter (fun ele-> not (comparePure ele TRUE)  ) finalPi in 
  if length filte_true == 0 then  TRUE
  else connectPi (tl filte_true) (hd filte_true)
  ;;


let rec normalTES (es:t_es) (pi:pure) mode:t_es = 
  match es with
  | TCons (TCons (esIn1, esIn2), es2)-> normalTES (TCons (esIn1, TCons (esIn2, es2))) pi mode
  | TCons (es1, es2) -> 
      let normalES1 = normalTES es1 pi mode in
      let normalES2 = normalTES es2 pi mode in
      (match (normalES1, normalES2) with 
        (ESEMP, _) -> normalES2 
      | (_, ESEMP) -> normalES1
      | (Nil, _) -> Nil

      (*
      | (TKleene (esIn1), TKleene (esIn2)) -> 
          if aCompareTES esIn1 esIn2 == true then normalES2
          else TCons (normalES1, normalES2)
      | (TKleene (esIn1), TCons(TKleene (esIn2), es2)) -> 
          if aCompareTES esIn1 esIn2 == true then normalES2
          else TCons (normalES1, normalES2) 
*)
      | (normal_es1, normal_es2) -> 
        if mode == 1 then 
        (
        match (normal_es1, normal_es2) with 
        (*|  (TCons (esIn1, esIn2), es2)-> normalTES (TCons (esIn1, TCons (esIn2, es2))) pi *)
        (*|  (TOr (or1, or2), es2) ->  (TOr (normalTES  (TCons (or1, es2)) pi mode,  normalTES (TCons (or2, es2)) pi mode)) *)
        |  (es1, TOr (or1, or2)) -> normalTES (TOr ( (TCons (es1, or1)),  (TCons (es1, or2)))) pi mode
        | _-> TCons (normal_es1, normal_es2)
        )
        else TCons (normal_es1, normal_es2)
      ;)
  | TOr (es1, es2) -> 
      (match (normalTES es1 pi mode, normalTES es2 pi mode) with 
        (Nil, Nil) -> Nil
      | (Nil, norml_es2) -> norml_es2
      | (norml_es1, Nil) -> norml_es1
      (*
      | (TOr(es1In, es2In), norml_es2 ) ->
        if aCompareTES norml_es2 es1In || aCompareTES norml_es2 es2In then TOr(es1In, es2In)
        else TOr (TOr(es1In, es2In), norml_es2 )
      | (norml_es2, TOr(es1In, es2In) ) ->
        if aCompareTES norml_es2 es1In || aCompareTES norml_es2 es2In then TOr(es1In, es2In)
        else TOr (norml_es2, TOr(es1In, es2In))
        *)
      | (ESEMP, TKleene norml_es2) ->  TKleene norml_es2
      | (TKleene norml_es2, ESEMP) ->  TKleene norml_es2

      | (norml_es1, norml_es2) -> 
      TOr (norml_es1, norml_es2)
      (*
        if aCompareTES  norml_es1 norml_es2 == true then norml_es1
        else 
        (match (norml_es1, norml_es2) with
          (norml_es1, TKleene norml_es2) ->  
          if aCompareTES norml_es1 norml_es2 == true then TKleene norml_es2
          else TOr (norml_es1, TKleene norml_es2)
        | (TKleene norml_es2, norml_es1) ->  
          if aCompareTES norml_es1 norml_es2 == true then TKleene norml_es2
          else TOr (TKleene norml_es2, norml_es1)
        |  _-> TOr (norml_es1, norml_es2)
        )
    
      ;)
          *))

          (*
  | TNtimes (es1, terms) -> 

      let t = normalTerms terms in 
      let normalInside = normalTES es1 pi mode in 
      (match normalInside with
        ESEMP -> ESEMP
      | _ -> 
        let allPi = getAllPi pi [] in 
        if (existPi (Eq (terms, Number 0)) allPi) then ESEMP else 
          match t with
            Number num -> concertive normalInside num 
          | _ -> TNtimes (normalInside, t))
        (*else if (existPi (Eq (terms, n)) allPi)) then ESEMP else TNtimes (normalInside, t))*)
 *)
  | TKleene es1 -> 
      let normalInside = normalTES es1 pi mode in 
      (match normalInside with
        ESEMP -> ESEMP
      | TKleene esIn1 ->  TKleene (normalTES esIn1 pi mode)
      | TOr(ESEMP, aa) -> TKleene aa
      | _ ->  TKleene normalInside)

  | _-> es
  ;;

type rule = LHSOR   | RHSOR 
          | LHSEX   | RHSEX 
          | LHSSUB  | RHSSUB 
          | LHSCASE | RHSCASE 
          | UNFOLD  | DISPROVE 
          | FRAME   | REOCCUR
          | RHSAND


let rec compareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> true
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | _ -> false 
  ;;

let rec subsetOf (small : string list) (big : string list) :bool = 
  let rec oneOf a set :bool = 
    match set with 
      [] -> false 
    | y:: ys -> if String.compare a y == 0 then true else oneOf a ys
  in 
  match small with 
    [] -> true 
  | x :: xs -> if oneOf x big == false then false else subsetOf xs big
;;

let rec compareTimedES es1 es2 = 
  match (es1, es2) with 
    (Nil, Nil) -> true
  | (ESEMP, ESEMP) -> true
  | (Single tran1, Single tran2) ->
  (
    match (tran1, tran2) with 
      ( (TEmp, c1, re1),  (TEmp, c, re)) ->  if comparePure (coconToPure c1) (coconToPure c) && subsetOf re re1 && subsetOf re1 re  then true else false
    | ( (EV ev1, c1, re1),  (EV ev, c, re)) -> if String.compare ev1 ev == 0 && comparePure (coconToPure c1) (coconToPure c) && subsetOf re re1 && subsetOf re1 re then true else false
    | _ -> false
  )
  | (TCons (es1L, es1R), TCons (es2L, es2R)) -> (compareTimedES es1L es2L) && (compareTimedES es1R es2R)
  | (TOr (es1L, es1R), TOr (es2L, es2R)) -> 
      let one = ((compareTimedES es1L es2L) && (compareTimedES es1R es2R)) in
      let two =  ((compareTimedES es1L es2R) && (compareTimedES es1R es2L)) in 
      one || two
  | (TNtimes (esL, termL), TNtimes (esR, termR)) -> 
      let insideEq = (compareTimedES esL esR) in
      let termEq = compareTerm termL termR in
      insideEq && termEq
  | (TKleene esL, TKleene esR) -> compareTimedES esL esR
  | (TAny, TAny ) -> true
  | _ -> false
;;

let showRule (r:rule):string = 
  match r with
    LHSOR -> " [LHSOR] "
  | RHSAND -> " [RHSAND] "
  | RHSOR -> " [RHSOR] "
  | LHSEX -> " [LHSEX] "  
  | RHSEX -> " [RHSEX] " 
  | LHSSUB -> " [LHSSUB] "
  | RHSSUB -> " [RHSSUB] "
  | LHSCASE -> " [LHSCASE] "
  | RHSCASE -> " [RHSCASE] "
  | UNFOLD  -> " [UNFOLD] "
  | DISPROVE -> " [DISPROVE] "
  | FRAME  -> " [FRAME] "
  | REOCCUR -> " [REOCCUR] "

let rec compareTimedEff eff1 eff2 =
  match (eff1, eff2) with
  | (TEff(FALSE, _ ), TEff(FALSE, _)) -> true 
  | (TEff(FALSE, _ ), TEff(_, Nil )) -> true 
  | (TEff(_, Nil), TEff(FALSE, _ )) -> true 
  | (TEff(_, Nil ), TEff(_, Nil)) -> true 

 (* | (TEff (pi1, es1), TEff (pi2, es2 )) -> compareTimedES es1 es2*)
  | (TDisj (eff11, eff12), TDisj (eff21, eff22)) -> 
      let one =  (compareTimedEff eff11  eff21) && (compareTimedEff eff12  eff22) in
      let two =  (compareTimedEff eff11  eff22) && (compareTimedEff eff12  eff21 ) in
      one || two
  | _ -> false
  ;;

let rec normalTimedEffect (eff:t_effect) :t_effect =

  
  let noPureOr  = deletePureOrInTEff eff in 
  match noPureOr with
  | TEff (p, es) -> 
      if (askZ3 p) == false then 
        ( 
          (*print_string (showPure p^"   "^ showES es^ "\n 11********\n");*)
          TEff (FALSE, es)
        )
      else 
        let p_normal = normalPure p in 
        let es_normal  = normalTES es p 0 in
        (match es_normal with 
          TOr (es_nor1, es_nor2) -> TDisj (TEff (p_normal, es_nor1), TEff (p_normal, es_nor2))
        | _ -> TEff ( p_normal, es_normal)
        )
  | TDisj (eff1, eff2) -> 
      let normaedEff1 = normalTimedEffect eff1  in 
      let normaedEff2 = normalTimedEffect eff2  in 
      match (normaedEff1, normaedEff2 ) with
        (TEff (_,  Nil  ), _) -> normaedEff2
      | (_, TEff (_,  Nil)) -> normaedEff1
      | (TEff (FALSE,  _), _) -> normaedEff2
      | (_, TEff (FALSE,  _)) -> normaedEff1

      | (TDisj(eff1In, eff2In), norml_eff2 ) ->
        if compareTimedEff norml_eff2 eff1In || compareTimedEff norml_eff2 eff2In then TDisj(eff1In, eff2In)
        else TDisj (TDisj(eff1In, eff2In), norml_eff2 )
      | (norml_eff2, TDisj(eff1In, eff2In) ) ->
        if compareTimedEff norml_eff2 eff1In || compareTimedEff norml_eff2 eff2In then TDisj(eff1In, eff2In)
        else TDisj (norml_eff2, TDisj(eff1In, eff2In))

      | _ -> TDisj (normaedEff1, normaedEff2)
      
  ;;

let rec sublist b e l = 
  if b > e then [] else 
  match l with
    [] -> raise (Foo  "sublist")
  | h :: t -> 
     let tail = if e=0 then [] else sublist (b-1) (e-1) t in
     if b>0 then tail else h :: tail
;;

let rec t_nullable (pi :pure) (es:t_es) : bool=
  match es with
    Nil -> false
  | ESEMP -> true 
  | Single tran -> false
  | TCons (es1 , es2) -> (t_nullable pi es1) && (t_nullable pi es2)
  | TOr (es1 , es2) -> (t_nullable pi es1) || (t_nullable pi es2)
  | TNtimes (es1, t) -> askZ3 (PureAnd (pi, Eq (t, Number 0))) 
  | TKleene es1 -> true
  | TAny -> false
  |  TNot es1 -> not (t_nullable pi es1)
  ;;

let rec t_checkNullable (eff:t_effect):bool = 
  match eff with 
    TEff (pi, es) -> t_nullable pi es
  | TDisj (eff1, eff2) -> t_checkNullable eff1 || t_checkNullable eff2 
;;

let rec t_fst (pi :pure) (es:t_es): (t_trans) list = 
  match es with
    Nil -> []     
  | ESEMP -> []
  | Single trans -> [trans]
  | TNtimes (es1, t) -> t_fst pi es1
  | TCons (es1 , es2) ->  if t_nullable pi es1 then List.append (t_fst pi es1) (t_fst pi es2) else t_fst pi es1
  | TOr (es1, es2) -> append (t_fst pi es1) (t_fst pi es2)
  | TAny -> [( (EV "_", CCTop,  []))]
  | TKleene es1 -> t_fst pi es1
  | TNot es1 -> t_fst pi es1
;;

let rec t_checkFst (eff:t_effect) : t_trans list = 
  match eff with
    TEff (pi, es) -> t_fst pi es
  | TDisj (eff1, eff2) -> append (t_checkFst eff1) (t_checkFst eff2) 
 ;;



let rec t_t_appendEff_ES eff es = 
  match eff with 
    TEff (p , es_eff) ->  TEff(p, TCons (es_eff, es))
  | TDisj (eff1 , eff2)  ->  TDisj (t_t_appendEff_ES eff1 es, t_t_appendEff_ES eff2 es)
  
  (*raise ( Foo "t_appendEff_ES exception!")*)
  ;;

let t_ifShouldDisj (temp1:t_effect) (temp2:t_effect) : t_effect = 
  match (temp1, temp2) with
      (TEff(pure1, evs1), TEff(pure2, evs2)) -> 
        if comparePure pure1 pure2 then  TEff (pure1, TOr (evs1, evs2))
        else TDisj (temp1, temp2 )
      | _ -> 
      TDisj (temp1, temp2 )
  ;;

let rec t_appendEff_ES eff es = 
  match eff with 
    TEff (p , es_eff) ->  TEff(p, TCons (es_eff, es))
  | TDisj (eff1 , eff2)  ->  TDisj (t_appendEff_ES eff1 es, t_appendEff_ES eff2 es)
  
  (*raise ( Foo "t_appendEff_ES exception!")*)
  ;;
 

let rec t_derivative (p :pure) (es:t_es) (varL: var list) (tran:t_trans): (t_effect) =
  match es with (*es is the current*)
    Nil -> TEff (p,  Nil)
  | ESEMP -> TEff (p,  Nil)
  | Single tran1 ->
  (
    match (tran1, tran) with 
      ( (TEmp, c1, re1),  (TEmp, c, re)) ->  if entailConstrains (coconToPure c1) (coconToPure c) && subsetOf re re1 then TEff (p, ESEMP) else TEff (p,  Nil)
    | ( (EV ev1, c1, re1),  (EV ev, c, re)) -> if String.compare ev1 ev == 0 && entailConstrains (coconToPure c1) (coconToPure c) && subsetOf re re1 then TEff (p, ESEMP) else TEff (p,  Nil)
    | _ -> TEff (p,  Nil)
  )
  | TAny -> TEff (p, ESEMP)
  | TOr (es1 , es2) -> 
    let temp1 =  (t_derivative p es1 varL tran) in
    let temp2 =  (t_derivative p es2 varL tran) in 
    normalTimedEffect (t_ifShouldDisj temp1 temp2) 
  | TNtimes (es1, t) -> 
      let pi = PureAnd (Gt (t, Number 0), p) in
      let efF = t_derivative pi es1 varL tran in 
      let esT_minus1 = TNtimes (es1,  Minus (t, Number 1)) in
      t_t_appendEff_ES efF esT_minus1
  | TCons (es1 , es2) -> 
      if t_nullable p es1 
      then let efF = t_derivative p es1 varL tran in 
          let effL =  (t_appendEff_ES efF es2) in 
          let effR =  (t_derivative p es2 varL tran) in 
          normalTimedEffect (t_ifShouldDisj effL effR) 
      else let efF = t_derivative p es1 varL tran in 
          t_t_appendEff_ES efF es2    
          
  | TKleene es1 -> t_t_appendEff_ES  (t_derivative p es1 varL tran) es
  | TNot es1 -> 
    let der = t_derivative p es1 varL tran in 
    let tryder = normalTimedEffect der in 
    match  tryder with
      TEff (ppp,Nil) ->   TEff (p, TKleene (TAny))
    | TEff (ppp,ESEMP) ->  TEff (ppp,Nil)
    | _ -> 
      (let rec helper (noteffect:t_effect) : t_effect = 
        match noteffect with 
          TEff (pi, esnot) ->  TEff (pi, TNot esnot)
        | TDisj (eff11, eff22) -> TDisj (helper eff11, helper eff22)
      in 
      helper tryder)
  ;;

let rec t_addEntailConstrain (eff:t_effect) (pi:pure) :t_effect = 
  match eff with 
    TEff (pi1, es1)  -> 
      (match entailConstrains pi pi1 with 
        true -> eff
      | false -> TEff (FALSE, es1)
      )
  | TDisj (eff1, eff2) -> TDisj(t_addEntailConstrain eff1 pi, t_addEntailConstrain eff2 pi)
  ;;

let rec t_splitEffects eff : (pure * t_es) list = 
  match eff with 
    TEff (p1, es1) -> [(p1, es1)]
  | TDisj (eff1, eff2) -> List.append (t_splitEffects eff1) (t_splitEffects eff2)
  ;;

let t_effectEntailSyntatically eff1 eff2 :bool =
  let effsL = t_splitEffects eff1 in 
  let effsR = t_splitEffects eff2 in
  let rec checkSingle piL esL liR:bool = 
    match liR with
      [] -> false  
    | (piR, esR)::xs -> if compareTimedES esL esR && (t_nullable piR esR == t_nullable piL esL)then true else checkSingle piL esL xs
  in 
  List.fold_right (fun (piL, esL) acc -> acc && checkSingle piL esL effsR) (effsL) true 
  ;;

let rec t_checkDerivative  (eff:t_effect) (ev:t_trans) (varL :var list): t_effect = 
  match eff with 
    TEff (pi, es) -> t_derivative pi es varL ev
  | TDisj (eff1, eff2) -> TDisj (t_checkDerivative eff1 ev varL, t_checkDerivative eff2 ev varL)
  ;;

let rec t_checkReoccur (effL:t_effect) (effR:t_effect) (delta:t_hypotheses) :bool =
  let checkSingle (hypoL:t_effect) (hypoR:t_effect) = 
    t_effectEntailSyntatically effL hypoL && t_effectEntailSyntatically hypoR effR 
  in 
  match delta with
    [] -> false 
  | (hyL, hyR)::xs -> 
    if checkSingle hyL hyR then true else t_checkReoccur effL effR xs
  ;;

let rec t_headEs (es:t_es) : t_es list =
  match es with
    TCons (es1 , es2) -> t_headEs es1
  | TKleene es1 -> t_headEs es1
  | TNot es1 -> t_headEs es1
  | TOr (es1, es2 ) -> append (t_headEs es1) (t_headEs es2)
  | _ -> [es]
  ;;

let rec isEmpES (es:t_es) :bool = 
  match es with 
    ESEMP -> true 
  | _ -> false 
;;


let rec t_synchronizedReason (eff:t_effect) (s:string): t_effect list = 
  (*print_string (showEffect eff ^"\n" ^s^"\n");*)
  match eff with 
    TEff (pi, es) ->
      let rec helper (inner:t_es) esAcc effListAcc : t_effect list =
        match inner with 
          ESEMP -> 
            if isEmpES esAcc then effListAcc else (TEff(pi, esAcc)::effListAcc)
        | TCons (esIn1, esIn2) -> 
          let temp = if isEmpES esAcc then esIn1 else TCons (esAcc, esIn1) in 
          helper esIn2 temp effListAcc
        | TNtimes (esIn, Var t) -> 
            if String.compare t s == 0 
            then if isEmpES esAcc then helper ESEMP inner effListAcc else helper ESEMP inner (TEff(pi, esAcc)::effListAcc)
            else helper ESEMP (TCons (esAcc, inner)) effListAcc 
        | _ -> helper ESEMP (TCons (esAcc, inner)) effListAcc 
      in 
      helper es ESEMP []
  | TDisj (eff1, eff2) -> raise (Foo (string_of_timedEff eff ^ " t_synchronizedReason"))
  ;;

let rec t_synchronizedPairs (effList1:t_effect list) (effList2:t_effect list) : (t_effect *t_effect) list = 
  List.combine effList1 effList2
  ;;

let rec t_addConstrain effect addPi =
  match effect with
    TEff (pi, eff) -> TEff ( (PureAnd (pi, addPi)), eff)
  | TDisj (effL1, effL2) -> TDisj (t_addConstrain effL1 addPi, t_addConstrain effL2 addPi)
  ;;

let rec t_pattermMatchingTerms terms pattern termNew:terms= 
  if (stricTcompareTerm terms pattern) ==  true then termNew 
  else match terms with 
        Plus (tp, num) -> Plus (t_pattermMatchingTerms tp pattern termNew, num)
      | Minus (tp, num) -> Minus (t_pattermMatchingTerms tp pattern termNew, num)
      | _ -> terms
  ;;

let rec t_substituteES es termOrigin termNew = 
  match es with 
  | TNtimes (es1, term) -> TNtimes (es1,  t_pattermMatchingTerms term termOrigin termNew)
  | TCons (es1, es2) -> TCons (t_substituteES es1 termOrigin termNew ,t_substituteES es2 termOrigin termNew ) 
  | TOr (es1, es2) -> TCons (t_substituteES es1 termOrigin termNew ,t_substituteES es2 termOrigin termNew ) 
  | TKleene (es1) -> TKleene (t_substituteES es1 termOrigin termNew)
  | _ -> es
  ;;

let rec t_substituteEff (effect:t_effect) (termOrigin:terms) (termNew:terms) = 
  match effect with 
    TEff (pi, es) -> TEff (pi, t_substituteES es termOrigin termNew) 
  | TDisj (eff1, eff2) -> TDisj (t_substituteEff eff1 termOrigin termNew , t_substituteEff eff2 termOrigin termNew ) 
  ;;

let rec t_containment (effL:t_effect) (effR:t_effect) (delta:t_hypotheses) (mode:bool) : (binary_tree * bool * int * t_hypotheses) = 


  let normalFormL = normalTimedEffect effL in 
  let normalFormR = normalTimedEffect effR in

  
  
  let varList = getAllVarFromTimedEff normalFormL in 
  
  let showEntail  = string_of_TimedEntailmentEff normalFormL normalFormR in 
  let unfold eff1 eff2 del = 
    let fstL = t_checkFst eff1 in 
    let deltaNew = List.append [(eff1, eff2)] del  in

    let rec chceckResultAND li acc staacc hypoacc:(bool *binary_tree list* int * t_hypotheses)=
      (match li with 
        [] -> (true, acc, staacc, hypoacc ) 
      | ev::fs -> 
          (*print_string ("\n"^string_of_Event ev^"\n\n");
          *)
          let deriL = t_checkDerivative eff1 ev varList in
          let deriR = t_checkDerivative eff2 ev varList in
          let (tree, re, states, hypo) =  t_containment deriL deriR hypoacc mode in 
          if re == false then (false , tree::acc, staacc+states, [])
          else chceckResultAND fs (tree::acc) (staacc+states)  (hypo)
      )
    in 
    let (resultFinal, trees, states, hypy ) = chceckResultAND fstL [] 0 deltaNew in 
    (Node (showEntail ^ "   [UNFOLD]",trees ), resultFinal, states+1, hypy)    
  in 

  match (normalFormL, normalFormR) with 
  (TEff(FALSE, _), _) -> (Node(showEntail ^ "   [Nil-LHS]", []), true, 0, [])  
  | (TEff(_, Nil), _) -> (Node(showEntail ^ "   [Nil-LHS]", []), true, 0, [])  
  | (_, TEff(FALSE, _)) -> (Node(showEntail ^ "   [DISPROVE]", []), false, 0, [])  
  | (_, TEff(_, Nil)) -> (Node(showEntail ^ "   [DISPROVE]", []), false, 0, [])  
  
  | (TDisj (effL1, effL2), _) -> 
    (*[LHSOR]*)
      let (tree1, re1, states1 , hypo ) = (t_containment effL1 effR delta mode) in
      if re1 == false then (Node (showEntail ^ showRule LHSOR, [tree1] ),  false, states1, [])
      else 
        (
        (*print_string ("lallalallalal\n");*)
        let (tree2, re2 , states2, hypo1) = (t_containment effL2 effR (List.append delta (sublist (List.length delta) (List.length hypo -1 ) hypo)) mode) in
        (Node (showEntail ^ showRule LHSOR, [tree1; tree2] ), re2, states1+states2, hypo1)
        )

  (****If worriy of comokenness, need to delete this part. *****)
  | ( _, TDisj (effL1, effL2)) -> 
    (*[RHSOR]*)
      let (tree1, re1, states1, hypo ) = (t_containment normalFormL effL1 delta mode) in
      if re1 == true then (Node (showEntail ^ showRule RHSOR, [tree1] ),  true, states1, hypo)
      else 
        let (tree2, re2 , states2, hypo1) = (t_containment normalFormL effL2  delta mode) in 
        (Node (showEntail ^ showRule RHSOR, [tree2] ), re2, states2, hypo1)
    (****If worriy of comokenness, need to delete this part. *****)

  | (TEff (piL, esL),_) -> 
    if t_checkReoccur normalFormL normalFormR delta then (Node(showEntail ^ "   [Reoccur]", []), true, 0, delta) 
    else if (t_checkNullable normalFormL) == true && (t_checkNullable normalFormR) == false then (Node(showEntail ^ "   [REFUTATION] "  , []), false, 0, []) 

else 


(*there is no extantial var on thr RHS already*)
      let rec chceckSyncAND li acc staacc hypoacc:(bool *binary_tree list* int * t_hypotheses)=
        (match li with 
          [] -> (true, acc, staacc, hypoacc) 
        | (lhs, rhs)::fs -> 
            let (tree, re, states, hypo) =  t_containment lhs rhs delta true in 
            if re == false then (false , tree::acc, staacc+states, List.append  hypoacc hypo)
            else chceckSyncAND fs (tree::acc) (staacc+states) (List.append hypoacc hypo)
        )
      in 
      match List.hd (t_headEs esL) with
          TNtimes (esIn, term) -> 
            (match term with 
              Var s -> 
                let synchronizedLHS = t_synchronizedReason normalFormL s in 
                
                (*print_string (List.fold_left (fun acc a  -> acc ^ showEffect a ^ "\n") ""  synchronizedLHS ^"\n"); 

                print_string (string_of_int (List.length synchronizedLHS)^"\n"); 
                *)
                if List.length (synchronizedLHS) > 1 then 
                  (let synchronizedRHS = t_synchronizedReason normalFormR s in 
                  if List.length (synchronizedLHS) != List.length (synchronizedRHS) 
                  then (Node (showEntail ^"   [SYNC-REASONING-FAIL]",[] ), false, 0, [])
                  else 
                    let syncPairs = t_synchronizedPairs synchronizedLHS synchronizedRHS in
                    let (resultFinal, trees, states, hypo) = chceckSyncAND syncPairs [] 0 delta in 
                    (Node (showEntail ^ "   [SYNC-REASONING]",trees ), resultFinal, states+1, hypo)  
                  )  
                else 
                (match  entailConstrains (Eq (Var s, Number 0) ) piL  with 
                  true -> (*[CASE SPLIT]*) 
                    let zeroCase = PureAnd (piL, Eq (Var s, Number 0) ) in 
                    let nonZeroCase = PureAnd (piL, Gt (Var s, Number 0) ) in 
                    let leftZero =  (t_addConstrain (normalFormL) zeroCase) in
                    let rightZero =  (t_addConstrain (normalFormR) zeroCase) in
                    let leftNonZero =  (t_addConstrain normalFormL nonZeroCase) in
                    let rightNonZero =  (t_addConstrain normalFormR nonZeroCase) in


                    (*zhe li hao xiang ke yi gai*)

                    let (tree1, re1, states1, hypo) = (t_containment leftZero rightZero delta mode) in
                    (match re1 with 
                      false -> (Node (showEntail ^"   [CASE SPLIT]",[tree1] ), re1, states1, [])
                    | true -> let (tree2, re2, states2, hypo1) = (t_containment leftNonZero rightNonZero hypo mode) in
                      (Node (showEntail ^"   [CASE SPLIT]",[tree1;tree2] ), re1&& re2, states1+states2, List.append hypo hypo1)
                    )
                  | false -> (*[UNFOLD]*)unfold normalFormL (t_addEntailConstrain normalFormR piL) delta 
                )
            | Plus  (Var t, num) -> 
            (*[LHSSUB]*)
                let newVar = getAfreeVar varList in 
                let lhs = t_substituteEff normalFormL  (Plus  (Var t, num))  (Var newVar) in
                let rhs = t_substituteEff normalFormR  (Plus  (Var t, num))  (Var newVar) in
                let cons = PureAnd( Eq (Var newVar, Plus (Var t, num) ), GtEq (Var newVar, Number 0)) in
                let lhs' = t_addConstrain lhs cons in 
                let rhs' = t_addConstrain rhs cons in 
                let (tree, re, states, hypo) = t_containment lhs' rhs' delta mode in
                (Node (showEntail ^"   [SUB "^ newVar ^"/" ^ t ^"+1]",[tree] ), re, states, hypo)
            | Minus (Var t, num) -> 
            (*[LHSSUB]*)
                let newVar = getAfreeVar varList in 
                let lhs = t_substituteEff normalFormL  (Minus  (Var t, num)) (Var newVar) in
                let rhs = t_substituteEff normalFormR  (Minus  (Var t, num)) (Var newVar) in
                let cons = PureAnd( Eq (Var newVar, Minus (Var t, num) ), GtEq (Var newVar, Number 0))in
                let lhs' = t_addConstrain lhs cons in 
                let rhs' = t_addConstrain rhs cons in 
                let (tree, re, states, hypo) = t_containment lhs' rhs' delta mode in
                (Node (showEntail ^"   [SUB "^ newVar ^"/" ^ t ^"-1]",[tree] ), re, states, hypo)
            | Number n -> unfold normalFormL (t_addEntailConstrain normalFormR piL) delta 
            | _ -> print_endline (showEntail);
              raise ( Foo "term is too complicated exception1!")
            )
          | _ -> unfold normalFormL (t_addEntailConstrain normalFormR (piL)) delta 
(*Node ("TESTING",[] ), true, 1, delta*) 
;;

let printReportHelper lhs rhs (mode:bool): (binary_tree * bool * int * t_hypotheses) = 
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
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) ((*List.rev*) lines) "" in
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