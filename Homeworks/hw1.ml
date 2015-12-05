(* A parser and evaluator for a toy boolean language
   Some defs set up for expansion to NB = boolean + arith language
   EXERCISE:  expand parser+evaluator to NB. Both small-step and
              big-step evaluator.
*)

(*
 *
 * concrete syntax:
 * tm --> if tm then tm else tm|true|false
 *
 *typical concrete syntax:
 *  if (if true then false) then false else
    (if true then false else (if true then false else false))


 * abstract syntax:
 * tm --> TmTrue|TmFalse|TmIf(tm,tm,tm)
 *
 * when extended to system (NB):
 * tm --> TmTrue|TmFalse|TmIf(tm,tm,tm)|TmZero|TmSucc(tm)|
 *        TmPred(tm)|TmIsZero(tm)
 *)

(* utility functions *)

(* converts a string to a list of chars: stolen from SML because it's so handy *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

(* list of chars to string *)
let implode l =
  let res = String.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l;;

(* print a list of strings *)
let rec aux_print_list = function
  |[] -> print_string ""
  |(x::xs) -> (print_string x;print_string ":";aux_print_list xs);;

let print_list x =
  (print_string "<";aux_print_list x;print_string ">");;

(* boolean + arithmetical terms *)
type term =
    TmTrue
  |TmFalse
  |TmIf of (term * term * term)
  |TmZero
  |TmSucc of term
  |TmPred of term
  |TmIsZero of term
  |TmError


(* lexer: breaks up a string into a list of tokens:
   "if true then false else (if true then false else true)" |-->
   ["if";"true";"then";"false";"else";"(";"if";"true";...]
*)

(* char x is alphabetical *)
let alph x =
  let n = Char.code x in
  96< n && n < 122;;


exception BAD_CHAR;;


(* token boundaries *)
let bdry x = (x='(') || (x= ')') || (x = '0');;

(* accumulate characters until you reach a blank or a token boundary:
'e' ['l';'s';'e';'(';...] |--> ("else" ['('...])
 *)
let rec grab_chars_until_bdry ch rest =
  match rest with
    |[] -> (String.make 1 ch,rest)
    |(head::tail) ->
       if (head = ' ')
       then (String.make 1 ch,tail)
       else if (bdry head)
       then (String.make 1 ch,rest)
       else let (x,l) = (grab_chars_until_bdry head tail)
       in
	 ((String.make 1 ch)^x,l)
;;

(* char list |--> list of token strings *)
let rec aux_lexx chars =
  match chars with
    |[] -> []
    |(ch::rest) ->
       if (ch=' ')
       then aux_lexx rest
       else if (bdry ch)
       then (String.make 1 ch)::(aux_lexx rest)
       else if (alph ch)
       then
	 let (str, remainder) = grab_chars_until_bdry ch rest
	 in str::(aux_lexx remainder)
       else raise BAD_CHAR;;

(* explode input and aux_lexx it *)
let lexx x = aux_lexx (explode x);;


(* parser *)
(*
 * parse applies aux_parse to result of lexx.
 * aux_parse: string list -> term * string list
 * aux_parse calls aux_parse_subterm
 * which checks for parentheses and identifiers and
 * calls aux_parse on de-parenthesized terms
 *)
(* aux_parse : string list -> term * string list = <fun> *)
let rec   aux_parse tokens = (* parse if..then..else terms *)
  match tokens with
    |[] -> (TmError,[])
    |("if"::rest) ->
      let (t1, rest1) = aux_parse_subterm rest in
      let (tok_then::rest_then) = rest1 in (* throw away then *)
      let (t2, rest2) = aux_parse_subterm rest_then in
      let (tok_else::rest_else) = rest2 in (* throw away else *)
      let (t3,rest3) = aux_parse_subterm rest_else
      in (TmIf (t1,t2,t3),rest3)
    |("succ"::rest) ->
        let(t1, rest1) = aux_parse_subterm rest
        in (TmSucc(t1),rest1)
    |("pred"::rest) ->
        let(t1, rest1) = aux_parse_subterm rest
        in (TmPred(t1),rest1)
    |("iszero"::rest) ->
        let(t1, rest1) = aux_parse_subterm rest
        in (TmIsZero(t1),rest1)
      |x ->aux_parse_subterm x
and
    aux_parse_subterm tokens =
  match tokens with
    |[] -> (TmError,[])
    |("("::rest) ->
      let (tm, remainder) = aux_parse rest in
      let (tok_rparen::remainder_after_rparen) = remainder in
	(tm,remainder_after_rparen) (* throw away right parenthesis *)
    |("true"::tokens_rest) -> (TmTrue,tokens_rest)
    |("false"::tokens_rest) -> (TmFalse,tokens_rest)
    |("0"::tokens_rest) -> (TmZero,tokens_rest)
    |x -> ((print_list (["x = "]@x)); (TmError, []));; (* debug errors *)


(* parse:string -> term *)
let parse str =  fst (aux_parse (lexx str));;

(*** evaluation ***)

(* identify which terms are values *)
let rec is_a_numeric_value x =
  match x with
    |TmZero -> true
    |TmSucc(x1) -> is_a_numeric_value x1
    |x -> false;;

let is_a_value x =
   match x with
   |TmTrue -> true
   |TmFalse -> true
   |x -> is_a_numeric_value x

exception NO_RULE;;

(* single small step eval EXPAND TO INCLUDE arithmetic *)
let rec eval_step t =
  match t with
  |TmIf(TmTrue,t2,t3) -> t2
  |TmIf(TmFalse,t2,t3) -> t3
  |TmIf(t1,t2,t3) ->
     let t1' = eval_step t1 in
       TmIf(t1',t2,t3)
  |TmIsZero(TmZero) -> TmTrue
  |TmIsZero(TmSucc t1) -> if is_a_numeric_value t1 then TmFalse else let t1' =
    eval_step(TmSucc t1) in TmIsZero(t1')
  |TmIsZero(t1) -> let t1' = eval_step t1 in TmIsZero(t1')
  |TmSucc(t1) -> let t1' = eval_step t1 in TmSucc(t1')
  |TmPred(TmZero) -> TmZero
  |TmPred(TmSucc t1) -> if is_a_numeric_value t1 then t1 else let t1' = eval_step (TmSucc t1) in TmPred(t1')
  |TmPred(t1) -> let t1' = eval_step t1 in TmPred(t1')
  |_ -> raise NO_RULE;;

(* and the evaluation sequences it induces *)
let rec eval t =
  if (is_a_value t)
  then t
  else let t' = eval_step t in
    eval t';;


(* example of use

eval (parse "if (if (if true then false else (if true then false else true)) then true else false) then false else true");;
- : term = TmTrue

*)

(* big step *)

exception NO_GUARD (* if statement without a condition *)

let rec big_step t =
  match t with
    |TmTrue -> TmTrue
    |TmFalse -> TmFalse
    |TmZero -> TmZero
    |TmError -> TmError
    |TmIf(t1,t2,t3) ->
       let t2' = big_step t2 in
       if (big_step t1 = TmTrue)
       then t2'
       else
	 let t3' = big_step t3 in
	 if (big_step t1 = TmFalse)
	 then t3'
	 else raise NO_GUARD
    |TmIsZero(t1) -> let t1' = big_step t1 in
      (match t1' with
        |TmZero -> TmTrue
        |TmSucc(t1'') -> if is_a_numeric_value t1'' then TmFalse else raise
        NO_RULE
        |_ -> raise NO_RULE)
    |TmSucc(t1) -> let t1' = big_step t1 in if is_a_numeric_value t1' then
      TmSucc(t1') else raise NO_RULE
    |TmPred(t1) -> let t1' = big_step t1 in
      (match t1' with
        |TmZero -> TmZero
        |TmSucc(t1'') -> if is_a_numeric_value t1'' then t1'' else raise NO_RULE
        |_ -> raise NO_RULE)
