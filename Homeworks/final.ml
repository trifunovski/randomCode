(* Maksim Trifunovski, Narin Luangrath, Irma Mazariego *)
exception UNIMPLEMENTED
exception BAD_STRING
exception UNIFICATION_FAILURE

(* lexing *)
  (* Depending on how you define the lexer you may not need to bother with commas *)
type token_tag =
  | VAR
  | CONST
  | FUN
  | COMMA
  | LPAREN
  | RPAREN

type term =
  | Const of string
  | Var of string
  | Fun of string * term list

type substitution = (string * term) list

(* Utility functions *)
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

let alph x =
  let n = Char.code x in
  (96< n && n < 122);;

let varN x =
  let n = Char.code x in
   (64<n && n <91);;

let bdry x = (x='(') || (x= ')') || (x = ',');;

(* accumulate characters until you reach a blank or a token boundary:
'e' ['l';'s';'e';'(';...] |--> ("else" ['('...])
 *)
let rec grab_chars_until_bdry ch rest =
  match rest with
    |[] -> (String.make 1 ch,rest,' ')
    |(head::tail) ->
       if (head = ' ')
       then (String.make 1 ch,tail,' ')
       else if (bdry head)
       then (String.make 1 ch,rest, head)
       else let (x,l,bdy) = (grab_chars_until_bdry head tail)
       in
   ((String.make 1 ch)^x,l,bdy)
;;

(* char list |--> list of token strings *)
let rec aux_lexx chars =
  match chars with
    |[] -> []
    |(ch::rest) ->
       if (ch=' ')
       then aux_lexx rest
       else if (ch='(')
       then ("(",LPAREN)::(aux_lexx rest)
       else if (ch=')')
       then (")",RPAREN)::(aux_lexx rest)
       else if (ch=',')
       then (",",COMMA)::(aux_lexx rest)
       else if (varN ch)
       then let (str, remainder, _) = grab_chars_until_bdry ch rest
            in (str,VAR)::(aux_lexx remainder)
       else if (alph ch)
       then let (str, remainder, bdy) = grab_chars_until_bdry ch rest
            in (if bdy = '('
                then (str,FUN)::(aux_lexx remainder)
                else (str,CONST)::(aux_lexx remainder))
       else raise BAD_STRING;;

(* FINISH UTILITY FUNCTIONS *)

let lex (inp : string) : (string * token_tag) list = aux_lexx(explode inp)

let rec get_until_rparen l cnt : (((string * token_tag) list) * ((string *
token_tag) list)) =
  match l with
  |((str,RPAREN)::rest) -> if cnt=0 then ((str,RPAREN)::[],rest)
                           else if cnt<0 then raise BAD_STRING
                           else let (ans, rest2) = get_until_rparen rest (cnt-1)
                                in (((str,RPAREN)::ans), rest2)
  |((str,tag)::rest) -> if tag=LPAREN then let (ans,rest2) = get_until_rparen rest (cnt+1)
                                           in (((str,tag)::ans),rest2)
                        else let (ans,rest2) = get_until_rparen rest cnt
                             in (((str,tag)::ans),rest2)
  |_ -> raise BAD_STRING

let rec aux_parse (tkns : (string * token_tag) list) : term =
  match tkns with
  |((str,VAR)::[]) -> Var str
  |((str,CONST)::[]) -> Const str
  |((str,FUN)::(_,LPAREN)::(str2,tag)::rest) -> if tag=RPAREN
                                                then raise BAD_STRING
                                                else Fun (str, aux_parse_list ((str2,tag)::rest))
  |_ -> raise BAD_STRING
and
  aux_parse_list (rest : (string * token_tag) list) : term list =
    match rest with
    |((_,RPAREN)::[]) -> []
    |((_,COMMA)::(str,tag)::rest2) -> if (tag=LPAREN || tag=RPAREN ||
    tag=COMMA) then raise BAD_STRING else
      aux_parse_list ((str,tag)::rest2)
    |((str,VAR)::rest2) -> (Var str)::(aux_parse_list rest2)
    |((str,CONST)::rest2) -> (Const str)::(aux_parse_list rest2)
    |((str,FUN)::(str2,LPAREN)::rest2) -> let (arg,rest3) = get_until_rparen
    rest2 0 in (aux_parse ((str,FUN)::(str2,LPAREN)::arg))::(aux_parse_list rest3)
    |_ -> raise BAD_STRING


let parse (inp : string) : term = aux_parse (lex inp)

let rec occurs_inList (str : string) (l : term list) : bool =
  match l with
   |[] -> false
   |(x::xs) -> (occurs_free str x) || (occurs_inList str xs)
and occurs_free (str : string) (tm : term) : bool =
  match tm with
   |Var str2 -> str=str2
   |Const _ -> false
   |Fun (str2,tm2) -> occurs_inList str tm2

let rec apply_substitutionInList (s : substitution) (l : term list) : term list =
  match l with
   |[] -> []
   |(x::xs) -> (apply_substitution s x)::(apply_substitutionInList s xs)
and apply_substitution (s : substitution) (tm : term) : term =
  match s with
    |[] -> tm
    |((str,t)::rest) -> (match tm with
                          |Var str2 -> if str=str2 then t else apply_substitution rest tm
                          |Fun (str2, t2) -> Fun(str2, apply_substitutionInList s t2)
                          |_ -> tm)

let rec apply_subsList (s : substitution) (tml : substitution) : substitution =
  match tml with
    |[] -> []
    |((str,tm)::terms) -> (str,(apply_substitution s tm))::(apply_subsList s terms)

let rec isIn ((str,tm) : string*term) (f : substitution) : bool =
  match f with
    |[] -> false
    |(str2,tm2)::rest -> if str=str2 then true else isIn (str,tm) rest

let rec getOthers (g : substitution) (f : substitution) : substitution =
  match g with
    |[] -> []
    |sub::rest -> if isIn sub f then (getOthers rest f) else sub::(getOthers rest f)

let rec removeDups (s : substitution) : substitution =
match s with
  |[] -> []
  |(str,(Var m))::rest -> if str=m then removeDups rest else (str,(Var m))::(rest)
  |(str,tm)::rest -> (str,tm)::(removeDups rest)

let compose_substitution (g : substitution) (f : substitution) : substitution =
  removeDups((apply_subsList g f) @ (getOthers g f))

let rec unifyHelperList (tm0 : term list) (tm1 : term list) (s : substitution) : substitution =
  match (tm0,tm1) with
    |([],[]) -> []
    |((t1::t1s),(t2::t2s)) -> let newSub = unifyHelper t1 t2 s
                              in
                              compose_substitution
                              (unifyHelperList (apply_substitutionInList newSub t1s)
                              (apply_substitutionInList newSub t2s) newSub)
                              newSub
    |(_,_) -> raise UNIFICATION_FAILURE
and unifyHelper (tm0 : term) (tm1 : term) (s : substitution) : substitution =
  if tm0 = tm1 then s
  else
    match (tm0, tm1) with
    |(Var x, tm1) when not (occurs_free x tm1) -> compose_substitution ([(x,tm1)]) s
    |(tm0, Var y) when not (occurs_free y tm0) -> compose_substitution ([(y,tm0)]) s
    |((Fun (s0,t0)),(Fun (s1,t1))) when s0=s1 -> unifyHelperList t0 t1 s
    |_ -> raise UNIFICATION_FAILURE


let unify_terms (tm0 : term) (tm1 : term) : substitution =
  unifyHelper tm0 tm1 []


let rec toStringList (l : term list) : string =
  match l with
  |[] -> ""
  |x::[] -> toStringTm x
  |x::rest -> (toStringTm x)^","^(toStringList rest)
and toStringTm (tm : term) : string =
  match tm with
  |Var x -> x
  |Const x -> x
  |Fun (str, t) -> str^"("^(toStringList(t))^")"

let rec toString (s : substitution) : string =
  match s with
    |[] -> "}"
    |(var,tm)::[] -> (toStringTm(tm))^"/"^var^"}"
    |(var,tm)::rest -> (toStringTm(tm))^"/"^var^","^(toString rest)

let unify (x : string) (y : string) : string = "{"^(toString (unify_terms
  (parse x) (parse y)))
