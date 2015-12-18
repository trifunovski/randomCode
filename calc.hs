-- Haskell Student Forum Final Project: Calculator with an Environment of variables
-- You first input the environment as a set of bindings "x=0,y=2,z=3,w=-6"
-- Then you input your equation such that you put every pair of numbers and an operator
-- inside of parenthesis, example ((2+x)-y)
-- Then the program parses the environment and the equation and tries to match
-- the variables from the environment to the equation variables and evaluate as
-- much as it can.
-- Maksim Trifunovski

import Data.Maybe
import System.IO
import Control.Monad

data Exp = Add Exp Exp | Sub Exp Exp | Mul Exp Exp | Div Exp Exp | And Exp Exp
  | Or Exp Exp | Not Exp | Eq Exp Exp | Less Exp Exp | Greater Exp Exp
  | If Exp Exp Exp | Num Int | Bool Bool | Var String
  deriving (Eq, Show)

data Token =   TokAdd
             | TokSub
             | TokMul
             | TokDiv
             | TokNot
             | TokAnd
             | TokOr
             | TokLess
             | TokGreater
             | TokEq
             | TokIf
             | TokLParen
             | TokRParen
             | TokVar String
             | TokNum Int
             | TokBool Bool
             | TokComma
      deriving (Show, Eq)

isVal :: Exp -> Bool
isVal (Num _) = True
isVal (Bool _) = True
isVal (Var _) = True
isVal x = let x' = oper x in if x==x' then True else False

type Env = [(String, Exp)]

oper :: Exp -> Exp
oper (Add ((Num a)) ((Num b))) = (Num (a+b))
oper (Add ((Var x)) ((Var y))) | x == y = Mul ((Num 2)) ((Var x))
oper (Add (Mul (Num a) (Var x)) (Var y)) | x==y = Mul (Num (a+1)) (Var x)
oper (Add (Var y) (Mul (Num a) (Var x))) | x==y = Mul (Num (a+1)) (Var x)
oper (Add t1 t2) = (Add (oper t1) (oper t2))
oper (Sub ( (Num a)) ( (Num b))) = (Num (a-b))
oper (Sub ((Var x)) ((Var y))) | x == y = (Num 0)
oper (Sub t1 t2) = (Sub (oper t1) (oper t2))
oper (Mul ( (Num a)) ( (Num b))) = (Num (a*b))
oper (Mul t1 t2) = (Mul (oper t1) (oper t2))
oper (Div ( (Num a)) ( (Num b))) | b /= 0 = (Num (div a b))
                                 | otherwise = error "Division by zero"
oper (Div t1 t2) = (Div (oper t1) (oper t2))
oper (If ((Bool True)) t1 t2) = oper t1
oper (If ((Bool False)) t1 t2) = oper t2
oper (If t0 t1 t2) = let t0' = oper t0 in (If t0' t1 t2)
oper (And (Bool True) (Bool True)) = (Bool True)
oper (And (Bool True) t2) = let t2' = oper t2 in (And (Bool True) t2')
oper (And (Bool False) (_)) = (Bool False)
oper (And t1 t2) = let t1' = oper t1 in (And t1' t2)
oper (Or (Bool True) _) = (Bool True)
oper (Or (Bool False) t2) = let t2' = oper t2 in (And (Bool False) t2')
oper (Or _ (Bool True)) = (Bool True)
oper (Or t1 t2) = let t1' = oper t1 in (Or t1' t2)
oper (Not (Bool True)) = (Bool False)
oper (Not (Bool False)) = (Bool True)
oper (Not t1) = (Not (oper t1))
oper (Eq (Num x) (Num y)) = Bool (x == y)
oper (Eq t1 t2) = (Eq (oper t1) (oper t2))
oper (Less (Num x) (Num y)) = Bool (x < y)
oper (Less t1 t2) = (Less (oper t1) (oper t2))
oper (Greater (Num x) (Num y)) = Bool (x > y)
oper (Greater t1 t2) = (Greater (oper t1) (oper t2))
oper x = x

eval' :: Exp -> Exp
eval' op = let res = oper op in
           if isVal res then res else eval' res

eval :: Env -> Exp -> Exp
eval e op = eval' (subs e op)

applyS :: Env -> Exp -> Exp
applyS e (Var x) = find e x
applyS e oth = subs e oth

bimapMe :: (Exp -> Exp) -> Exp -> Exp
bimapMe f (Add t1 t2) = Add (f t1) (f t2)
bimapMe f (Sub t1 t2) = Sub (f t1) (f t2)
bimapMe f (Mul t1 t2) = Mul (f t1) (f t2)
bimapMe f (Div t1 t2) = Div (f t1) (f t2)
bimapMe f (And t1 t2) = And (f t1) (f t2)
bimapMe f (Or t1 t2) = Or (f t1) (f t2)
bimapMe f (Not t1) = Not (f t1)
bimapMe f (Eq t1 t2) = Eq (f t1) (f t2)
bimapMe f (Less t1 t2) = Less (f t1) (f t2)
bimapMe f (Greater t1 t2) = Greater (f t1) (f t2)
bimapMe f (If t1 t2 t3) = If (f t1) (f t2) (f t3)
bimapMe f (Num x) = Num x

subs :: Env -> Exp -> Exp
subs e ex = bimapMe (applyS e) ex

find :: Env -> String -> Exp
find [] s = (Var s)
find ((x,v):xs) s | (x == s) =  v
                  | otherwise = find xs s

t0 = (Add (Add (Var "x") (Var "x")) ((Var "y")))
t1 = (Sub (Mul (Add (Var "x") (Add (Var "x") (Var "x"))) (Num 4)) (Div (Var "y") (Num 2)))
tTest = (Mul (Add (Var "x") (Add (Var "x") (Var "x"))) (Num 4))
e0 = [("x",(Num 2)), ("y", (Num 3))]

expression :: Char -> Token
expression c | c == '+' = TokAdd
           | c == '-' = TokSub
           | c == '*' = TokMul
           | c == '/' = TokDiv
           | c == '!' = TokNot
           | c == '&' = TokAnd
           | c == '|' = TokOr
           | c == '<' = TokLess
           | c == '=' = TokEq
           | c == '>' = TokGreater
           | c == ',' = TokComma

isDigit :: Char -> Bool
isDigit c | (c >= '0') && (c <= '9') = True
          | otherwise = False

isAlpha :: Char -> Bool
isAlpha c | (c >= 'a') && (c <= 'z') = True
          | otherwise = False

isSpace :: Char -> Bool
isSpace c = c == ' '

isAlphaNum :: Char -> Bool
isAlphaNum c = ((isAlpha c) || (isDigit c))

identifier :: Char -> String -> [Token]
identifier c cs = let (name, cs') = span isAlphaNum cs in
                  TokVar (c:name) : tokenize cs'

number :: Char -> String -> [Token]
number c cs =
  let (digs, cs') = span isDigit cs in TokNum (read (c : digs)) : tokenize cs'

tokenize :: String -> [Token]
tokenize [] = []
tokenize (c : cs)
    | elem c "+-*/!<>=," = (expression c) : tokenize cs
    | c == '('  = TokLParen : tokenize cs
    | c == ')'  = TokRParen : tokenize cs
    | isDigit c = number c cs
    | isAlpha c = identifier c cs
    | isSpace c = tokenize cs
    | otherwise = error $ "Cannot tokenize " ++ [c]

runParse :: [Token] -> Int -> ([Token], [Token])
runParse [] _ = error "Can't parse"
runParse (t : ts) n
  | t == TokRParen = if n==1 then ([],ts) else let (ex, rest) = runParse ts (n-1) in (t:ex, rest)
  | t == TokLParen = let (ex, rest) = runParse ts (n+1) in (t:ex, rest)
  | otherwise = let (ex, rest) = runParse ts n in (t:ex, rest)

op :: Token -> (Exp -> Exp -> Exp)
op c       | c == TokAdd = Add
           | c == TokSub = Sub
           | c == TokMul = Mul
           | c == TokDiv = Div
           | c == TokAnd = And
           | c == TokOr  = Or
           | c == TokLess = Less
           | c == TokEq  = Eq
           | c == TokGreater = Greater

getExp :: [Token] -> Exp
getExp [] = error "Can't expressionize"
getExp (t : ts) = case t of
   TokLParen -> let (ex1, re) = runParse ts 1
                     in if re == [] then (getExp ex1)
                     else let (r:rest) = re in
                     if r==TokNot then Not (getExp ex1) else (op(r)) (getExp ex1) (getExp rest)
   TokBool x -> if ts==[] then (Bool x) else let (r:rest) = ts
                    in if r==TokNot then Not (Bool x) else (op(r)) (Bool x) (getExp rest)
   TokNum x -> if ts/=[] then let (r:rest) = ts in (op(r)) (Num x) (getExp rest) else (Num x)
   TokVar x -> if ts/=[] then let (r:rest) = ts in (op(r)) (Var x) (getExp rest) else (Var x)
   _ -> error "can't expressionize"

parse :: [Token] -> Exp
parse [] = error "Can't parse"
parse (t : ts)
  | t == TokLParen = let (ex, rest) = runParse ts 1 in getExp ex
  | otherwise = error "bad string"

parseComma :: [Token] -> ([Token], [Token])
parseComma [] = ([], [])
parseComma (TokComma:rest) = ([], rest)
parseComma (r:rest) = let (p1, p2) = parseComma rest in (r:p1, p2)

parseEnv :: [Token] -> Env
parseEnv [] = []
parseEnv ((TokVar x):(TokEq):rest) = let (bind, rest1) = parseComma rest in [(x,getExp(bind))] ++ (parseEnv rest1)
parseEnv _ = error "bad environment"

toString :: Exp -> String
toString (Add t1 t2) = "("++(toString t1)++"+"++(toString t2)++")"
toString (Sub t1 t2) = "("++(toString t1)++"-"++(toString t2)++")"
toString (Mul t1 t2) = "("++(toString t1)++"*"++(toString t2)++")"
toString (Div t1 t2) = "("++(toString t1)++"/"++(toString t2)++")"
toString (If t1 t2 t3) = "(if "++(toString t1)++" then "++(toString t2)++" else "++(toString t3)++")"
toString (And t1 t2) = "("++(toString t1)++"&"++(toString t2)++")"
toString (Or t1 t2) = "("++(toString t1)++"|"++(toString t2)++")"
toString (Not t1) = "(!"++(toString t1)++")"
toString (Eq t1 t2) = "("++(toString t1)++"="++(toString t2)++")"
toString (Less t1 t2) = "("++(toString t1)++"<"++(toString t2)++")"
toString (Greater t1 t2) = "("++(toString t1)++">"++(toString t2)++")"
toString (Var a) = a
toString (Bool a) = show a
toString (Num a) = show a

main = do
  putStrLn "Enter your equation using parenthesis around each operator of 2 terms:"
  equation <- getLine
  putStrLn "Enter your environment in the format x=0,y=2,z=3"
  environment <- getLine
  putStrLn (toString (eval (parseEnv(tokenize environment)) (parse(tokenize equation))))
