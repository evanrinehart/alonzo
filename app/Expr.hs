module Expr where

import Ty

import Data.Char
import Data.List

data Expr =
    Var String |
    Star |
    TT |
    FF |
    Pair Expr Expr |
    Fst Expr |
    Snd Expr |
    L Expr |
    R Expr |
    Case Expr Expr Expr | -- incomplete
    App Expr Expr |
    Lam String Expr |
    LamA String Ty Expr
        deriving (Show, Read)

-- x
-- ()
-- true
-- false
-- (e, e)
-- #0 e
-- #1 e
-- L e
-- R e
-- case e {L x -> e; R y -> e}
-- e e
-- \x -> e
-- \x : ty -> e

trim :: String -> String
trim (c:cs) = if isSpace c then trim cs else c:cs
trim "" = ""

whitespace :: Parser ()
whitespace input = [((), trim input)]

isReserved :: String -> Bool
isReserved word =
    word `elem` ["case", "true", "false", "L", "R"]

type Parser a = String -> [(a, String)]

isVarChar :: Char -> Bool
isVarChar c = c=='_' || isAlphaNum c

isInitialVarChar :: Char -> Bool
isInitialVarChar c = c=='_' || isAlphaNum c

variable :: Parser Expr
variable "" = []
variable (c:more) =
    if isInitialVarChar c
        then
            let (cs, rest) = span isVarChar more in
            if isReserved (c:cs)
                then []
                else [(Var (c:cs), trim rest)]
        else []

star :: Parser Expr
star ('(':')':more) = [(Star, trim more)]
star _ = []

true :: Parser Expr
true ('t':'r':'u':'e':more) = [(TT, trim more)]
true _ = []

false :: Parser Expr
false ('f':'a':'l':'s':'e':more) = [(FF, trim more)]
false _ = []

arrow :: Parser ()
arrow ('-':'>':more) = [((), trim more)]
arrow _ = []

proj0 :: Parser Int
proj0 ('#':'0':more) = [(0, trim more)]
proj0 _ = []

proj1 :: Parser Int
proj1 ('#':'1':more) = [(1, trim more)]
proj1 _ = []

oneOf :: [Parser a] -> Parser a
oneOf [] _ = []
oneOf (p:ps) input = case p input of
    [] -> oneOf ps input
    success -> success

char :: Char -> Parser Char
char _ "" = []
char wanted (c:cs)
    | c == wanted = [(c, cs)]
    | otherwise   = []

string :: String -> Parser ()
string wanted input = case stripPrefix wanted input of
    Just rest -> [((), rest)]
    Nothing   -> []

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p k input = p input >>= \(x, rest) -> k x rest

parens :: Parser Expr
parens =
    char '(' `bind` \_ ->
    whitespace `bind` \_ ->
    expr `bind` \e ->
    char ')' `bind` \_ ->
    whitespace `bind` \_ ->
    (\input -> [(e, input)])

pair :: Parser Expr
pair =
    char '(' `bind` \_ ->
    whitespace `bind` \_ ->
    expr `bind` \e1 ->
    char ',' `bind` \_ ->
    whitespace `bind` \_ ->
    expr `bind` \e2 ->
    char ')' `bind` \_ ->
    whitespace `bind` \_ ->
    (\input -> [(Pair e1 e2, input)])

applyProj :: Parser Expr
applyProj =
    oneOf [proj0, proj1] `bind` \n ->
    whitespace `bind` \_ ->
    expr `bind` \e ->
    (\input -> [(if n==0 then Fst e else Snd e, input)])

applyInj :: Parser Expr
applyInj =
    oneOf [char 'L', char 'R'] `bind` \c ->
    whitespace `bind` \_ ->
    expr `bind` \e ->
    (\input -> [(if c=='L' then L e else R e, input)])

primary :: Parser Expr
primary = oneOf [lamA, lam, caseExp, applyInj, applyProj, pair, true, false, variable, star, parens]

lam :: Parser Expr
lam =
    char '\\' `bind` \_ ->
    whitespace `bind` \_ ->
    variable `bind` \(Var x) ->
    whitespace `bind` \_ ->
    arrow `bind` \_ ->
    whitespace `bind` \_ ->
    expr `bind` \e ->
    (\input -> [(Lam x e, input)])

lamA :: Parser Expr
lamA =
    char '\\' `bind` \_ ->
    whitespace `bind` \_ ->
    variable `bind` \(Var x) ->
    whitespace `bind` \_ ->
    char ':' `bind` \_ ->
    whitespace `bind` \_ ->
    parseTy `bind` \t ->
    arrow `bind` \_ ->
    whitespace `bind` \_ ->
    expr `bind` \e ->
    (\input -> [(LamA x t e, input)])

caseExp :: Parser Expr
caseExp = 
    string "case" `bind` \_ ->
    whitespace `bind` \_ ->
    expr `bind` \e1 ->
    char '{' `bind` \_ ->
    whitespace `bind` \_ ->
    string "L x ->" `bind` \_ ->
    whitespace `bind` \_ ->
    expr `bind` \e2 ->
    char ';' `bind` \_ ->
    whitespace `bind` \_ ->
    string "R y ->" `bind` \_ ->
    whitespace `bind` \_ ->
    expr `bind` \e3 ->
    char '}' `bind` \_ ->
    whitespace `bind` \_ ->
    \input -> [(Case e1 e2 e3, input)]

chainl :: (a -> a -> a) -> Parser a -> Parser a
chainl comb p input = start where
    go accum more = case p more of
        [] -> [(accum, more)]
        [(y, rest)] -> go (comb accum y) rest
    start = case p input of
        [] -> []
        [(x, rest)] -> go x rest

expr :: Parser Expr
expr = chainl App primary

parseExpr :: String -> Either String Expr
parseExpr input = case expr input of
    (e, ""):_ -> Right e
    (e, more):_ -> Left ("parseExpr: unexpected " ++ take 10 more)
    [] -> Left "parseExpr: no parse"
