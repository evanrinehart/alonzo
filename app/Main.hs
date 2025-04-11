module Main where

import System.IO

import Control.Monad

import Ty
import Expr hiding (bind)

data Check a =
    Done a |
    GenNum (Int -> Check a) |
    Fail String

bind :: Check a -> (a -> Check b) -> Check b
bind (Done x) f   = f x
bind (Fail msg) _ = Fail msg
bind (GenNum k) f = GenNum (\i -> k i `bind` f)

instance Functor Check where
    fmap f (Done x)   = Done (f x)
    fmap _ (Fail msg) = Fail msg
    fmap f (GenNum k) = GenNum (fmap (fmap f) k)

instance Monad Check where
    (>>=) = bind

instance Applicative Check where
    pure = Done
    (<*>) = ap

runCheck :: Int -> Check a -> Either String a
runCheck _ (Done x)   = Right x
runCheck _ (Fail msg) = Left msg
runCheck g (GenNum k) = runCheck (g + 1) (k g)

instance MonadFail Check where
    fail = Fail

fresh :: Check Ty
fresh = GenNum (\i -> Done (Alpha i))

unify :: Ty -> Ty -> Check Sub
unify t1 t2 = case mgu t1 t2 of
    Left msg -> Fail msg
    Right s -> return s

infer :: [(String, Ty)] -> Expr -> Check (Sub, Ty)
infer ctx Star = return ([], Unit)
infer ctx TT   = return ([], Bool)
infer ctx FF   = return ([], Bool)
infer ctx (Var x) = case lookup x ctx of
    Just t  -> return ([], t) -- ??
    Nothing -> fail "variable not in scope"

infer ctx (Pair e1 e2) = do
    (s1, t1) <- infer ctx e1
    let ctx' = map (fmap (subAll s1)) ctx
    (s2, t2) <- infer ctx' e2
    return (s1++s2, Cross t1 t2)

infer ctx (Fst e) = do
    (s1,t) <- infer ctx e
    a <- fresh
    b <- fresh
    case mgu t (Cross a b) of
        Right s2 -> do
            let Cross t1 t2 = subAll s2 t
            return (s1++s2, t1)
        Left msg -> fail msg

infer ctx (Snd e) = do
    (s1,t) <- infer ctx e
    a <- fresh
    b <- fresh
    case mgu t (Cross a b) of
        Right s2 -> do
            let Cross t1 t2 = subAll (s1++s2) t
            return (s1++s2, t2)
        Left msg -> fail msg

infer ctx (L e) = do
    (s, t) <- infer ctx e
    beta <- fresh
    return (s, Plus t beta)

infer ctx (R e) = do
    (s, t) <- infer ctx e
    beta <- fresh
    return (s, Plus beta t)

infer ctx (Case e1 e2 e3) = do
    (s1, t1) <- infer ctx e1
    a <- fresh
    b <- fresh
    s2 <- unify t1 (Plus a b)
    let t1' = subAll s2 t1
    let ctx' = map (fmap (subAll (s1++s2))) ctx
    (s3, t2) <- infer (("x", subAll s2 a):ctx') e2
    (s4, t3) <- infer (("y", subAll s2 b):ctx') e3
    s5 <- unify t2 t3
    let t3' = subAll s5 t3
    return (s1++s2++s3++s4++s5, t3')

infer ctx (Lam x body) = do
    beta <- fresh
    (s, t2) <- infer ((x, beta) : ctx) body
    return (s, Arrow (subAll s beta) t2)

infer ctx (LamA x t1 body) = do
    (s, t2) <- infer ((x, t1) : ctx) body
    return (s, Arrow t1 t2)

infer ctx (App e1 e2) = do
    (s1, t1) <- infer ctx e1
    let ctx' = map (fmap (subAll s1)) ctx
    (s2, t2) <- infer ctx' e2
    let t1' = subAll s2 t1
    beta <- fresh
    case mgu t1' (Arrow t2 beta) of
        Right s3 -> return (s1 ++ s2 ++ s3, subAll s3 beta)
        Left msg -> fail msg

f @@ x = App f x
    
eI = Lam "x" (Var "x")
eK = Lam "x" (Lam "y" (Var "x"))
eS =
    let f = Var "f" in
    let g = Var "g" in
    let x = Var "x" in
    Lam "f" (Lam "g" (Lam "x" ((f @@ x) @@ (g @@ x))))

e0 = Lam "f" (Lam "x" (Var "x"))
e1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
e2 = Lam "f" (Lam "x" (App (Var "f") (App (Var "f") (Var "x"))))


main :: IO ()
main = do
    putStrLn "Toy language type inference REPL 1.0.0.95"
    putStrLn ""
    putStrLn "The language:"
    putStrLn "e = x, e e, \\x -> e,"
    putStrLn "    (e,e), #0 e, #1 e,"
    putStrLn "    L e, R e, case e {L x -> e; R y -> e}, "
    putStrLn "    true, false, ()"
    putStrLn ""
    putStrLn "The types:"
    putStrLn "t = unit, bool, t -> t, t * t, t + t, unknowns"
    putStrLn ""
    loop

loop :: IO ()
loop = do
    putStr "> "
    hFlush stdout
    l <- getLine
    case parseExpr l of
        Right e -> do
            putStrLn "program:"
            print (e :: Expr)
            putStrLn ""
            case runCheck 1 (infer [] e) of
                Right (s, t) -> do
                    putStrLn "has type:"
                    putStrLn (pp t)
                Left msg -> do
                    putStrLn "inference error:"
                    putStrLn msg
            putStrLn ""
            loop
        Left msg -> do
            putStrLn msg
            loop
