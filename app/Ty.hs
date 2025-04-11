module Ty where

data Ty =
    Alpha Int |
    Unit |
    Bool |
    Arrow Ty Ty |
    Plus Ty Ty |
    Cross Ty Ty
        deriving (Show, Read)

pp :: Ty -> String
pp t = go 0 t where
    go _ Unit = "unit"
    go _ Bool = "bool"
    go _ (Alpha i) = "u" ++ show i
    go p (Cross t1 t2) = wrap (p > 5) (go 6 t1 ++ " * " ++ go 5 t2)
    go p (Arrow t1 t2) = wrap (p > 3) (go 4 t1 ++ " -> " ++ go 3 t2)
    go p (Plus t1 t2)  = wrap (p > 1) (go 2 t1 ++ " + " ++ go 1 t2)

wrap b x = if b then "(" ++ x ++ ")" else x


type Sub = [(Int, Ty)]

occurs :: Int -> Ty -> Bool
occurs i (Alpha j) = i == j
occurs i (Arrow a b) = occurs i a || occurs i b
occurs i (Cross a b) = occurs i a || occurs i b
occurs i (Plus a b) = occurs i a || occurs i b
occurs _ _ = False

subst :: Int -> Ty -> Ty -> Ty
subst i r (Alpha j)
    | i == j = r
    | otherwise = Alpha j
subst i r (Arrow a b) = Arrow (subst i r a) (subst i r b)
subst i r (Cross a b) = Cross (subst i r a) (subst i r b)
subst i r (Plus a b) = Plus (subst i r a) (subst i r b)
subst _ _ other = other

subAll :: Sub -> Ty -> Ty
subAll [] t = t
subAll ((i,r):ss) t = subAll ss (subst i r t)

mgu :: Ty -> Ty -> Either String Sub
mgu Unit Unit = Right []  -- delete
mgu Bool Bool = Right []  -- delete
mgu (Alpha i) (Alpha j)
    | i == j = Right [] -- delete
    | otherwise = Right [(j, Alpha i)] -- eliminate
mgu (Alpha i) t
    | occurs i t = Left "occurs check failed"
    | otherwise = Right [(i, t)] -- eliminate
mgu t (Alpha i) = mgu (Alpha i) t -- swap
mgu (Arrow a b) (Arrow c d) = do -- decompose
    sub1 <- mgu a c
    sub2 <- mgu (subAll sub1 b) (subAll sub1 d)
    Right (sub1 ++ sub2)
mgu (Cross a b) (Cross c d) = do
    sub1 <- mgu a c
    sub2 <- mgu (subAll sub1 b) (subAll sub1 d)
    Right (sub1 ++ sub2)
mgu (Plus a b) (Plus c d) = do
    sub1 <- mgu a c
    sub2 <- mgu (subAll sub1 b) (subAll sub1 d)
    Right (sub1 ++ sub2)
mgu _ _ = Left "can't unify" -- conflict



parseTy :: String -> [(Ty, String)]
parseTy _ = []
