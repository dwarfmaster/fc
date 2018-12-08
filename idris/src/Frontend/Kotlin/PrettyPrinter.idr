
module Fronted.Kotlin.PrettyPrinter

import Frontend.Kotlin.AST
import Tools.Annotation

%access public export


--  _   _ _   _ _      ---------------------------------------------------------
-- | | | | |_(_) |___  ---------------------------------------------------------
-- | | | | __| | / __| ---------------------------------------------------------
-- | |_| | |_| | \__ \ ---------------------------------------------------------
--  \___/ \__|_|_|___/ ---------------------------------------------------------
--                     ---------------------------------------------------------
exprLvl : (k : SyntaxType -> Type)
       -> (k ExprTy -> Nat)
       -> SyntaxF k ExprTy
       -> Nat
exprLvl _ lvl (EInt x)        = 0
exprLvl _ lvl (EStr x)        = 0
exprLvl _ lvl ETrue           = 0
exprLvl _ lvl EFalse          = 0
exprLvl _ lvl EThis           = 0
exprLvl _ lvl ENull           = 0
exprLvl _ lvl (EAccess x)     = 0
exprLvl _ lvl (EAss x y)      = 8
exprLvl _ lvl (ECall x xs)    = 0
exprLvl _ lvl (ENot x)        = 1
exprLvl _ lvl (EMinus x)      = 1
exprLvl _ lvl (EOp x y z)     = operatorLvl x
exprLvl _ lvl (EIfElse x y z) = 10
exprLvl _ lvl (EWhile x y)    = 9
exprLvl _ lvl (EReturn x)     = 9
exprLvl _ lvl (EFun xs x y)   = 0


intersperse : String -> List String -> String
intersperse sep [] = ""
intersperse sep xs = foldl1 (\a1 => \a2 => a1 ++ sep ++ a2) xs

parens : String -> String
parens str = "(" ++ str ++ ")"


--                 _   _         ____       _       _    ____             ------
--  _ __  _ __ ___| |_| |_ _   _|  _ \ _ __(_)_ __ | |_ / ___| ___ _ __   ------
-- | '_ \| '__/ _ \ __| __| | | | |_) | '__| | '_ \| __| |  _ / _ \ '_ \  ------
-- | |_) | | |  __/ |_| |_| |_| |  __/| |  | | | | | |_| |_| |  __/ | | | ------
-- | .__/|_|  \___|\__|\__|\__, |_|   |_|  |_|_| |_|\__|\____|\___|_| |_| ------
-- |_|                     |___/                                          ------
-- 

prettyPrintGen : (k : SyntaxType -> Type)
              -> ((tp : SyntaxType) -> Nat -> k tp -> String)
              -> (k ExprTy -> Nat)
              -> (tp : SyntaxType)
              -> Nat
              -> SyntaxF k tp
              -> String


--  _____              _____     
-- |_   _|  _ _ __  __|_   _|  _ 
--   | || || | '_ \/ -_)| || || |
--   |_| \_, | .__/\___||_| \_, |
--       |__/|_|            |__/ 
prettyPrintGen _ shower lvl _ tbs (TParam x [])  = x
prettyPrintGen _ shower lvl _ tbs (TParam x xs)  = x ++ "<"
                                                ++ ( intersperse ", "
                                                   $ map (shower TypeTy tbs) xs)
                                                ++ ">"
prettyPrintGen _ shower lvl _ tbs (TNull x)      = shower TypeTy tbs x ++ "?"
prettyPrintGen _ shower lvl _ tbs (TFun xs x)    = ( parens  $ intersperse ", "
                                                   $ map (shower TypeTy tbs) xs)
                                                ++ " -> " ++ shower TypeTy tbs x


-- __   __       _____     
-- \ \ / /_ _ _ |_   _|  _ 
--  \ V / _` | '_|| || || |
--   \_/\__,_|_|  |_| \_, |
--                    |__/ 
prettyPrintGen _ shower lvl _ tbs (VVar x Nothing z)  = concat (take tbs (repeat "\t"))
                                                     ++ "var " ++ x ++ " = "
                                                     ++ shower ExprTy (tbs + 1) z
prettyPrintGen _ shower lvl _ tbs (VVar x (Just t) z) = concat (take tbs (repeat "\t"))
                                                     ++ "var " ++ x ++ " : " ++ shower TypeTy 0 t
                                                     ++ " = " ++ shower ExprTy (tbs + 1) z
prettyPrintGen _ shower lvl _ tbs (VVal x Nothing z)  = concat (take tbs (repeat "\t"))
                                                     ++ "val " ++ x ++ " = "
                                                     ++ shower ExprTy (tbs + 1) z
prettyPrintGen _ shower lvl _ tbs (VVal x (Just t) z) = concat (take tbs (repeat "\t"))
                                                     ++ "val " ++ x ++ " : " ++ shower TypeTy 0 t
                                                     ++ " = " ++ shower ExprTy (tbs + 1) z


--  ___                   _____       ___                     ___ _____     
-- | _ \__ _ _ _ __ _ _ _|_   _|  _  | _ \__ _ _ _ __ _ _ __ / __|_   _|  _ 
-- |  _/ _` | '_/ _` | '  \| || || | |  _/ _` | '_/ _` | '  \ (__  | || || |
-- |_| \__,_|_| \__,_|_|_|_|_| \_, | |_| \__,_|_| \__,_|_|_|_\___| |_| \_, |
--                             |__/                                    |__/ 
prettyPrintGen _ shower lvl _ tbs (Param x y) =           x ++ " : " ++ shower TypeTy 0 y
prettyPrintGen _ shower lvl _ tbs (PCVar x y) = "var " ++ x ++ " : " ++ shower TypeTy 0 y
prettyPrintGen _ shower lvl _ tbs (PCVal x y) = "val " ++ x ++ " : " ++ shower TypeTy 0 y



--   ___ _            _____     
--  / __| |__ _ _____|_   _|  _ 
-- | (__| / _` (_-<_-< | || || |
--  \___|_\__,_/__/__/ |_| \_, |
--                         |__/ 
prettyPrintGen _ shower lvl _ tbs (Class x xs ys zs) = concat (take tbs (repeat "\t"))
                                                    ++ "data class " ++ x ++ "<"
                                                    ++ intersperse ", " xs ++ ">("
                                                    ++ ( intersperse ", "
                                                       $ map (shower ParamCTy (tbs + 1)) ys)
                                                    ++ ") {"
                                                    ++ ( intersperse ";\n"
                                                       $ map (shower VarTy (tbs + 1)) zs)
                                                    ++ " }"


--  ___        _____     
-- | __|  _ _ |_   _|  _ 
-- | _| || | ' \| || || |
-- |_| \_,_|_||_|_| \_, |
--                  |__/ 
prettyPrintGen _ shower lvl _ tbs (Fun xs x ys y z) = concat (take tbs (repeat "\t"))
                                                   ++ "fun<" ++ intersperse ", " xs ++ "> "
                                                   ++ x ++ "("
                                                   ++ ( intersperse ", "
                                                      $ map (shower ParamTy 0) ys)
                                                   ++ ")"
                                                   ++ case y of
                                                        Nothing => ""
                                                        Just y' => " : " ++ shower TypeTy 0 y'
                                                   ++ " {\n" ++ shower BlockTy (tbs + 1) z


--  ___         _ _____     
-- |   \ ___ __| |_   _|  _ 
-- | |) / -_) _| | | || || |
-- |___/\___\__|_| |_| \_, |
--                     |__/ 
prettyPrintGen _ shower lvl _ tbs (DVar x)   = shower VarTy   tbs x
prettyPrintGen _ shower lvl _ tbs (DClass x) = shower ClassTy tbs x
prettyPrintGen _ shower lvl _ tbs (DFun x)   = shower FunTy   tbs x


--  ___ _ _    _____     
-- | __(_) |__|_   _|  _ 
-- | _|| | / -_)| || || |
-- |_| |_|_\___||_| \_, |
--                  |__/ 
prettyPrintGen _ shower lvl _ tbs (File xs) = intersperse "\n\n"
                                            $ map (shower DeclTy tbs) xs


--  ___             _____     
-- | __|_ ___ __ _ |_   _|  _ 
-- | _|\ \ / '_ \ '_|| || || |
-- |___/_\_\ .__/_|  |_| \_, |
--         |_|           |__/ 
prettyPrintGen _ shower lvl _ tbs (EInt x)        = show x
prettyPrintGen _ shower lvl _ tbs (EStr x)        = show x
prettyPrintGen _ shower lvl _ tbs ETrue           = "true"
prettyPrintGen _ shower lvl _ tbs EFalse          = "false"
prettyPrintGen _ shower lvl _ tbs EThis           = "this"
prettyPrintGen _ shower lvl _ tbs ENull           = "null"
prettyPrintGen _ shower lvl _ tbs (EAccess x)     = shower AccessTy tbs x
prettyPrintGen _ shower lvl _ tbs (EAss x y)      = shower AccessTy tbs x ++ " = "
                                                 ++ shower ExprTy   tbs y
prettyPrintGen _ shower lvl _ tbs (ECall x xs)    = x ++ "("
                                                 ++ ( intersperse ", "
                                                    $ map (shower ExprTy tbs) xs)
                                                 ++ ")"
prettyPrintGen _ shower lvl _ tbs (ENot x)        = "!"
                                                 ++ ( (if lvl x > 1 then parens else id)
                                                    $ shower ExprTy tbs x)
prettyPrintGen _ shower lvl _ tbs (EMinus x)      = "-"
                                                 ++ ( (if lvl x > 1 then parens else id)
                                                    $ shower ExprTy tbs x)
prettyPrintGen _ shower lvl _ tbs (EOp x y z)     = ( (if lvl y > operatorLvl x then parens else id)
                                                    $ shower ExprTy tbs y)
                                                 ++ " " ++ show x ++ " "
                                                 ++ ( (if lvl z > operatorLvl x then parens else id)
                                                    $ shower ExprTy tbs z)
prettyPrintGen _ shower lvl _ tbs (EIfElse x y z) = "if(" ++ shower ExprTy tbs x ++ ") "
                                                 ++ shower BlockExprTy tbs y
                                                 ++ case z of
                                                      Nothing => ""
                                                      Just z' => " else "
                                                              ++ shower BlockExprTy tbs z'
prettyPrintGen _ shower lvl _ tbs (EWhile x y)    = "while(" ++ shower ExprTy tbs x ++ ") "
                                                 ++ shower BlockExprTy tbs y
prettyPrintGen _ shower lvl _ tbs (EReturn x)     = "return "
                                                 ++ case x of
                                                      Nothing => ""
                                                      Just x' => shower ExprTy tbs x'
prettyPrintGen _ shower lvl _ tbs (EFun xs x y)   = "fun("
                                                 ++ ( intersperse ", "
                                                    $ map (shower ParamTy tbs) xs)
                                                 ++ ") "
                                                 ++ case x of
                                                      Nothing => ""
                                                      Just t  => " : " ++ shower TypeTy tbs t ++ " "
                                                 ++ "{" ++ shower BlockTy (tbs + 1) y


--  ___ _         _   _____     
-- | _ ) |___  __| |_|_   _|  _ 
-- | _ \ / _ \/ _| / / | || || |
-- |___/_\___/\__|_\_\ |_| \_, |
--                         |__/ 
prettyPrintGen _ shower lvl _ tbs BEmpty      = concat (take tbs (repeat "\t")) ++ "}"
prettyPrintGen _ shower lvl _ tbs (BVar x y)  = shower VarTy   (tbs + 1) x ++ "\n"
                                             ++ shower BlockTy tbs       y
prettyPrintGen _ shower lvl _ tbs (BExpr x y) = concat (take (tbs + 1) (repeat "\t"))
                                             ++ shower ExprTy  (tbs + 1) x ++ "\n"
                                             ++ shower BlockTy tbs       y


--  ___ _         _   ___             _____     
-- | _ ) |___  __| |_| __|_ ___ __ _ |_   _|  _ 
-- | _ \ / _ \/ _| / / _|\ \ / '_ \ '_|| || || |
-- |___/_\___/\__|_\_\___/_\_\ .__/_|  |_| \_, |
--                           |_|           |__/ 
prettyPrintGen _ shower lvl _ tbs (BEBlock x) = concat (take tbs (repeat "\t")) ++ "{"
                                             ++ shower BlockTy tbs x
prettyPrintGen _ shower lvl _ tbs (BEExpr x)  = shower ExprTy tbs x


--    _                   _____     
--   /_\  __ __ ___ _____|_   _|  _ 
--  / _ \/ _/ _/ -_|_-<_-< | || || |
-- /_/ \_\__\__\___/__/__/ |_| \_, |
--                             |__/ 
prettyPrintGen _ shower lvl _ tbs (AIdent x)  = x
prettyPrintGen _ shower lvl _ tbs (ASub x y)  = ( (if lvl x > 0 then parens else id)
                                                $ shower ExprTy tbs x)
                                               ++ "." ++ y
prettyPrintGen _ shower lvl _ tbs (ANSub x y) = ( (if lvl x > 0 then parens else id)
                                                $ shower ExprTy tbs x)
                                               ++ "?." ++ y


--     _                      _        _   _              ----------------------
--    / \   _ __  _ __   ___ | |_ __ _| |_(_) ___  _ __   ----------------------
--   / _ \ | '_ \| '_ \ / _ \| __/ _` | __| |/ _ \| '_ \  ----------------------
--  / ___ \| | | | | | | (_) | || (_| | |_| | (_) | | | | ----------------------
-- /_/   \_\_| |_|_| |_|\___/ \__\__,_|\__|_|\___/|_| |_| ----------------------
--                                                        ----------------------

prettyPrintLvl : SyntaxAnn ExprTy a -> Nat
prettyPrintLvl (Ann _ syn) = exprLvl (\id => SyntaxAnn id a) prettyPrintLvl syn

prettyPrintAST : (tp : SyntaxType) -> Nat -> SyntaxAnn tp a -> String
prettyPrintAST _ tbs (Ann _ syn) = prettyPrintGen (\id => SyntaxAnn id a)
                                                  prettyPrintAST
                                                  prettyPrintLvl
                                                  tp tbs syn

prettyPrintAnn : Show a => (tp : SyntaxType) -> Nat -> SyntaxAnn tp a -> String
prettyPrintAnn _ tbs (Ann ann syn) = "[" ++ show ann ++ "]"
                                  ++ prettyPrintGen (\id => SyntaxAnn id a)
                                                    prettyPrintAnn
                                                    prettyPrintLvl
                                                    tp tbs syn

Show (SyntaxAnn tp a) where
  show syn = prettyPrintAST tp 0 syn

