
module Frontend.Kotlin.AST

import Tools.AstF
import Tools.FullList
import Tools.Annotation

%access public export

--     _    ____ _____   _____                 _             
--    / \  / ___|_   _| |  ___|   _ _ __   ___| |_ ___  _ __ 
--   / _ \ \___ \ | |   | |_ | | | | '_ \ / __| __/ _ \| '__|
--  / ___ \ ___) || |   |  _|| |_| | | | | (__| || (_) | |   
-- /_/   \_\____/ |_|   |_|   \__,_|_| |_|\___|\__\___/|_|   
--                                                           

data Operator = RefEq | RefNeq
              | StructEq | StructNeq
              | Lt | Le | Gt | Ge
              | Plus | Subs | Mult | Div | Modulo
              | And | Or

Ident : Type
Ident = String

data SyntaxType = TypeTy | VarTy | ParamTy | ParamCTy
                | ClassTy | FunTy | DeclTy | FileTy
                | ExprTy | BlockTy | BlockExprTy | AccessTy

data SyntaxF : (k : SyntaxType -> Type) -> (i : SyntaxType) -> Type where
  TParam  : Ident -> FullList (k TypeTy) -> SyntaxF k TypeTy
  TNull   : k TypeTy -> SyntaxF k TypeTy
  TFun    : List (k TypeTy) -> SyntaxF k TypeTy

  VVar    : Ident -> Maybe (k TypeTy) -> k ExprTy -> SyntaxF k VarTy
  VVal    : Ident -> Maybe (k TypeTy) -> k ExprTy -> SyntaxF k VarTy

  Param   : Ident -> k TypeTy -> SyntaxF k ParamTy

  PCVar   : Ident -> Maybe (k TypeTy) -> k ExprTy -> SyntaxF k ParamCTy
  PCVal   : Ident -> Maybe (k TypeTy) -> k ExprTy -> SyntaxF k ParamCTy

  Class   : Ident -> List Ident -> FullList (k ParamCTy)
         -> List (k VarTy) -> SyntaxF k ClassTy

  Fun     : List Ident -> Ident -> List (k ParamTy)
         -> k TypeTy -> k BlockTy -> SyntaxF k FunTy

  DVar    : k VarTy -> SyntaxF k DeclTy
  DClass  : k ClassTy -> SyntaxF k DeclTy
  DFun    : k FunTy -> SyntaxF k DeclTy

  File    : List (k DeclTy) -> SyntaxF k FileTy

  EInt    : Integer -> SyntaxF k ExprTy
  EStr    : String  -> SyntaxF k ExprTy
  ETrue   : SyntaxF k ExprTy
  EFalse  : SyntaxF k ExprTy
  EThis   : SyntaxF k ExprTy
  ENull   : SyntaxF k ExprTy
  EAccess : k AccessTy -> SyntaxF k ExprTy
  EAss    : k AccessTy -> k ExprTy -> SyntaxF k ExprTy
  ECall   : Ident -> List (k ExprTy) -> SyntaxF k ExprTy
  ENot    : k ExprTy -> SyntaxF k ExprTy
  EMinus  : k ExprTy -> SyntaxF k ExprTy
  EOp     : Operator -> k ExprTy -> k ExprTy -> SyntaxF k ExprTy
  EIfElse : k ExprTy -> k ExprTy -> k ExprTy -> SyntaxF k ExprTy
  EWhile  : k ExprTy -> k BlockExprTy -> SyntaxF k ExprTy
  EReturn : k ExprTy -> SyntaxF k ExprTy
  EFun    : List (k ParamTy) -> k TypeTy -> k BlockTy -> SyntaxF k ExprTy

  BEmpty  : SyntaxF k BlockTy
  BVar    : k VarTy -> k BlockTy -> SyntaxF k BlockTy
  BExpr   : k ExprTy -> k BlockTy -> SyntaxF k BlockTy

  BEBlock : k BlockTy -> SyntaxF k BlockExprTy
  BEExpr  : k ExprTy -> SyntaxF k BlockExprTy

  AIdent  : Ident -> SyntaxF k AccessTy
  ASub    : k ExprTy -> Ident -> SyntaxF k AccessTy
  ANSub   : k ExprTy -> Ident -> SyntaxF k AccessTy


--     _        _   _____   _           _                       
--    / \   ___| |_|  ___| (_)_ __  ___| |_ __ _ _ __   ___ ___ 
--   / _ \ / __| __| |_    | | '_ \/ __| __/ _` | '_ \ / __/ _ \
--  / ___ \\__ \ |_|  _|   | | | | \__ \ || (_| | | | | (_|  __/
-- /_/   \_\___/\__|_|     |_|_| |_|___/\__\__,_|_| |_|\___\___|
--                                                              
AstF SyntaxType SyntaxF where
  --  _              _ __  __           
  -- | |___  __ __ _| |  \/  |__ _ _ __ 
  -- | / _ \/ _/ _` | | |\/| / _` | '_ \
  -- |_\___/\__\__,_|_|_|  |_\__,_| .__/
  --                              |_|   
  localMap _ _ fn TypeTy (TParam x y) = TParam x $ map (fn TypeTy) y
  localMap _ _ fn TypeTy (TNull x)    = TNull $ fn TypeTy x
  localMap _ _ fn TypeTy (TFun xs)    = TFun $ map (fn TypeTy) xs

  localMap _ _ fn VarTy (VVar x y z) = VVar x (map (fn TypeTy) y) $ fn ExprTy z
  localMap _ _ fn VarTy (VVal x y z) = VVal x (map (fn TypeTy) y) $ fn ExprTy z

  localMap _ _ fn ParamTy (Param x y) = Param x $ fn TypeTy y

  localMap _ _ fn ParamCTy (PCVar x y z) = PCVar x (map (fn TypeTy) y) $ fn ExprTy z
  localMap _ _ fn ParamCTy (PCVal x y z) = PCVal x (map (fn TypeTy) y) $ fn ExprTy z

  localMap _ _ fn ClassTy (Class x xs y ys) = Class x xs
                                                    (map (fn ParamCTy) y)
                                                    (map (fn VarTy) ys)

  localMap _ _ fn FunTy (Fun xs x ys y z) = Fun xs x (map (fn ParamTy) ys)
                                                (fn TypeTy y)
                                                (fn BlockTy z)

  localMap _ _ fn DeclTy (DVar x)   = DVar $ fn VarTy x
  localMap _ _ fn DeclTy (DClass x) = DClass $ fn ClassTy x
  localMap _ _ fn DeclTy (DFun x)   = DFun $ fn FunTy x

  localMap _ _ fn FileTy (File xs) = File $ map (fn DeclTy) xs

  localMap _ _ fn ExprTy (EInt x)        = EInt x
  localMap _ _ fn ExprTy (EStr x)        = EStr x
  localMap _ _ fn ExprTy ETrue           = ETrue
  localMap _ _ fn ExprTy EFalse          = EFalse
  localMap _ _ fn ExprTy EThis           = EThis
  localMap _ _ fn ExprTy ENull           = ENull
  localMap _ _ fn ExprTy (EAccess x)     = EAccess $ fn AccessTy x
  localMap _ _ fn ExprTy (EAss x y)      = EAss (fn AccessTy x) (fn ExprTy y)
  localMap _ _ fn ExprTy (ECall x xs)    = ECall x (map (fn ExprTy) xs)
  localMap _ _ fn ExprTy (ENot x)        = ENot $ fn ExprTy x
  localMap _ _ fn ExprTy (EMinus x)      = EMinus $ fn ExprTy x
  localMap _ _ fn ExprTy (EOp x y z)     = EOp x (fn ExprTy y) (fn ExprTy z)
  localMap _ _ fn ExprTy (EIfElse x y z) = EIfElse (fn ExprTy x)
                                                   (fn ExprTy y)
                                                   (fn ExprTy z)
  localMap _ _ fn ExprTy (EWhile x y)    = EWhile (fn ExprTy x) (fn BlockExprTy y)
  localMap _ _ fn ExprTy (EReturn x)     = EReturn $ fn ExprTy x
  localMap _ _ fn ExprTy (EFun xs x y)   = EFun (map (fn ParamTy) xs)
                                                (fn TypeTy x)
                                                (fn BlockTy y)

  localMap _ _ fn BlockTy BEmpty      = BEmpty
  localMap _ _ fn BlockTy (BVar x y)  = BVar (fn VarTy x) (fn BlockTy y)
  localMap _ _ fn BlockTy (BExpr x y) = BExpr (fn ExprTy x) (fn BlockTy y)

  localMap _ _ fn BlockExprTy (BEBlock x) = BEBlock $ fn BlockTy x
  localMap _ _ fn BlockExprTy (BEExpr x)  = BEExpr  $ fn ExprTy  x

  localMap _ _ fn AccessTy (AIdent x)  = AIdent x
  localMap _ _ fn AccessTy (ASub x y)  = ASub  (fn ExprTy x) y
  localMap _ _ fn AccessTy (ANSub x y) = ANSub (fn ExprTy x) y


--     _                      _        _   _             
--    / \   _ __  _ __   ___ | |_ __ _| |_(_) ___  _ __  
--   / _ \ | '_ \| '_ \ / _ \| __/ _` | __| |/ _ \| '_ \ 
--  / ___ \| | | | | | | (_) | || (_| | |_| | (_) | | | |
-- /_/   \_\_| |_|_| |_|\___/ \__\__,_|\__|_|\___/|_| |_|
--                                                       

SyntaxAnn : SyntaxType -> Type -> Type
SyntaxAnn = Annotated SyntaxType SyntaxF

