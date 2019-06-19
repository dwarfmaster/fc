
module Frontend.Kotlin.AST

import Tools.AstF
import Tools.FullList
import Tools.Annotation
import Data.So
import Data.Vect

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

operatorLvl : Operator -> Nat
operatorLvl RefEq     = 6
operatorLvl RefNeq    = 6
operatorLvl StructEq  = 6
operatorLvl StructNeq = 6
operatorLvl Lt        = 5
operatorLvl Le        = 5
operatorLvl Gt        = 5
operatorLvl Ge        = 5
operatorLvl Plus      = 4
operatorLvl Subs      = 4
operatorLvl Mult      = 3
operatorLvl Div       = 3
operatorLvl Modulo    = 3
operatorLvl And       = 7
operatorLvl Or        = 8

Show Operator where
  show RefEq     = "==="
  show RefNeq    = "!=="
  show StructEq  = "=="
  show StructNeq = "!="
  show Lt        = "<"
  show Le        = "<="
  show Gt        = ">"
  show Ge        = ">="
  show Plus      = "+"
  show Subs      = "-"
  show Mult      = "*"
  show Div       = "/"
  show Modulo    = "%"
  show And       = "&&"
  show Or        = "||"

Ident : Type
Ident = String

data SyntaxType = TypeTy | VarTy | ParamTy | ParamCTy
                | ClassTy | FunTy | DeclTy | FileTy
                | ExprTy | BlockTy | BlockExprTy | AccessTy

data SyntaxF : (k : SyntaxType -> Type) -> (i : SyntaxType) -> Type where
  TParam  : Ident -> List (k TypeTy) -> SyntaxF k TypeTy
  TNull   : k TypeTy -> SyntaxF k TypeTy
  TFun    : List (k TypeTy) -> k TypeTy -> SyntaxF k TypeTy

  VVar    : Ident -> Maybe (k TypeTy) -> k ExprTy -> SyntaxF k VarTy
  VVal    : Ident -> Maybe (k TypeTy) -> k ExprTy -> SyntaxF k VarTy

  Param   : Ident -> k TypeTy -> SyntaxF k ParamTy

  PCVar   : Ident -> k TypeTy -> SyntaxF k ParamCTy
  PCVal   : Ident -> k TypeTy -> SyntaxF k ParamCTy

  Class   : Ident -> List Ident -> List (k ParamCTy)
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
  EIfElse : k ExprTy -> k BlockExprTy -> k BlockExprTy -> SyntaxF k ExprTy
  EWhile  : k ExprTy -> k BlockExprTy -> SyntaxF k ExprTy
  EReturn : Maybe (k ExprTy) -> SyntaxF k ExprTy
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
  localMap _ _ fn TypeTy (TFun xs x)  = TFun (map (fn TypeTy) xs) $ fn TypeTy x

  localMap _ _ fn VarTy (VVar x y z) = VVar x (map (fn TypeTy) y) $ fn ExprTy z
  localMap _ _ fn VarTy (VVal x y z) = VVal x (map (fn TypeTy) y) $ fn ExprTy z

  localMap _ _ fn ParamTy (Param x y) = Param x $ fn TypeTy y

  localMap _ _ fn ParamCTy (PCVar x y) = PCVar x $ (fn TypeTy) y
  localMap _ _ fn ParamCTy (PCVal x y) = PCVal x $ (fn TypeTy) y

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
                                                   (fn BlockExprTy y)
                                                   (fn BlockExprTy z)
  localMap _ _ fn ExprTy (EWhile x y)    = EWhile (fn ExprTy x) (fn BlockExprTy y)
  localMap _ _ fn ExprTy (EReturn x)     = EReturn $ map (fn ExprTy) x
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


--  _____                 
-- |_   _|   _ _ __   ___ 
--   | || | | | '_ \ / _ \
--   | || |_| | |_) |  __/
--   |_| \__, | .__/ \___|
--       |___/|_|         


--  _  _  ___   _   ___ 
-- | || |/ _ \ /_\ / __|
-- | __ | (_) / _ \\__ \
-- |_||_|\___/_/ \_\___/
--                      
mutual
  record KClass where
    constructor MkClass
    name    : String
    argc    : Nat
    members : List $ Pair String $ (Vect argc KType) -> KType

  record KFun where
    constructor MkFun
    name : String
    argc : Nat
    args : List $ Pair String $ Vect argc KType -> KType
    ret  : Vect argc KType -> KType

  data KType : Type where
    KTFun   : (f : KFun) -> Vect (argc f) KType -> KType
    KTNull  : KType
    KTOpt   : KType -> KType
    KTClass : (c : KClass) -> Vect (argc c) KType -> KType

record Var where
  constructor MkVar
  name  : String
  type  : KType
  scope : Nat
  
-- TODO replace lists by SortedMap
record Environment where
  constructor MkEnv
  classes   : List KClass
  functions : List KFun
  variables : List (List Var)

interface Named a where
  name : a -> String

Named KClass where
  name = KClass.name

Named KFun where
  name = KFun.name

Named Var where
  name = Var.name


--  _                 _                _ 
-- | |   _____ __ __ | |   _____ _____| |
-- | |__/ _ \ V  V / | |__/ -_) V / -_) |
-- |____\___/\_/\_/  |____\___|\_/\___|_|
--                                       
interface Named a => Lookable t a | t where
  total lookupDef  : t -> String -> Bool
  total lookupObj  : (objs : t) -> (c : String) -> (So $ lookupDef objs c) -> a
  total insertable : Bool
  total subset     : t -> t -> Type
  total propagate  : (c : String) -> (objs1 : t) -> (objs2 : t)
                  -> subset objs1 objs -> (So $ lookupDef objs1 c)
                  -> (So $ lookupDef objs2 c)
  total insert     : So insertable -> (objs : t) -> (obj : a)
                  -> (result : t ** (Pair (So $ lookupDef result $ name obj) (subset objs result)))

total namedLookupDef : Named a => a -> String -> Bool
namedLookupDef obj nm = case decEq (name obj) nm of
                             Yes _ => True
                             No _  => False

total namedLookupObj : Named a => (obj : a) -> (nm : String) -> (So $ namedLookupDef obj nm) -> a
namedLookupObj obj nm prf with (name obj == nm)
  | True  = obj
  | False = void $ uninhabited prf

total namedSubset : Named a => a -> a -> Type
namedSubset obj1 obj2 = name obj1 = name obj2

total namedPropagate : Named a => (c : String) -> (obj1 : a) -> (obj2 : a)
                    -> namedSubset obj1 obj2 -> (So $ namedLookupDef obj1 c)
                    -> (So $ namedLookupDef obj2 c)
namedPropagate c obj1 obj2 sub prf with (name obj1 == name obj2)
  | True with (name obj1 == c) proof eqC
    | True  = ?hole
    | False = void $ uninhabited prf
  | False = ?hole2

Lookable KClass KClass where
  lookupDef  = namedLookupDef
  lookupObj  = namedLookupObj
  insertable = False
  subset     = namedSubset
Lookable KFun KFun where
  lookupDef  = namedLookupDef
  lookupObj  = namedLookupObj
  insertable = False
  subset     = namedSubset
Lookable Var Var where
  lookupDef  = namedLookupDef
  lookupObj  = namedLookupObj
  insertable = False
  subset     = namedSubset

total listLookupDef : Lookable t a => List t -> String -> Bool
listLookupDef []       _ = False
listLookupDef (h :: t) c = lookupDef h c || listLookupDef t c

Lookable t a => Lookable (List t) a where
  lookupDef = listLookupDef
  lookupObj (h :: t) c prf with (lookupDef h c) proof eq
    | True  = lookupObj h c $ replace eq prf
    | False = lookupObj t c prf
  insertable = True


--  _   _ _   _ _ _ _   _        
-- | | | | |_(_) (_) |_(_)___ ___
-- | |_| |  _| | | |  _| / -_|_-<
--  \___/ \__|_|_|_|\__|_\___/__/
--                               
total hasClass : Environment -> String -> Type
hasClass env c = So $ lookupDef (classes env) c

total hasFun : Environment -> String -> Type
hasFun env c = So $ lookupDef (functions env) c

total hasVar : Environment -> String -> Type
hasVar env c = So $ lookupDef (variables env) c

total envClass : (e : Environment) -> (c : String) -> hasClass e c -> KClass
envClass env c prf = lookupObj (classes env) c prf

total envFun : (e : Environment) -> (c : String) -> hasFun e c -> KFun
envFun env c prf = lookupObj (functions env) c prf

total envVar : (e : Environment) -> (c : String) -> hasVar e c -> Var
envVar env c prf = lookupObj (variables env) c prf


