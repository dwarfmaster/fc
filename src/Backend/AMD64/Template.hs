
{-# LANGUAGE TemplateHaskell #-}

-- |Template Haskell definitions for the Asm module
module Backend.AMD64.Template (mkSize, mkRegister) where
import Language.Haskell.TH
import Data.Char (toUpper)

-- |Generates a constant function
constFun :: String -> Lit -> Dec
constFun name c = FunD (mkName name)
                       [ Clause []
                                (NormalB $ AppE (VarE $ mkName "const") 
                                                (LitE c)) 
                                []
                       ]

-- |Generates a type for size i and an instance of Size :
-- data Size'i
-- instance Size Size'i where
--     size_bytes = const $ i / 8
mkSize :: Integer -> Q [Dec]
mkSize i = return [data_def, inst_def]
 where name      = mkName $ "Size" ++ show i
       inst_name = mkName "Size"
       data_def  = DataD [] name [] Nothing [] []
       inst_def  = InstanceD Nothing []
                     (AppT (ConT inst_name) (ConT name))
                     [ constFun "size_bytes" $ IntegerL $ i `div` 8 ]

-- |Generates a type for a register, along with the right instances.
-- It needs the register name uncapitalised and its size in bits
-- For exemple, mkRegister "eax" 64 would generate :
-- @
--   data Eax = Eax
--   eax :: Eax
--   eax = Eax
--   eax' :: AnyRegister
--   eax' = AnyRegister eax
--   instance Register Eax where
--       reg_name = const "eax"
--       reg_ref  = const "%eax"
--   instance Sized Eax Size32
--   instance RValue Eax where
--       arg = const "%eax"
--   instance LValue Eax
-- @
mkRegister :: String -> Integer -> Q [Dec]
mkRegister name size = return [ data_def, alias_sig, alias
                              , reg_inst, alias_sig', alias'
                              , sized_inst, rvalue_inst, lvalue_inst]
 where lname       = mkName name
       lname'      = mkName $ name ++ "'"
       uname       = mkName $ (\(x:xs) -> toUpper x : xs) name

       data_def    = DataD [] uname [] Nothing [NormalC uname []] []

       alias_sig   = SigD lname (ConT uname)
       alias       = FunD lname [ Clause [] (NormalB $ ConE uname) [] ]

       alias_sig'  = SigD lname' (ConT $ mkName "AnyRegister")
       alias'      = FunD lname' [ Clause []
                                          (NormalB $ AppE (ConE $ mkName "AnyRegister")
                                                          (VarE lname))
                                          [] ]

       reg_inst    = InstanceD Nothing []
                       (AppT (ConT $ mkName "Register") (ConT uname))
                       [ constFun "reg_name" $ StringL name
                       , constFun "reg_ref"  $ StringL $ '%' : name
                       ]

       sized_inst  = InstanceD Nothing []
                       (AppT (AppT (ConT $ mkName "Sized") (ConT uname))
                             (ConT $ mkName $ "Size" ++ show size))
                       []
       
       rvalue_inst = InstanceD Nothing []
                       (AppT (ConT $ mkName "RValue") (ConT uname))
                       [ constFun "arg" $ StringL $ '%' : name ]

       lvalue_inst = InstanceD Nothing []
                       (AppT (ConT $ mkName "LValue") (ConT uname))
                       []

