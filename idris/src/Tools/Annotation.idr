
module Tools.Annotation

import Tools.Indexed
import Tools.AstF

%access public export

AstFTy : Type -> Type
AstFTy idx = (idx -> Type) -> (idx -> Type)

data Annotated : (idx : Type) -> (f : AstFTy idx)
              -> (i : idx) -> (ann : Type) -> Type where
  Ann : (a : ann) -> f (\id => Annotated idx f id ann) i -> Annotated idx f i ann

AstF idx f => IxFunctor idx (Annotated idx f) where
  imap {b} {a} {i} fn (Ann x rec) = Ann (fn x)
                          $ localMap (\id => Annotated idx f id a)
                                     (\id => Annotated idx f id b)
                                     (\id => imap {i = id} fn)
                                     i rec

AstF idx f => IxCopointed idx (Annotated idx f) where
  iextract (Ann x _) = x

