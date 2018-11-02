
module Tools.Indexed

%access public export

interface IxFunctor (idx : Type) (f : idx -> Type -> Type) where
  imap : {i : idx} -> (a -> b) -> f i a -> f i b

interface IxFunctor idx f => IxPointed idx (f : idx -> Type -> Type) where
  ireturn : {i : idx} -> a -> f i a

interface IxFunctor idx f => IxCopointed idx (f : idx -> Type -> Type) where
  iextract : {i : idx} -> f i a -> a

interface IxPointed idx f => IxApplicative idx (f : idx -> Type -> Type) where
  iapp : {i : idx} -> f i (a -> b) -> f i a -> f i b

interface IxFoldable (idx : Type) (f : idx -> Type -> Type) where
  ifoldMap : Monoid m => {i : idx} -> (a -> m) -> f i a -> m

