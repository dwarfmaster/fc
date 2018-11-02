
module Tools.AstF

public export
interface AstF (idx : Type) (f : (idx -> Type) -> (idx -> Type)) where
  localMap : (f1 : idx -> Type) -> (f2 : idx -> Type) -> ((i : idx) -> f1 i -> f2 i)
          -> (i : idx) -> f f1 i -> f f2 i
  -- TODO find a food localFold
  -- localFold : Monoid m => (i : idx) -> f (\_ => m) i -> m

