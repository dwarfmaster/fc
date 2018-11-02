
module Tools.FullList

%access public export

data FullList a = End a | Cons a (FullList a)

(++) : FullList a -> FullList a -> FullList a
(End x)     ++ tl' = Cons x tl'
(Cons x tl) ++ tl' = Cons x $ tl ++ tl'

Functor FullList where
  map f (End x)     = End $ f x
  map f (Cons x tl) = Cons (f x) $ map f tl

Foldable FullList where
  foldl func init (End x)     = func init x
  foldl func init (Cons x tl) = func (foldl func init tl) x
  foldr func init (End x)     = func x init
  foldr func init (Cons x tl) = func x $ foldr func init tl

Applicative FullList where
  pure x = End x
  (End f)     <*> lst = map f lst
  (Cons f tl) <*> lst = map f lst ++ (tl <*> lst)

