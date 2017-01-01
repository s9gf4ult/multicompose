module Data.Functor.MultiCompose where

import TypeFun.Data.List
import TypeFun.Data.Peano

-- | Typeclass providing bidirectional type inference:
--
-- 1. We can derive list of functors from agument applied to 'MultiCompose'
-- 2. We can derive argument of 'MultiCompose' from functors list
class
  (len ~ Length functors)
  => Applied' len (functors :: [* -> *]) (applied :: *) (a :: *)
  | functors a -> applied, len applied a -> functors, functors applied -> a

instance
  Applied' ('S 'Z) '[f] (f a) a

instance
  Applied' ('S len) (f2 ': rest) (f2 restapps) a
  => Applied' ('S ('S len)) (f ': f2 ': rest) (f (f2 restapps)) a

type Applied functors applied a = Applied' (Length functors) functors applied a

data MultiCompose fs a where
  MultiCompose
    :: (Applied fs app a)
    => app
    -> MultiCompose fs a

-- deriving instance (Eq app, Applied f app a) => Eq (MultiCompose f a)

-- instance
--   (Functor f)
--   => Functor (MultiCompose '[f]) where
--   fmap f (MultiCompose fa) = MultiCompose $ fmap f fa

fmapComp :: (a -> b) -> MultiCompose '[f] a -> MultiCompose '[f] b
fmapComp f (MultiCompose fa) = MultiCompose $ fmap f fa
-- fmapComp f (MultiCompose fa) = MultiCompose _
