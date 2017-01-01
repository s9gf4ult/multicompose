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
  | len functors a -> applied, len applied a -> functors, functors applied -> a

instance
  Applied' ('S 'Z) (f ': '[]) (f a) a

instance
  Applied' ('S len) (f2 ': rest) (f2 restapps) a
  => Applied' ('S ('S len)) (f ': f2 ': rest) (f (f2 restapps)) a

type Applied functors applied a = Applied' (Length functors) functors applied a

data MultiCompose (functors :: [* -> *]) (a :: *) where
  MultiCompose
    :: (Applied functors applied a)
    => applied
    -> MultiCompose functors a
