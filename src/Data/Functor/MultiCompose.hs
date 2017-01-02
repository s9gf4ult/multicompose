module Data.Functor.MultiCompose where

import TypeFun.Data.List
import TypeFun.Data.Peano

type family Apply (fs :: [* -> *]) (a :: *) :: * where
  Apply '[] a = a
  Apply (f ': fs) a = f (Apply fs a)

type family Deapply (applied :: *) (len :: N) :: [* -> *] where
  Deapply a 'Z = '[]
  Deapply (f rest) ('S len) = f ': (Deapply rest len)

-- | Typeclass providing bidirectional type inference:
--
-- 1. We can derive list of functors from agument applied to 'MultiCompose'
-- 2. We can derive argument of 'MultiCompose' from functors list
class
  ( len ~ Length functors
  , Apply functors a ~ applied
  , Deapply applied len ~ functors
  ) =>
  Composable' len (functors :: [* -> *]) (applied :: *) (a :: *)
  | functors a -> applied, len applied a -> functors, functors applied -> a where
  compose :: applied -> MultiCompose functors a
  decompose :: MultiCompose functors a -> applied

instance Composable' 'Z '[] a a where
  compose a = MCEmpty a
  decompose (MCEmpty a) = a

instance
  ( Composable' len rest restapps a
  , Functor f
  ) =>
  Composable' ('S len) (f ': rest) (f restapps) a where
  compose app = MCApply $ fmap compose app
  decompose (MCApply a) = fmap decompose a

type Composable functors applied a =
  Composable' (Length functors) functors applied a

data MultiCompose fs a where
  MCEmpty :: a -> MultiCompose '[] a
  MCApply :: f (MultiCompose rest a) -> MultiCompose (f ': rest) a

instance
  Functor (MultiCompose '[]) where
  fmap f (MCEmpty a) = MCEmpty $ f a

instance
  ( Functor f, Functor (MultiCompose rest)
  ) =>
  Functor (MultiCompose (f ': rest)) where
  fmap f (MCApply fa) = MCApply $ fmap (fmap f) fa

instance
  Applicative (MultiCompose '[]) where
  pure = MCEmpty
  MCEmpty f <*> MCEmpty a = MCEmpty $ f a

instance
  ( Applicative f, Applicative (MultiCompose rest)
  ) =>
  Applicative (MultiCompose (f ': rest)) where
  pure a = MCApply $ pure $ pure a
  MCApply f <*> MCApply fa =
    let ff = fmap (<*>) f
    in MCApply $ ff <*> fa
