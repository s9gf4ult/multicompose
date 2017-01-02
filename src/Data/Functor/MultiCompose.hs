module Data.Functor.MultiCompose where

import TypeFun.Data.List
import TypeFun.Data.Peano

type family ApplyHelper (fs :: [* -> *]) (a :: *) :: * where
  ApplyHelper '[] a = a
  ApplyHelper (f ': fs) a = f (ApplyHelper fs a)

type family DeapplyHelper (applied :: *) (len :: N) :: [* -> *] where
  DeapplyHelper a 'Z = '[]
  DeapplyHelper (f rest) ('S len) = f ': (DeapplyHelper rest len)

type ApplyConstraint len functors applied a =
  ( len ~ Length functors
  , ApplyHelper functors a ~ applied
  , DeapplyHelper applied len ~ functors
  )

-- | Typeclass providing bidirectional type inference:
--
-- 1. We can derive list of functors from agument applied to 'MultiCompose'
-- 2. We can derive argument of 'MultiCompose' from functors list
class
  ( ApplyConstraint len functors applied a )
  => Applied' len (functors :: [* -> *]) (applied :: *) (a :: *)
  | functors a -> applied, len applied a -> functors, functors applied -> a where

instance Applied' 'Z '[] a a where

instance
  Applied' len rest restapps a
  => Applied' ('S len) (f ': rest) (f restapps) a where

type Applied functors applied a = Applied' (Length functors) functors applied a

data MultiCompose fs a where
  MultiCompose
    :: (Applied fs app a)
    => app
    -> MultiCompose fs a

getMultiCompose :: MultiCompose fs a -> ApplyHelper fs a
getMultiCompose (MultiCompose app) = app

deriving instance (Eq app, Applied f app a) => Eq (MultiCompose f a)
deriving instance (Ord app, Applied f app a) => Ord (MultiCompose f a)

instance
  Functor (MultiCompose '[]) where
  fmap f (MultiCompose a) = MultiCompose $ f a

-- instance
--   ( Functor (MultiCompose rest), Functor f, functors ~ f ': rest
--   , ApplyConstraint (Length functors) functors appb b ) =>
--   Functor (MultiCompose (f ': rest)) where
--   fmap f (MultiCompose fa) =
--     MultiCompose $ fmap _ fa

-- fmapComp :: (a -> b) -> MultiCompose '[f] a -> MultiCompose '[f] b
-- fmapComp f (MultiCompose fa) = MultiCompose $ fmap f fa
-- -- fmapComp f (MultiCompose fa) = MultiCompose _
