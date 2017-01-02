module Data.Functor.MultiCompose where

import Data.Proxy
import TypeFun.Data.List
import TypeFun.Data.Peano

type family Apply (fs :: [* -> *]) (a :: *) :: * where
  Apply '[] a = a
  Apply (f ': fs) a = f (Apply fs a)

type family Deapply (applied :: *) (len :: N) :: [* -> *] where
  Deapply a 'Z = '[]
  Deapply (f rest) ('S len) = f ': (Deapply rest len)

type family AppLen f where
  AppLen (f a) = 'S (AppLen a)
  AppLen a     = 'Z

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
  | functors a -> applied, len applied -> functors, len applied -> a where
  compose :: Proxy len -> applied -> MultiCompose functors a
  decompose :: MultiCompose functors a -> applied

instance Composable' 'Z '[] a a where
  compose _ a = MCSingle a
  decompose (MCSingle a) = a

instance
  ( Composable' len rest restapps a
  , Functor f
  ) =>
  Composable' ('S len) (f ': rest) (f restapps) a where
  compose _ app = MCApply $ fmap (compose (Proxy :: Proxy len)) app
  decompose (MCApply a) = fmap decompose a

type Composable functors applied a =
  Composable' (Length functors) functors applied a

fullCompose
  :: forall fs app a
  .  (Composable' (AppLen app) fs app a)
  => app
  -> MultiCompose fs a
fullCompose = compose (Proxy :: Proxy (AppLen app))

data MultiCompose fs a where
  MCSingle :: a -> MultiCompose '[] a
  MCApply :: f (MultiCompose rest a) -> MultiCompose (f ': rest) a

instance Show a => Show (MultiCompose '[] a) where
  show (MCSingle a) = "MCSingle (" ++ show a ++ ")"

instance
  ( Show (f (MultiCompose rest a))
  ) =>
  Show (MultiCompose (f ': rest) a) where
  show (MCApply a) = "MCAPply (" ++ show a ++ ")"

instance (Eq a) => Eq (MultiCompose '[] a) where
  MCSingle a == MCSingle b = a == b

instance
  ( Eq (f (MultiCompose rest a))
  ) =>
  Eq (MultiCompose (f ': rest) a) where
  MCApply fa == MCApply fb = fa == fb

instance (Ord a) => Ord (MultiCompose '[] a) where
  compare (MCSingle a) (MCSingle b) = compare a b

instance
  ( Ord (f (MultiCompose rest a))
  ) =>
  Ord (MultiCompose (f ': rest) a) where
  compare (MCApply fa) (MCApply fb) = compare fa fb

instance Functor (MultiCompose '[]) where
  fmap f (MCSingle a) = MCSingle $ f a

instance
  ( Functor f, Functor (MultiCompose rest)
  ) =>
  Functor (MultiCompose (f ': rest)) where
  fmap f (MCApply fa) = MCApply $ fmap (fmap f) fa

instance Applicative (MultiCompose '[]) where
  pure = MCSingle
  MCSingle f <*> MCSingle a = MCSingle $ f a

instance
  ( Applicative f, Applicative (MultiCompose rest)
  ) =>
  Applicative (MultiCompose (f ': rest)) where
  pure a = MCApply $ pure $ pure a
  MCApply f <*> MCApply fa =
    let ff = fmap (<*>) f
    in MCApply $ ff <*> fa


-- instance Monad (MultiCompose '[]) where
--   return = pure
--   MCSingle a >>= f = f a

-- TODO: these instances should be banned or done right. Appearantly
-- 'f' should be Identity

-- instance
--   ( Monad f, Comonad f, Monad (MultiCompose rest)
--   ) =>
--   Monad (MultiCompose (f ': rest)) where
--   return = pure
--   (MCApply ma) >>= f =
--     let inner mcra = return $ mcra >>= (\a -> case f a of
--                                            MCApply mb -> extract mb)
--     in MCApply $ ma >>= inner


instance Foldable (MultiCompose '[]) where
  foldr f b (MCSingle a) = f a b

instance
  ( Foldable f, Foldable (MultiCompose rest)
  ) =>
  Foldable (MultiCompose (f ': rest)) where
  foldr f b (MCApply fa) = foldr go b fa
    where
      go mra b' = foldr f b' mra

instance Traversable (MultiCompose '[]) where
  traverse f (MCSingle a) = fmap MCSingle $ f a

instance
  ( Traversable f, Traversable (MultiCompose rest)
  ) =>
  Traversable (MultiCompose (f ': rest)) where
  traverse f (MCApply fa) =
    fmap MCApply $ traverse (traverse f) fa
