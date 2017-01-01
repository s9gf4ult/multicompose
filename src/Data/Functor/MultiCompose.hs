module Data.Functor.MultiCompose where

class Apply functors applied | functors -> applied, applied -> functors

data MultiCompose (f :: [* -> *]) a = MultiCompose
