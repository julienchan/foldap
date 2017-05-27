module Proext.Compose
  ( Procompose
  , procompose
  , unProcompose
  ) where

import Prelude

import Data.Exists (Exists, runExists, mkExists)
import Data.Profunctor (class Profunctor, rmap, lmap)
import Data.Profunctor.Strong (class Strong, first, second)
import Data.Profunctor.Choice (class Choice, left, right)
import Data.Profunctor.Closed (class Closed, closed)

data ProcomposeX p q a b x = ProcomposeX (p x b) (q a x)

newtype Procompose p q a b = Procompose (Exists (ProcomposeX p q a b))

procompose :: forall p q a b x. p x b -> q a x -> Procompose p q a b
procompose p q = Procompose (mkExists (ProcomposeX p q))

unProcompose :: forall p q a b r. (forall x. p x b -> q a x -> r) -> Procompose p q a b -> r
unProcompose r (Procompose x) = x # runExists \(ProcomposeX f g) -> r f g

instance profunctorProcompose :: (Profunctor p, Profunctor q) => Profunctor (Procompose p q) where
  dimap l r (Procompose x) = x # runExists \(ProcomposeX f g) -> procompose (rmap r f) (lmap l g)

instance functorProcompose :: Profunctor p => Functor (Procompose p q a) where
  map f (Procompose x) = x # runExists \(ProcomposeX g h) -> procompose (rmap f g) h

instance strongProcompose :: (Strong p, Strong q) => Strong (Procompose p q) where
  first (Procompose x)  = x # runExists \(ProcomposeX f g) -> procompose (first f) (first g)
  second (Procompose x) = x # runExists \(ProcomposeX f g) -> procompose (second f) (second g)

instance choiceProcompose :: (Choice p, Choice q) => Choice (Procompose p q) where
  left (Procompose x)  = x # runExists \(ProcomposeX f g) -> procompose (left f) (left g)
  right (Procompose x) = x # runExists \(ProcomposeX f g) -> procompose (right f) (right g)

instance closedProcompose :: (Closed p, Closed q) => Closed (Procompose p q) where
  closed (Procompose x) = x # runExists \(ProcomposeX f g) -> procompose (closed f) (closed g)
