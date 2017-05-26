module Foldap.Foldl where

import Prelude

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Control.Comonad (class Comonad, extract)
import Control.Extend (class Extend, duplicate)

import Data.Either (Either(..))
import Data.Distributive (class Distributive, cotraverse, distribute)
import Data.Foldable as F
import Data.Foldable (class Foldable)
import Data.Function (applyFlipped)
import Data.HeytingAlgebra (ff, tt)
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid, mempty)
import Data.Profunctor (class Profunctor, dimap, lmap)
import Data.Profunctor.Choice (class Choice, left, right)
import Data.Profunctor.Closed (class Closed, closed)
import Data.Tuple (Tuple(..))
import Data.Traversable (class Traversable)
import Data.Traversable as T

import Unsafe.Coerce (unsafeCoerce)

-- | Run Foldl by providing foldable container
foldl :: forall f a b. Foldable f => Foldable f => Foldl a b -> f a -> b
foldl fo t = fo # runFoldl \k h z -> k (F.foldl h z t)

-- | Run a `Fold` by providing a `Traversable` container of inputs
scanl :: forall f a b. Traversable f => Foldl a b -> f a -> f b
scanl fo t = fo # runFoldl \k h z -> map k (T.scanl h z t)

-- | Fold over entire collections of inputs, producing a collection of outputs.
distributed :: forall f a b. Distributive f => Foldl a b -> Foldl (f a) (f b)
distributed = dimap applyFlipped (flip cotraverse id) <<< closed

-- | Fold all values within a container using 'mappend' and 'mempty'
mconcat :: forall m. Monoid m => Foldl m m
mconcat = mkFoldl id append mempty

-- | Convert a foldMap to Foldl
foldMap :: forall a b m. Monoid m => (a -> m) -> (m -> b) -> Foldl a b
foldMap to from = mkFoldl from (\x a -> append x (to a)) mempty

-- | A `Fold` which remembers the first input.
head :: forall a. Foldl a (Maybe a)
head = mkFoldl_ Nothing (\m a -> m <|> Just a)

-- | A `Fold` which keeps the last input.
last :: forall a. Foldl a (Maybe a)
last = mkFoldl_ Nothing (\_ a -> Just a)

-- | Returns 'True' if the container is empty, 'False' otherwise
null :: forall a. Foldl a Boolean
null = mkFoldl_ true (\_ _ -> false)

length :: forall a s. Semiring s => Foldl a s
length = mkFoldl_ zero (\n _ -> n + one)

and :: forall b. HeytingAlgebra b => Foldl b b
and = mkFoldl_ tt conj

or :: forall b. HeytingAlgebra b => Foldl b b
or = mkFoldl_ ff disj

all :: forall a b. HeytingAlgebra b => (a -> b) -> Foldl a b
all pred = lmap pred and

any :: forall a b. HeytingAlgebra b => (a -> b) -> Foldl a b
any pred = lmap pred or

sum :: forall s. Semiring s => Foldl s s
sum = mkFoldl_ zero add

product :: forall s. Semiring s => Foldl s s
product = mkFoldl_ one mul

maximum :: forall a. Bounded a => Foldl a a
maximum = mkFoldl_ bottom max

minimum :: forall a. Bounded a => Foldl a a
minimum = mkFoldl_ top min

elem :: forall a. Eq a => a -> Foldl a Boolean
elem a = any (_ == a)

notElem :: forall a. Eq a => a -> Foldl a Boolean
notElem a = all (_ /= a)

data FoldlX a b x = FoldlX (x -> b) (x -> a -> x) x

foreign import data Foldl :: Type -> Type -> Type

mkFoldl :: forall a b x. (x -> b) -> (x -> a -> x) -> x -> Foldl a b
mkFoldl done step x = unsafeCoerce (FoldlX done step x)

mkFoldl_ :: forall a b. b -> (b -> a -> b) -> Foldl a b
mkFoldl_ b f = mkFoldl id f b

unFoldX :: forall a b r. (forall x. FoldlX a b x -> r) -> Foldl a b -> r
unFoldX = unsafeCoerce

runFoldl :: forall a b r. (forall x. (x -> b) -> (x -> a -> x) -> x -> r) -> Foldl a b -> r
runFoldl f fo = fo # unFoldX \(FoldlX k h z) -> f k h z

instance profunctorFoldl :: Profunctor Foldl where
  dimap f g fo = fo # runFoldl \k h z -> mkFoldl (g <<< k) (\r -> h r <<< f) z

instance choiceFoldl :: Choice Foldl where
  left fo = fo # runFoldl \k h z ->
    let
      step (Left x) (Left y) = Left (h x y)
      step (Right c) _ = Right c
      step _ (Right c) = Right c
    in mkFoldl (left k) step (Left z)

  right fo = fo # runFoldl \k h z ->
    let
      step (Right x) (Right y) = Right (h x y)
      step (Left c) _ = Left c
      step _ (Left c) = Left c
    in mkFoldl (right k) step (Right z)

instance functorFoldl :: Functor (Foldl a) where
  map f fo = fo # runFoldl \k h z -> mkFoldl (f <<< k) h z

instance extendFoldl :: Extend (Foldl a) where
  extend f fo = fo # runFoldl \k h z -> mkFoldl (f <<< mkFoldl k h) h z

instance comonadFoldl :: Comonad (Foldl a) where
  extract fo = fo # runFoldl \k _ z -> k z

instance applyFoldl :: Apply (Foldl a) where
  apply ff fo =
    runFoldl (\xf bxx xz ->
      runFoldl (\ya byy yz ->
        mkFoldl
          (\(Tuple x y) -> xf x $ ya y)
          (\(Tuple x y) b -> Tuple (bxx x b) (byy y b))
          (Tuple xz yz)
      ) fo) ff

instance applicativeFoldl :: Applicative (Foldl a) where
  pure a = mkFoldl (\_ -> a) (\_ _ -> unit) unit

instance distributiveFoldl :: Distributive (Foldl a) where
  distribute = mkFoldl (map extract) (\fm a -> map (run a <<< duplicate) fm)
    where
    run t fo = fo # runFoldl \k h z -> k (h z t)
  collect f   = distribute <<< map f

instance closedFoldl :: Closed Foldl where
  closed fo = fo # runFoldl \k h z -> mkFoldl (\f x -> k (f x)) (lift2 h) (pure z)