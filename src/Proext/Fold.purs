module Proext.Fold
  ( Fold, Foldr, FoldM
  , runFold, runFoldr, runFoldM
  , runFold'
  , mkFold, mkFoldr, mkFoldM
  , mkFold'

  , fold
  , foldr
  , scanl
  , scanr
  , foldM

  , distributed
  , mconcat
  , foldMap

  , head
  , last

  , null
  , length

  , and
  , or
  , any
  , all

  , sum
  , product

  , maximum
  , maximumBy
  , minimum
  , minimumBy

  , elem
  , notElem
  , find
  , elemIndex
  , findIndex
  , lookup

  , filtering
  , interspersing
  , oneOf
  , generalize

  , mapA_
  , sink
  , hoists
  ) where

import Prelude

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Control.Comonad (class Comonad, extract)
import Control.Extend (class Extend, duplicate, extend)
import Control.Plus (class Plus, alt, empty)

import Data.Either (Either(..), either)
import Data.Distributive (class Distributive, cotraverse, distribute)
import Data.Foldable as F
import Data.Foldable (class Foldable)
import Data.Function (applyFlipped)
import Data.HeytingAlgebra (ff, tt)
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid (class Monoid, mempty)
import Data.Profunctor (class Profunctor, dimap, lmap)
import Data.Profunctor.Choice (class Choice, left, right)
import Data.Profunctor.Closed (class Closed, closed)
import Data.Tuple (Tuple(..))
import Data.Traversable (class Traversable)
import Data.Traversable as T

import Unsafe.Coerce (unsafeCoerce)

-- | Run Fold by providing foldable container
fold :: forall f a b. Foldable f => Fold a b -> f a -> b
fold fo t = fo # runFold \k h z -> k (F.foldl h z t)

-- | Run `Foldr` by providing foldable container
foldr :: forall f a b. Foldable f => Foldr a b -> f a -> b
foldr fo t = fo # runFoldr \k h z -> k (F.foldr h z t)

-- | Like 'fold', but monadic.
foldM :: forall m f a b. Foldable f => Monad m => FoldM m a b -> f a -> m b
foldM fo t = fo # runFoldM step
  where
  step :: forall x. (x -> m b) -> (x -> a -> m x) -> m x -> m b
  step k h z = F.foldl h' z t >>= k
    where
      h' x a = x >>= \r -> h r a

-- | Run a `Fold` by providing a `Traversable` container of inputs
scanl :: forall f a b. Traversable f => Fold a b -> f a -> f b
scanl fo t = fo # runFold \k h z -> map k (T.scanl h z t)

-- | Run a `Foldr` by providing a `Traversable` container of inputs
scanr :: forall f a b. Traversable f => Foldr a b -> f a -> f b
scanr fo t = fo # runFoldr \k h z -> map k (T.scanr h z t)

-- | Fold over entire collections of inputs, producing a collection of outputs.
distributed :: forall f a b. Distributive f => Fold a b -> Fold (f a) (f b)
distributed = dimap applyFlipped (flip cotraverse id) <<< closed

-- | Fold all values within a container using 'mappend' and 'mempty'
mconcat :: forall m. Monoid m => Fold m m
mconcat = mkFold id append mempty

-- | Convert a foldMap to Foldl
foldMap :: forall a b m. Monoid m => (a -> m) -> (m -> b) -> Fold a b
foldMap to from = mkFold from (\x a -> append x (to a)) mempty

-- | A `Fold` which remembers the first input.
head :: forall a. Fold a (Maybe a)
head = mkFold' Nothing (\m a -> m <|> Just a)

-- | A `Fold` which keeps the last input.
last :: forall a. Fold a (Maybe a)
last = mkFold' Nothing (\_ a -> Just a)

-- | Returns 'True' if the container is empty, 'False' otherwise
null :: forall a. Fold a Boolean
null = mkFold' true (\_ _ -> false)

-- | Return the length of the container
length :: forall a s. Semiring s => Fold a s
length = mkFold' zero (\n _ -> n + one)

-- | Returns 'True' if all elements are 'True', 'False' otherwise. Generalized
-- | to work with an arbitrary `HeytingAlgebra
and :: forall b. HeytingAlgebra b => Fold b b
and = mkFold' tt conj

-- | Returns 'True' if any element is 'True', 'False' otherwise. Generalized
-- | to work  with an arbitrary `HeytingAlgebra`
or :: forall b. HeytingAlgebra b => Fold b b
or = mkFold' ff disj

-- | Test if `all` of its inputs satisfy some predicate. Generalized to work
-- | with an arbitrary `HeytingAlgebra`
all :: forall a b. HeytingAlgebra b => (a -> b) -> Fold a b
all pred = lmap pred and

-- | Test if `any` of its inputs satisfy some predicate
any :: forall a b. HeytingAlgebra b => (a -> b) -> Fold a b
any pred = lmap pred or

-- | Computes the sum of all elements, Generalized to work with an arbitrary Semiring
sum :: forall s. Semiring s => Fold s s
sum = mkFold' zero add

-- | Computes the product of all elements, Generalized to work with an arbitrary Semiring
product :: forall s. Semiring s => Fold s s
product = mkFold' one mul

-- | Computes the maximum element, Generalized to work with an arbitrary `Ord`
maximum :: forall a. Ord a => Fold a (Maybe a)
maximum = maximumBy compare

-- | Computes the maximum element with respect to the given comparison function
maximumBy :: forall a. (a -> a -> Ordering) -> Fold a (Maybe a)
maximumBy cmp = mkFold' Nothing max'
  where
  max' Nothing x  = Just x
  max' (Just x) y = Just (if cmp x y == GT then x else y)

-- | Computes the minimum element, Generalized to work with an arbitrary `Ord`
minimum :: forall a. Ord a => Fold a (Maybe a)
minimum = minimumBy compare

-- | Computes the minimum element with respect to the given comparison function
minimumBy :: forall a. (a -> a -> Ordering) -> Fold a (Maybe a)
minimumBy cmp = mkFold' Nothing min'
  where
  min' Nothing x = Just x
  min' (Just x) y = Just (if cmp x y == LT then x else y)

-- | Returns 'true' if the container has an element equal to `a`, false otherwise
elem :: forall a. Eq a => a -> Fold a Boolean
elem a = any (_ == a)

-- | Returns `false` if the container has an element equal to `a`, false otherwise
notElem :: forall a. Eq a => a -> Fold a Boolean
notElem a = all (_ /= a)

-- | Returns the first element that satisfies the predicate or Nothing if no element
-- | satisfies the predicate
find :: forall a. (a -> Boolean) -> Fold a (Maybe a)
find pred = mkFold' Nothing step
  where
  step Nothing a    = if pred a then Just a else Nothing
  step x@(Just _) _ = x

-- | returns the index of the first element that equals `a`
elemIndex :: forall a. Eq a => a -> Fold a (Maybe Int)
elemIndex a = findIndex (_ == a)

-- | Return the index of the first element that satisfies the predicate
findIndex :: forall a. (a -> Boolean) -> Fold a (Maybe Int)
findIndex pred = mkFold (either (const Nothing) Just) step (Left 0)
  where
  step (Left i) a    = if pred a then Right i else Left (i + 1)
  step x@(Right _) _ = x

-- | Lookup an input of Tuple that equals to `a` in its first component, and returns
-- | the second component.
lookup :: forall a b. Eq a => a -> Fold (Tuple a b) (Maybe b)
lookup a' = mkFold' Nothing step
  where
  step Nothing (Tuple a b) = if a == a' then Just b else Nothing
  step x@(Just _) _        = x

-- | Filter the input of `Foldl`, the step will be called when the predicate return
-- | true.
filtering :: forall a b. (a -> Boolean) -> Fold a b -> Fold a b
filtering p = runFold \k h z -> mkFold k (\r a -> if p a then h r a else r) z

-- | intersperse the input of `Fold`
interspersing :: forall a b. a -> Fold a b -> Fold a b
interspersing a = runFold \k h z ->
  let
    h' Nothing b  = Just (h z b)
    h' (Just x) b = Just (h (h x a) b)
  in mkFold (maybe (k z) k) h' Nothing

mapA_ :: forall m a. Applicative m => (a -> m Unit) -> FoldM m a Unit
mapA_ = sink

sink :: forall m w a. Applicative m => Monoid w => (a -> m w) -> FoldM m a w
sink act = mkFoldM pure step (pure mempty)
  where
  step m a = append m <$> act a

generalize :: forall m a b. Applicative m => Fold a b -> FoldM m a b
generalize = runFold \k h z -> mkFoldM (pure <<< k) (\x -> pure <<< h x) (pure z)

hoists :: forall m n a b. (m ~> n) -> FoldM m a b -> FoldM n a b
hoists p = runFoldM \k h z -> mkFoldM (p <<< k) (\a -> p <<< h a) (p z)

-- | Combines all elements using the `Alt` operation.
oneOf :: forall f a. Plus f => Foldr (f a) (f a)
oneOf = mkFoldr id alt empty

--------------------------------------------------------------------------------
-- Fold profunctor ------------------------------------------------------------
--------------------------------------------------------------------------------

-- | A left folds applicative. It also a profunctor

data FoldX a b x = FoldX (x -> b) (x -> a -> x) x

foreign import data Fold :: Type -> Type -> Type

mkFold :: forall a b x. (x -> b) -> (x -> a -> x) -> x -> Fold a b
mkFold k h x = unsafeCoerce (FoldX k h x)

mkFold' :: forall a b. b -> (b -> a -> b) -> Fold a b
mkFold' b f = mkFold id f b

unFoldX :: forall a b r. (forall x. FoldX a b x -> r) -> Fold a b -> r
unFoldX = unsafeCoerce

-- | Run a fold to accept the 'Foldl' type
runFold :: forall a b r. (forall x. (x -> b) -> (x -> a -> x) -> x -> r) -> Fold a b -> r
runFold f = unFoldX \(FoldX k h z) -> f k h z

-- | Run a traditional fold to accept `Foldl`
runFold' :: forall a b. (forall x. (x -> a -> x) -> x -> x) -> Fold a b -> b
runFold' f = runFold \k h z -> k (f h z)

instance profunctorFold :: Profunctor Fold where
  dimap f g = runFold \k h z -> mkFold (g <<< k) (\r -> h r <<< f) z

instance choiceFold :: Choice Fold where
  left = runFold \k h z ->
    let
      step (Left x) (Left y) = Left (h x y)
      step (Right c) _ = Right c
      step _ (Right c) = Right c
    in mkFold (left k) step (Left z)

  right = runFold \k h z ->
    let
      step (Right x) (Right y) = Right (h x y)
      step (Left c) _ = Left c
      step _ (Left c) = Left c
    in mkFold (right k) step (Right z)

instance functorFold :: Functor (Fold a) where
  map f = runFold \k h z -> mkFold (f <<< k) h z

instance extendFold :: Extend (Fold a) where
  extend f = runFold \k h z -> mkFold (f <<< mkFold k h) h z

instance comonadFold :: Comonad (Fold a) where
  extract = runFold \k _ z -> k z

instance applyFold :: Apply (Fold a) where
  apply ff fo =
    runFold (\xf bxx xz ->
      runFold (\ya byy yz ->
        mkFold
          (\(Tuple x y) -> xf x $ ya y)
          (\(Tuple x y) b -> Tuple (bxx x b) (byy y b))
          (Tuple xz yz)) fo) ff

instance applicativeFold :: Applicative (Fold a) where
  pure a = mkFold (\_ -> a) (\_ _ -> unit) unit

instance distributiveFold :: Distributive (Fold a) where
  distribute = mkFold (map extract) (\fm a -> map (run a <<< duplicate) fm)
    where
    run t = runFold \k h z -> k (h z t)
  collect f   = distribute <<< map f

instance closedFold :: Closed Fold where
  closed = runFold \k h z -> mkFold (\f x -> k (f x)) (lift2 h) (pure z)

--------------------------------------------------------------------------------
-- Foldr -----------------------------------------------------------------------
--------------------------------------------------------------------------------

-- | right folds
data FoldrX a b x = FoldrX (x -> b) (a -> x -> x) x

foreign import data Foldr :: Type -> Type -> Type

mkFoldr :: forall a b x. (x -> b) -> (a -> x -> x) -> x -> Foldr a b
mkFoldr k h z = unsafeCoerce (FoldrX k h z)

unFoldr :: forall a b r. (forall x. FoldrX a b x -> r) -> Foldr a b -> r
unFoldr = unsafeCoerce

runFoldr :: forall a b r. (forall x. (x -> b) -> (a -> x -> x) -> x -> r) -> Foldr a b -> r
runFoldr f = unFoldr \(FoldrX k h z) -> f k h z

instance profunctorFoldr :: Profunctor Foldr where
  dimap f g = runFoldr \k h z -> mkFoldr (g <<< k) (h <<< f) z

instance choiceFoldr :: Choice Foldr where
  left = runFoldr \k h z ->
    let
      step (Left x) (Left y) = Left (h x y)
      step (Right c) _ = Right c
      step _ (Right c) = Right c
    in mkFoldr (left k) step (Left z)

  right = runFoldr \k h z ->
    let
      step (Right x) (Right y) = Right (h x y)
      step (Left c) _ = Left c
      step _ (Left c) = Left c
    in mkFoldr (right k) step (Right z)

instance closedFoldr :: Closed Foldr where
  closed = runFoldr \k h z -> mkFoldr (\f x -> k (f x)) (lift2 h) (pure z)

instance functorFoldr :: Functor (Foldr a) where
  map f = runFoldr \k h z -> mkFoldr (f <<< k) h z

instance applyFoldr :: Apply (Foldr a) where
  apply ff fa =
    runFoldr (\xf bxx xz ->
      runFoldr (\ya byy yz ->
        mkFoldr
          (\(Tuple x y) -> xf x $ ya y)
          (\b (Tuple x y) -> Tuple (bxx b x) (byy b y))
          (Tuple xz yz)) fa) ff

instance applicativeFoldr :: Applicative (Foldr a) where
  pure a = mkFoldr (\_ -> a) (\_ _ -> unit) unit

instance extendFoldr :: Extend (Foldr a) where
  extend f = runFoldr \k h z -> mkFoldr (f <<< mkFoldr k h) h z

instance comonadFoldr :: Comonad (Foldr a) where
  extract = runFoldr \k _ z -> k z

instance distributiveFoldr :: Distributive (Foldr a) where
  distribute = mkFoldr (map extract) (map <<< extend <<< run)
    where
      run t = runFoldr \k h z -> k (h t z)
  collect f = distribute <<< map f

--------------------------------------------------------------------------------
-- Foldl in Applicative functor ------------------------------------------------
--------------------------------------------------------------------------------

data FoldXM f a b x = FoldXM (x -> f b) (x -> a -> f x) (f x)

foreign import data FoldM :: (Type -> Type) -> Type -> Type -> Type

mkFoldM :: forall f a b x. (x -> f b) -> (x -> a -> f x) -> f x -> FoldM f a b
mkFoldM k h z = unsafeCoerce (FoldXM k h z)

unFoldXM :: forall f a b r. (forall x. FoldXM f a b x -> r) -> FoldM f a b -> r
unFoldXM = unsafeCoerce

runFoldM :: forall f a b r. (forall x. (x -> f b) -> (x -> a -> f x) -> f x -> r) -> FoldM f a b -> r
runFoldM f = unFoldXM \(FoldXM k h z) -> f k h z

instance functorFoldM :: Functor f => Functor (FoldM f a) where
  map f = runFoldM \k h z -> mkFoldM (map f <<< k) h z

instance applyFoldM :: Apply f => Apply (FoldM f a) where
  apply ff fa =
    runFoldM (\xf bxx xz ->
      runFoldM (\ya byy yz ->
        mkFoldM
          (\(Tuple x y) -> xf x <*> ya y)
          (\(Tuple x y) b -> lift2 Tuple (bxx x b) (byy y b))
          (lift2 Tuple xz yz)) fa) ff

instance applicativeFoldM :: Applicative f => Applicative (FoldM f a) where
  pure a = mkFoldM (\_ -> pure a) (\_ _ -> pure unit) (pure unit)

instance profunctorFoldM :: Functor f => Profunctor (FoldM f) where
  dimap f g = runFoldM \k h z -> mkFoldM (map g <<< k) (\r -> h r <<< f) z

instance choiceFoldM :: Applicative f => Choice (FoldM f) where
  left = runFoldM \k h z ->
    let
      h' (Left x) (Left y) = map Left (h x y)
      h' (Right c) _ = pure $ Right c
      h' _ (Right c) = pure $ Right c
    in mkFoldM (either (map Left <<< k) (pure <<< Right)) h' (Left <$> z)

  right = runFoldM \k h z ->
    let
      h' (Right x) (Right y) = map Right (h x y)
      h' (Left c) _ = pure $ Left c
      h' _ (Left c) = pure $ Left c
    in mkFoldM (either (pure <<< Left) (map Right <<< k)) h' (Right <$> z)
