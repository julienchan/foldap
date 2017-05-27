module Proext.Free
  ( FreePro
  , liftFreePro
  , runPro
  , freePro

  , FreeArr
  , liftFreeArr
  , runFreeArr
  , comp
  , hom

  , Arr
  , liftArr
  , runArr
  ) where

import Prelude

import Data.Profunctor (class Profunctor, rmap, lmap, dimap, arr)
import Data.Profunctor.Strong (class Strong, (***), first)
import Data.Profunctor.Choice (class Choice, left)
import Data.Tuple (Tuple(..))
import Data.Exists (Exists, runExists, mkExists)
import Data.Either (Either(..), either)

import Unsafe.Coerce (unsafeCoerce)

import Proext.Types (type (:~>))


type Arr p = FreeArr (FreePro p)

liftArr :: forall p . p :~> Arr p
liftArr p = comp (liftFreePro p) (hom id)

liftFreeArr :: forall p. p :~> FreeArr p
liftFreeArr p = comp p (hom id)

liftFreePro :: forall p a b. p a b -> FreePro p a b
liftFreePro p = freePro id id p

runPro :: forall p q. Profunctor q => (p :~> q) -> FreePro p :~> q
runPro f = unFreePro \l g r -> dimap l r (f g)

runFreeArr :: forall p q. Category q => Profunctor q => (p :~> q) -> FreeArr p :~> q
runFreeArr _ (Hom g)  = arr g
runFreeArr f (Comp c) = c # runExists \(CompX x y) -> runFreeArr f y <<< f x

runArr :: forall p q. Category q => Profunctor q => (p :~> q) -> Arr p :~> q
runArr f = runFreeArr (runPro f)

-- | A Free Profunctor for any data type
data FreeProX p a b x y = FreeProX (a -> x) (p x y) (y -> b)

foreign import data FreePro :: (Type -> Type -> Type) -> Type -> Type -> Type

-- | construct free profunctor
freePro :: forall p a b x y. (a -> x) -> (y -> b) -> p x y -> FreePro p a b
freePro f g p = unsafeCoerce (FreeProX f p g)

unFreePro_ :: forall p a b r. (forall x y. FreeProX p a b x y -> r) -> FreePro p a b -> r
unFreePro_ = unsafeCoerce

unFreePro :: forall p a b r. (forall x y. (a -> x) -> p x y -> (y -> b) -> r) -> FreePro p a b -> r
unFreePro f = unFreePro_ \(FreeProX k p r) -> f k p r

instance profunctorFreePro :: Profunctor (FreePro p) where
  dimap f g = unFreePro \k p h -> freePro (k <<< f) (g <<< h) p

-- | Turn any profunctor to a Category
data FreeArr p a b
  = Hom (a -> b)
  | Comp (Exists (CompX p a b))

data CompX p a b x = CompX (p a x) (FreeArr p x b)

comp :: forall p a b x. p a x -> FreeArr p x b -> FreeArr p a b
comp p f = Comp (mkExists (CompX p f))

hom :: forall p a b. (a -> b) -> FreeArr p a b
hom = Hom

instance profunctorFreeArr :: Profunctor p => Profunctor (FreeArr p) where
  dimap f g (Hom k)  = hom (g <<< k <<< f)
  dimap f g (Comp e) = e # runExists \(CompX x y) -> comp (lmap f x) (rmap g y)

instance categoryFreeArr :: Profunctor p => Category (FreeArr p) where
  id = hom id

instance semigroupoidFreeArr :: Profunctor p => Semigroupoid (FreeArr p) where
  compose f (Hom g)  = lmap g f
  compose f (Comp e) = e # runExists \(CompX h g) -> comp h (f <<< g)

instance strongFreeArr :: Strong p => Strong (FreeArr p) where
  first (Hom f)  = hom (\(Tuple x z) -> Tuple (f x) z)
  first (Comp e) = runExists (\(CompX x y) -> comp (first x) (first y)) e
  second         = (***) id

instance choiceFreeArr :: Choice p => Choice (FreeArr p) where
  left (Hom f)   = hom (either (Left <<< f) Right)
  left (Comp e)  = runExists (\(CompX x y) -> comp (left x) (left y)) e
  right          = dimap (either Right Left) (either Right Left) <<< left
