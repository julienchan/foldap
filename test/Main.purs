module Test.Main where

import Prelude
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log, logShow)

import Foldap.Foldl as Foldl

average :: forall s. EuclideanRing s => Foldl.Foldl s s
average = (/) <$> Foldl.sum <*> Foldl.length

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  logShow (Foldl.scanl average [1.0, 2.0, 3.0, 4.0, 5.0])
  log "You should add some tests."
