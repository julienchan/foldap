module Test.Main where

import Prelude
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log, logShow)

import Proext.Fold as F

average :: forall s. EuclideanRing s => F.Fold s s
average = (/) <$> F.sum <*> F.length

commasep :: F.Fold String String
commasep = F.interspersing ", " F.mconcat

foldMExample :: forall e a. Show a => F.FoldM (Eff (console :: CONSOLE | e)) a Unit
foldMExample = F.mkFoldM done step begin
  where
  begin  = log "Begin foldMExample"
  done _ = log "Done"
  step _ a = logShow a

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  logShow (F.fold commasep ["hello", "word", "purescript"])
  logShow (F.scanl average [1.0, 2.0, 3.0, 4.0, 5.0])
  F.foldM foldMExample [10, 11, 12, 13]
