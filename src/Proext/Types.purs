module Proext.Types where

import Prelude

type ProNat p q = forall a b. p a b -> q a b

infixr 0 type ProNat as :~>
