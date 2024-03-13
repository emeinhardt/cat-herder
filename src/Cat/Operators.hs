{- | The main operators exported here are infix type operators
[courtesy of u/Iceland_jack](https://www.reddit.com/r/haskell/comments/xdcx08/comment/iog81nv)
that make arrow-like terms with many parameters easier to parse, particularly
when viewing source code, and to a lesser degree in Haddock. -}

module Cat.Operators
  ( (<.)
  , (.>)
  , (⊲)
  , (⊳)
  , type (-|)
  , type (|->)
  -- , (.&)
  -- , (.&&)
  , uc
  , uc3
  , flt3
  , flt4
  , flt3'
  , flt4'
  ) where

-- import Prelude qualified as P
import Prelude hiding
  ( (.)
  )
import Prelude.Unicode
  ((∘))
import Data.Composition
  ( (.:)
  , (.:.)
  )
import Control.Arrow
  ( (>>>)
  , (<<<)
  )

import Data.Function
  ((&), ($))


-- C/o u/Iceland_jack: https://www.reddit.com/r/haskell/comments/xdcx08/arbitrary_expression_in_infix_mode/

infixl 3 -|
type (-|) ∷ a → (a → b) → b
type a -| f = f a

infixl 3 |->
type (|->) ∷ (a → b) → a → b
type f |-> a = f a

-- infixl 4 ~|
-- type (~|) ∷ a → (a → b) → b
-- type a ~| f = f a

-- infixl 4 |~>
-- type (|~>) ∷ (a → b) → a → b
-- type f |~> a = f a


infixl 3 ⊲
(⊲) ∷ a → (a → b) → b
(⊲) = (&)

infixl 3 ⊳
(⊳) ∷ (a → b) → a → b
(⊳) = ($)

infixl 3 <.
(<.) ∷ a → (a → b) → b
(<.) = (&)

infixl 3 .>
(.>) ∷ (a → b) → a → b
(.>) = ($)

-- infixr 9 .&
-- (.&) ∷ (x → y → z) → (w → (x,y)) → (w → z)
-- (.&) g f = P.uncurry g P.. f

-- infixr 9 .&&
-- (.&&) ∷ (x → y → z) → (v → w → (x,y)) → ((v,w) → z)
-- (.&&) g f = P.uncurry g P.. P.uncurry f


uc ∷ (a → b → c) → (a, b) → c
uc = uncurry

uc3 ∷ (a → b → c → d) → (a, b, c) → d
uc3 f = (uc ∘ uc $ f) ∘ flt3'

flt3 ∷ ((a, b), c) → (a,b,c)
flt3 = uc ∘ uc $ (,,)

flt4 ∷ (((a, b), c), d) → (a,b,c,d)
flt4 = uc ∘ uc ∘ uc $ (,,,)

flt3' ∷ (a,b,c) → ((a, b), c)
flt3' (a,b,c) = ((a,b),c)

flt4' ∷ (a,b,c,d) → (((a, b), c),d)
flt4' (a,b,c,d) = (((a,b),c),d)
