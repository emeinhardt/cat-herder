{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{- | The source for this module is a minimal example of using this package; the
Haddocks are not meant to be a substitute for viewing the source. -}

module Cat.Sized.Examples.Arith where

-- import Prelude qualified as P
import Prelude.Unicode ((∘))
import Prelude hiding
  ( and
  , or
  , not
  , (.)
  , id
  , foldMap
  )

-- import GHC.Generics (Generic)
-- import Data.Coerce (coerce)
import Data.Kind
  ( Type
  -- , Constraint
  )
import GHC.TypeNats
  ( KnownNat
  , Nat
  -- , SNat
  -- , type (+)
  -- , type (*)
  )


import Data.Bool hiding (not)
-- import Data.Maybe (fromMaybe, fromJust)
-- import Data.Foldable qualified as FO
-- import Data.Functor  qualified as F

-- import Control.Functor.Constrained.Extras
--   ( Functor
--   , fmap
--   )

-- import Cat.Operators
--   ( type (-|)
--   , type (|->)
--   )


import Cat.Sized.Semigroupoid.Class
  ( -- Object
  -- , Object'
    -- Semigroupoid
  -- , (.)
    Sized ( Sized )
  -- , unSized
  )
-- import Cat.Sized.Category.Class

import Cat.Sized.Semigroupoid.Instances ()
import Cat.Sized.Category.Instances ()

-- import Cat.Sized.Category.Free.Data qualified as Cat
import Cat.Sized.Semigroupoid.Free.Data
   ( HasObject ( ObjectOf
               )
   -- , ObjectOf'
   -- , N (N)
   -- , To (To)
   )
import Cat.Sized.Category.Free.Data
  ( Cat ( Id
        , Emb
        , Of
        )
  , foldMap
  )
import Cat.Sized.Semigroupoid.Free.Instances ()
import Cat.Sized.Category.Free.Instances ()

import Data.Vector.Sized qualified as VS



data ArithFunc (φ ∷ Nat → Type → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type) where
  Lit    ∷ (ArithPrim b) ⇒ b →     ArithFunc φ 0 1 ()   b
  Inc    ∷                         ArithFunc φ 1 1 Int  Int
  Dec    ∷                         ArithFunc φ 1 1 Int  Int
  Add    ∷                 Int →   ArithFunc φ 1 1 Int  Int
  EqlTo  ∷ (ArithPrim a) ⇒ a →     ArithFunc φ 1 1 a    Bool
  Ite    ∷ (ArithPrim b) ⇒ b → b → ArithFunc φ 1 1 Bool b

deriving instance (Show (ArithFunc φ n m a b))

class (Show x, Eq x) ⇒ ArithPrim x
instance ArithPrim Int
instance ArithPrim Bool
instance ArithPrim ()

instance HasObject φ ArithFunc where
  type ObjectOf φ ArithFunc n a = ( ArithPrim a
                                  , Applicative (φ n)
                                  , KnownNat n
                                  )



type FreeArith = Cat ArithFunc

noOp ∷ (ObjectOf φ ArithFunc n a)
  ⇒ FreeArith φ n n a a
noOp = Id

one ∷ ( ObjectOf φ ArithFunc 0 ()
      , ObjectOf φ ArithFunc 1 Int
      )
  ⇒ FreeArith φ 0 1 () Int
one = Emb $ Lit 1

two ∷ ( ObjectOf φ ArithFunc 0 ()
      , ObjectOf φ ArithFunc 1 Int
      )
  ⇒ FreeArith φ 0 1 () Int
two = Emb $ Lit 2

sub1 ∷ ( ObjectOf φ ArithFunc 1 Int
       )
  ⇒ FreeArith φ 1 1 Int Int
sub1 = Emb Dec

alsoOne ∷ ( ObjectOf φ ArithFunc 0 ()
          , ObjectOf φ ArithFunc 1 ()
          )
  ⇒ FreeArith φ 0 1 () Int
alsoOne = sub1 `Of` two

alsoOneIsOne ∷ ( ObjectOf φ ArithFunc 0 ()
               , ObjectOf φ ArithFunc 1 ()
               )
  ⇒ FreeArith φ 0 1 () Bool
alsoOneIsOne = Emb (EqlTo 1) `Of` alsoOne

boolToInt ∷ ( ObjectOf φ ArithFunc 1 Bool
            , ObjectOf φ ArithFunc 1 Int
            )
  ⇒ FreeArith φ 1 1 Bool Int
boolToInt = Emb (Ite 0 1)

alsoOneIsOne' ∷ ( ObjectOf φ ArithFunc 0 ()
                , ObjectOf φ ArithFunc 1 Int
                )
  ⇒ FreeArith φ 0 1 () Int
alsoOneIsOne' = boolToInt `Of` alsoOneIsOne `Of` noOp



instance HasObject VS.Vector (Sized (->))

evalArithPrimV ∷ ∀ (n ∷ Nat) (m ∷ Nat) a b.
  ( ObjectOf VS.Vector ArithFunc n a
  , ObjectOf VS.Vector ArithFunc m b
  -- , Object   VS.Vector (Sized (->)) n a
  -- , Object   VS.Vector (Sized (->)) m b
  -- , (∀ i x. ObjectOf VS.Vector ArithFunc i x ⇒ Object' VS.Vector (Sized (->)) i x)
  )
  ⇒ ArithFunc  VS.Vector n m a b
  → (Sized (->)) VS.Vector n m a b
evalArithPrimV (Lit @b_ @VS.Vector  b) =
  Sized $ const @(VS.Vector 1 b_) @(VS.Vector 0 ())   (pure b)
evalArithPrimV  Inc            = Sized   (+        1)
evalArithPrimV  Dec            = Sized   (subtract 1)
evalArithPrimV (Add   @a_ a  ) = Sized $ pure ∘ (+      a) ∘ VS.head
evalArithPrimV (EqlTo @a_ a  ) = Sized $ pure ∘ (==     a) ∘ VS.head
evalArithPrimV (Ite   @b_ f t) = Sized $ pure ∘  bool f t  ∘ VS.head

{- |

>>> :t (unSized $ evalArith (Emb $ Lit (3 ∷ Int)))
(unSized $ evalArith (Emb $ Lit (3 ∷ Int)))
  :: VS.Vector 0 () -> VS.Vector 1 Int
>>> (unSized $ evalArith (Emb $ Lit (3 ∷ Int))) $ (fromJust $ VS.fromList @0 [()])
Vector [3]
it :: VS.Vector 1 Int
>>> (unSized $ evalArith $ alsoOneIsOne') $ (fromJust $ VS.fromList @0 [()])
Vector [1]
it :: VS.Vector 1 Int
-}
evalArith ∷ ∀ n m a b.
          ( ObjectOf VS.Vector ArithFunc n a
          , ObjectOf VS.Vector ArithFunc m b
          -- , ∀ i o. ObjectOf VS.Vector ArithFunc i o ⇒ Object' VS.Vector (Sized (->)) i o
          )
          ⇒ FreeArith  VS.Vector  n m a b
          → (Sized (->)) VS.Vector n m a b
evalArith = foldMap evalArithPrimV
