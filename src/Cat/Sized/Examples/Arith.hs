{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{- | The source for this module is a minimal example of using this package; the
Haddocks are not meant to be a substitute for viewing the source.

This module is meant as a minor step beyond the gentler introduction or
sized-product-free baseline of the 'Cat.Unsized.Examples.Arith' module; see that
module or the 'Razor' example in the README for additional context on what is
here and why.

Neither this nor the 'unsized' variation on Hutton's Razor document or explain
everything one might want to know about why things are the way they are in the
module: for example, the role of object constraints and how the 'HasObject'
typeclass (or the 'ObjectOf' associated type synonym) link a primitive morphism
to the object constraints for a free category type. For deeper exposition on
details like this, see the introduction to Boolean circuits (combinational
logic) in "Cat.Sized.Examples.Circuit" or the discussion in the README. -}

module Cat.Sized.Examples.Arith where

import Prelude hiding
  ( and
  , or
  , not
  , (.)
  , id
  , foldMap
  )
import Control.Arrow ((<<<))

import Data.Kind
  ( Type
  )
import GHC.TypeNats
  ( KnownNat
  , Nat
  )


import Data.Bool hiding (not)

import Cat.Sized.Semigroupoid.Class
  ( Sized ( Sized )
  )

import Cat.Sized.Semigroupoid.Instances ()
import Cat.Sized.Category.Instances ()

import Cat.Sized.Semigroupoid.Free.Data
   ( HasObject ( ObjectOf
               )
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


-- One of the first differences you'll note is explicit kind annotations — and
-- further down — more constraints:
--
-- 1. A product functor has kind @Nat → κ → κ@ for some kind @κ@.
-- 2. A monoidal category has kind @(Nat → κ → κ) → Nat → Nat → κ → κ → Type@.
--
-- Why not specialize @κ@ to just @Type@?
--
-- In an earlier prototype for what became this package, I modeled Boolean
-- functions as a category with an anonymous /n/-ary product, with morphisms of
-- kind @Nat → Nat → Type@. This example suggested the value of kind
-- polymorphism for singletons. There may be other useful reasons for kind
-- polymorphism, but I haven't enountered them yet, and more salient reasons why
-- maintaining this polymorphism might be appealing turned to be irrelevant as
-- long as (kind- polymorphic) type families can't be partially applied.
--
-- In the meantime, a leading explicit kind parameter is a frequently recurring
-- (and annoying) extra layer of verbosity when trying to use type applications;
-- at some point, if I don't identify and find compelling use cases for this
-- particular kind polymorphism, I may remove it and specialize @κ@ to @Type@
-- throughout the package. (This would also make "first-class type families"
-- relevant to a much larger proportion of the scope of the package.)

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
                                  , KnownNat  n
                                  )



type FreeArith = Cat ArithFunc

noOp ∷ (ObjectOf φ ArithFunc n a)
  ⇒ FreeArith φ n n a a
noOp = Id

one ∷  FreeArith φ 0 1 () Int
one = Emb $ Lit 1

two ∷ FreeArith φ 0 1 () Int
two = Emb $ Lit 2

sub1 ∷ FreeArith φ 1 1 Int Int
sub1 = Emb Dec

alsoOne ∷ FreeArith φ 0 1 () Int
alsoOne = sub1 `Of` two

alsoOneIsOne ∷ FreeArith φ 0 1 () Bool
alsoOneIsOne = Emb (EqlTo 1) `Of` alsoOne

boolToInt ∷ FreeArith φ 1 1 Bool Int
boolToInt = Emb (Ite 0 1)

alsoOneIsOne' ∷ FreeArith φ 0 1 () Int
alsoOneIsOne' = boolToInt `Of` alsoOneIsOne `Of` noOp



evalArithPrimV ∷ ∀ φ (n ∷ Nat) (m ∷ Nat) a b.
  ( ObjectOf φ ArithFunc n a
  , ObjectOf φ ArithFunc m b
  )
  ⇒ ArithFunc    φ         n m a b
  → (Sized (->)) VS.Vector n m a b
evalArithPrimV (Lit     b) = Sized $ const    (pure b)
evalArithPrimV  Inc        = Sized   (+        1)
evalArithPrimV  Dec        = Sized   (subtract 1)
evalArithPrimV (Add     a) = Sized $ pure <<< (+      a) <<< VS.head
evalArithPrimV (EqlTo   a) = Sized $ pure <<< (==     a) <<< VS.head
evalArithPrimV (Ite   f t) = Sized $ pure <<<  bool f t  <<< VS.head


{- |

>>> import Cat.Sized.Semigroupoid.Class (unSized)
>>> import Data.Maybe (fromJust)
>>> :t (unSized $ evalArith (Emb $ Lit (3 ∷ Int)))
(unSized $ evalArith (Emb $ Lit (3 ∷ Int)))
  :: VS.Vector 0 () -> VS.Vector 1 Int
>>> (unSized $ evalArith (Emb $ Lit (3 ∷ Int))) $ (fromJust $ VS.fromList @0 [()])
Vector [3]
it :: VS.Vector 1 Int
>>> (unSized $ evalArith $ alsoOneIsOne') $ (fromJust $ VS.fromList @0 [()])
Vector [1]
it :: VS.Vector 1 Int
>>> (unSized $ evalArith two) $ pure ()
Vector [2]
it :: VS.Vector 1 Int
-}
evalArith ∷ ∀ n m a b.
          ( ObjectOf VS.Vector ArithFunc n a
          , ObjectOf VS.Vector ArithFunc m b
          )
          ⇒ FreeArith    VS.Vector n m a b
          → (Sized (->)) VS.Vector n m a b
evalArith = foldMap evalArithPrimV
