{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{- | The source for this module is a minimal example of using this package; the
Haddocks are not meant to be a substitute for viewing the source.

The module 'Cat.Sized.Examples.Arith' is a very mild extension of this module
that uses 'sized' (type-level @Nat@-indexed) products. See the 'Razor' example
in the README for additional context about what is here and why.

Neither this nor the 'sized' variation on Hutton's Razor document or explain
everything one might want to know about why things are the way they are in the
module: for example, the role of object constraints and how the 'HasObject'
typeclass (or the 'ObjectOf' associated type synonym) link a primitive morphism
to the object constraints for a free category type. For deeper exposition on
details like this, see the introduction to Boolean circuits (combinational
logic) in "Cat.Sized.Examples.Circuit" or the discussion in the README. -}

module Cat.Unsized.Examples.Arith where

import Prelude hiding
  ( id
  , (.)
  , foldMap
  )

import Data.Bool (bool)

import Cat.Unsized.Functor
  ( Fix ( In
        )
  , cata
  )


import Cat.Unsized.Category.Class
  ( Object
  , Object'
  )

import Cat.Unsized.Category.Free.Data
  ( Cat ( Emb
        , Id
        , Of
        )
  , HasObject ( ObjectOf
              )
  , foldMap
  , CatF ( EmbF
         , IdF
         , OfF
         )
  , Cat'
  , mkAlg
  , fixed
  , unfixed
  )

import Cat.Unsized.Category.Instances ()
import Cat.Unsized.Category.Free.Instances ()



data ArithFunc a b where
  Lit    ∷ (ArithPrim b) ⇒ b   →     ArithFunc ()   b
  Inc    ∷                           ArithFunc Int  Int
  Dec    ∷                           ArithFunc Int  Int
  Add    ∷                 Int →     ArithFunc Int  Int
  EqlTo  ∷ (ArithPrim a) ⇒ a   →     ArithFunc a    Bool
  Ite    ∷ (ArithPrim b) ⇒ b   → b → ArithFunc Bool b

deriving instance (Show (ArithFunc a b))

class (Show x, Eq x) ⇒ ArithPrim x
instance ArithPrim Int
instance ArithPrim Bool
instance ArithPrim ()

instance HasObject ArithFunc where
  type ObjectOf ArithFunc a = ArithPrim a



type FreeArith = Cat ArithFunc


-- | ≈ @id@
noOp ∷ ( Object FreeArith a )
  ⇒ FreeArith a a
noOp = Id

-- | ≈ @const (1 ∷ Int)@
one ∷ FreeArith () Int
one = Emb $ Lit 1

-- | ≈ @const (2 ∷ Int)@
two ∷ FreeArith () Int
two = Emb $ Lit 2

-- | ≈ @subtract (1 ∷ Int)@
sub1 ∷ FreeArith Int Int
sub1 = Emb Dec

-- | ≈ @const (2 - (1 ∷ Int))@
alsoOne ∷ FreeArith () Int
alsoOne = sub1 `Of` two

-- | ≈ @(== 1) ∘ (const (2 - (1 ∷ Int)))@
oneIsOne ∷ FreeArith () Bool
oneIsOne = Emb (EqlTo 1) `Of` alsoOne

-- | ≈ @bool (0 ∷ Int) (1 ∷ Int)@
boolToInt ∷ FreeArith Bool Int
boolToInt = Emb (Ite 0 1)

{- |
@
≈ (bool (0 ∷ Int) (1 ∷ Int))
∘ ((== 1) ∘ (const (2 - (1 ∷ Int))))
∘ id
@
-}
alsoOneIsOne ∷ FreeArith () Int
alsoOneIsOne = boolToInt `Of` oneIsOne `Of` noOp



evalArithPrim ∷ ∀ a b.
    ArithFunc a b
  → (a → b)
evalArithPrim (Lit     b) = const    b
evalArithPrim  Inc        = (+       1)
evalArithPrim  Dec        = subtract 1
evalArithPrim (Add     a) = (+       a)
evalArithPrim (EqlTo   a) = (==      a)
evalArithPrim (Ite   f t) = bool   f t


{- |
>>> :t evalFreeArith (Emb $ Lit True)
evalFreeArith (Emb $ Lit True) :: () -> Bool
>>> evalFreeArith (Emb $ Lit True) $ ()
True
it :: Bool
>>> evalFreeArith alsoOneIsOne $ ()
1
it :: Int
-}
evalFreeArith ∷ ∀ a b.
              ( Object FreeArith a
              , Object FreeArith b
              )
              ⇒ FreeArith a b
              → (a → b)
evalFreeArith = foldMap evalArithPrim



-- Once more, but with recursion schemes — catamorphisms in the category of
-- categories.

{- |
> Cat' ArithFunc = Fix (CatF ArithFunc)
> Cat' ArithFunc ≅ Cat ArithFunc
 -}
type FreeArith' = Cat' ArithFunc
type FreeArithF = CatF ArithFunc


-- | ≈ @id@
noOp' ∷ ( Object FreeArith' a )
  ⇒ FreeArith' a a
noOp' = In IdF

-- | ≈ @const (1 ∷ Int)@
one' ∷ FreeArith' () Int
one' = In $ EmbF $ Lit 1

-- | ≈ @const (2 ∷ Int)@
two' ∷ FreeArith' () Int
two' = In $ EmbF $ Lit 2

-- | ≈ @subtract (1 ∷ Int)@
sub1' ∷ FreeArith' Int Int
sub1' = In $ EmbF Dec

-- | ≈ @const (2 - (1 ∷ Int))@
alsoOne' ∷ FreeArith' () Int
alsoOne' = In $ sub1' `OfF` two'

-- | ≈ @(== 1) ∘ (const (2 - (1 ∷ Int)))@
oneIsOne' ∷ FreeArith' () Bool
oneIsOne' = In $ In (EmbF (EqlTo 1)) `OfF` alsoOne'

-- | ≈ @bool (0 ∷ Int) (1 ∷ Int)@
boolToInt' ∷ FreeArith' Bool Int
boolToInt' = In $ EmbF (Ite 0 1)

{- |
@
≈ (bool (0 ∷ Int) (1 ∷ Int))
∘ ((== 1) ∘ (const (2 - (1 ∷ Int))))
∘ id
@
-}
alsoOneIsOne' ∷ FreeArith' () Int
alsoOneIsOne' = In $ boolToInt' `OfF` In (oneIsOne' `OfF` noOp')


{- |

>>> :t evalFreeArith' $ In $ EmbF $ Lit True
evalFreeArith' $ In $ EmbF $ Lit True :: () -> Bool
>>> evalFreeArith' (In $ EmbF $ Lit True) $ ()
True
it :: Bool
>>> evalFreeArith' alsoOneIsOne' $ ()
1
it :: Int
-}
evalFreeArith' ∷ ∀ a b.
  (∀ x. Object FreeArith' x ⇒ Object' (->) x)
  ⇒ FreeArith' a b
  → (a → b)
evalFreeArith' = cata $ mkAlg evalArithPrim


{- | Evaluate @FreeArith'@ morphisms by first converting them via a catamorphism
('unfixed') to @FreeArith@ morphisms.

>>> :t evalFreeArithUnfixed' $ In $ EmbF $ Lit True
evalFreeArithUnfixed' $ In $ EmbF $ Lit True :: () -> Bool
>>> (evalFreeArithUnfixed' (In $ EmbF $ Lit True)) $ ()
True
>>> (evalFreeArithUnfixed' alsoOneIsOne') $ ()
True
-}
evalFreeArithUnfixed' ∷ ∀ a b.
  (Object FreeArith' a, Object FreeArith' b)
  ⇒ FreeArith' a b
  → (a → b)
evalFreeArithUnfixed' f = evalFreeArith $ unfixed f



{- | Evaluate @FreeArith@ morphisms by first converting them via an anamorphism
('fixed') to @FreeArith'@ morphisms.

>>> :t (evalFreeArithFixed (Emb $ Lit (3 :: Int)))
(evalFreeArithFixed (Emb $ Lit (3 :: Int))) :: () -> Int
>>> evalFreeArithFixed (Emb $ Lit (3 :: Int)) $ ()
3
>>> (evalFreeArithFixed $ alsoOneIsOne) ()
1
>>> (evalFreeArithFixed two) $ ()
2
-}
evalFreeArithFixed ∷ ∀ a b.
  (∀ x. Object FreeArith x ⇒ Object' (->) x)
  ⇒ FreeArith a b
  → (a → b)
evalFreeArithFixed f = evalFreeArith' $ fixed f
