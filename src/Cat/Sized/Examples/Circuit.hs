{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{- | The source for this module is a minimal example of using this package that
includes working with type-level sized products; the Haddocks are an imperfect
substitute for viewing the source, but simplified source has often been included
in docstrings.

The module contains

1. Discussion focused on domain modeling and this package:

   - Definitions of the primitive morphisms and object constraints defining the
     category.
   - Discussion of how typelevel-size-annotated products could interact with
     domain modeling.
   - Discussion of how the package permits customizable constraints for
     categories defined by freely lifting morphisms into some category type.

2. Some examples from the domain. Most definitions have associated usage
   examples in the docstring, and if not, then there is at least one other
   definition showing its use in its docstring.

      - The current examples were chosen to represent a small range of complexity and to
        show use of Cartesian combinators in tacit style.

3. Code showing evaluation of terms into `(->)`. When pretty-printing to GraphViz is
   added, circuit diagrams and code for generating them will be present as well.

== Source conventions

As a first introduction to the package, combinator conventions in this module are:

 - Homophonous ("homographic") synonyms for Prelude combinators are used in 
   expressions in the object language (DSL). For example,

      - @(.)@ refers to "Cat.Sized.Semigroupoid" composition.
      - @id@ refers to the identity morphism from "Cat.Sized.Category".
      - @(***)@ refers to the monoidal tensor product from "Cat.Sized.Monoidal".
      - @(&&&)@ refers to the "fork" operation from "Cat.Sized.Diagonal.Class" —
        except in one or two cases where it is explicitly qualified to indicate
        that the "Control.Arrow" combinator is used instead.

 - "Control.Arrow" operators — '(>>>)', '(<<<)' — are used for composition in
   the metalanguage — @(->)@.

 - @IcelandJack@'s mixfix operator hack (see '-|', '|->') is used to make large
   morphisms a bit more readable, especially in source code:

> -- A morphism in the category k from a to b:
>
>   k a b
> ≡ a `k` b
> ≡ a -| k |-> b
>
>
> -- A morphism from a vector of 3 Bools to a vector of 2 Bools:
>
>   Circuit VS.Vector 3 2 Bool Bool
> ≡ Bool -| Circuit VS.Vector 3 2 |-> Bool
>
> -- Now the source object of the morphism and its multiplicity are on the 
> -- left, and information about the target object and its multiplicity are to 
> -- the right.

Above you see a typical morphism type in this package:

 - Such a morphism /always/ maps from a homogeneously-typed product to a
   homogeneously-typed product, and the monoidal product is part of the type of
   the morphism. 
 - In general though, morphisms don't have to be to and from the same 
   types — a type like @Bool@ doesn't have to show up on both sides, and we can
   have arbitrarily nested products of products.

-}

module Cat.Sized.Examples.Circuit
  ( -- * Primitive morphisms, object constraints, and typeclass instances
    -- | This type models propositional logic (combinational circuits) with two
    -- introduction forms and a relatively complete set of elimination forms
    -- that are gracefully polymorphic in their input size (notably not including
    -- implication).
    Circuit ( InT
            , InF
            , Not
            , Or
            , And
            , Nor
            , Nand
            , Xor
            , Iff
            )
  , FreeCircuit
  , ToBool (toBool)
  , CircuitCarrier

    -- * Example: A simple logical predicate / powerset operation
  , impliesBin
  , impliesElem
  , implies

    -- * Example: Adding unsigned fixed-width integers
    -- | See e.g.
    -- [Adder (electronics)](https://w.wiki/9SJT)
    -- for background.

    -- ** Ripple-carry adder
  , halfAdder
  , fullAdder
  , rippleCarry2'
  , rippleCarry2
  , rippleCarry3'
  , rippleCarry3
  , rippleCarry4'
  , rippleCarry4

    -- ** Carry-lookahead adder
  , fullAdderGP
  , lookahead
  , lookaheadCarryGPs
  , lookaheadCarry1
  , lookaheadCarry2
  , lookaheadCarry3
  , lookaheadCarry4Flat
  , lookaheadCarry4O
  , lookaheadCarryGGP4
  , lookaheadCarry4Unit
  , lookaheadCarry4UnitO
  , lookaheadCarry8Unit
  , lookaheadCarry8UnitO
  , lookaheadCarry16Unit
  , lookaheadCarry16UnitO

    -- * Evaluation
    -- ** @(->)@ analogues for circuit primitives
  , inTF
  , inFF
  , notF
  , orF
  , andF
  , norF
  , nandF
  , iffF
  , xorF
  , evalCircuitPrim
    -- ** Evaluation into @Hask@
  , eval
  , eval'

    -- ** Recursion schemes variants
  , FreeCircuit'
  , FreeCircuitF
  , evalFreeCircuit'
  , evalFreeCircuitUnfixed'
  , evalFreeCircuitFixed
  , impliesBin'
  , impliesElem'
  , implies'

    -- ** Documentation helpers
    -- | As this is a documentation module, these are part of the public
    -- interface essentially to facilitate readability of the docstrings;
    -- not all helpers used are included.
  , numToBools
  , boolsToNum
  , boolsToNumL
  , boolsToNumR
  , bn
  , table
  , table2
  , table2I
  , table2IL
  , table2IR
  , table2B
  ) where

{- TODO

  1. Interpret example circuits into GraphViz.

  2. Interpret example circuits into tensors over the Booleans.
-}

import Prelude qualified as P
import Prelude hiding
  ( (.)
  , id
  , foldMap
  , and
  , or
  , not
  , Functor
  , fmap
  , zip
  , zipWith
  , head
  , tail
  , last
  , init
  , reverse
  , take
  , drop
  )

import Control.Arrow qualified as CA
import Control.Arrow
  ( first
  , (>>>)
  , (<<<)
  )
import Data.Bifunctor
  ( bimap
  )
import Data.Functor  qualified as F

import Data.Kind
  ( Type
  )
import GHC.TypeNats
  ( KnownNat
  , Nat
  , pattern SNat
  , natVal
  )
-- import Data.Finite (Finite)


import Data.Maybe
  ( fromMaybe
  , fromJust
  )
import Data.Foldable qualified as FO


import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Sized.Functor
  ( Fix (In)
  , cata
  )


-- Imports in this example module are intentionally more granular than in the
-- 'Arith' ones to facilitate finding definitions.

import Cat.Sized.Functor.Monoidal
  ( zip
  , zipWith
  )

import Cat.Sized.Semigroupoid.Class
  ( (.)
  , Object
  , Sized ( Sized )
  , unSized
  )
import Cat.Sized.Category.Class
  ( id
  )
import Cat.Sized.Monoidal.Class
  ( (***)
  , join
  , split
  , sing
  , unsing
  , bising
  )
import Cat.Sized.Semicartesian.Class
  ( del
  , tail
  , last
  , suffix
  )
import Cat.Sized.Diagonal.Class
  ( (&&&)
  )
import Cat.Sized.Braided.Class
  ( swap
  )

-- import Cat.VectorSized ()
import Cat.Sized.Cartesian.Instances ()

import Cat.Sized.Cartesian.Free.Data
  ( Cart ( Id
         , Emb
         )
  , foldMap
  , HasObject (ObjectOf)
  , HasProxy
  , HasProj
  , HasDel
  , HasSelect
  , HasProj
  , HasDup 
  , HasSwap
  , Cart'
  , mkAlg
  , CartF ( EmbF
          , IdF
          )
  , fixed
  , unfixed
  )

import Cat.Sized.Cartesian.Free.Instances ()

import Data.Vector.Sized qualified as VS
import Data.Bits qualified as B
import Data.Bits ((.|.), (.&.))



{- | One possible choice for primitive morphisms — if, for instance, we wanted to
reason about hardware defined in terms of a specific subset of gates or reify a
particular kind of normal form, we might only have a subset of what's present
below.

Two other dimensions of variation:

 - This definition uses GADTs to tightly control valid term construction but
   gives up many automatically derivable instances as a consequence.

 - For simplicity of presentation, the only constructors provided mean that
   @Circuit@ arrows can only ever be between @Bool@s, but e.g. if we wanted
   interoperability with a SAT solving package, we might want to relax this
   restriction. This would make the object constraint for the 'FreeCircuit'
   category less trivial.


=== Why might sizes matter in this domain?

For concision, the cardinalities below are generally polymorphic in @Nat@
instead of being e.g. more fixed as in

@
data Circuit (φ ∷ Nat → Type → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type) where
  InT  ∷                Bool -| Circuit φ 0 1 |-> Bool
  InF  ∷                Bool -| Circuit φ 0 1 |-> Bool
  Not  ∷                Bool -| Circuit φ 1 1 |-> Bool
  Or   ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  And  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  Nor  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  Nand ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  Xor  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  Iff  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
@

or completely monomorphized by fixing each @n@ above to @2@.

Why might you prefer what's below ("option 1"), what's above ("option 2"), or
complete monomorphization ("option 3")?

1. /Domain modeling of your object language:/ Option 3 might be better for
   domain modeling — e.g. some hardware-oriented application.

2. /Domain modeling of this package:/ In the context of this package, both #2
   and #3 would be better than #1 if the framework for thinking about
   multi-arity categories you'd prefer to use (e.g. operads) takes many-input
   (i.e. products of objects) single-output (i.e. a single non-product object)
   morphisms as the basic idea rather than many-input many-output morphisms.

3. /Ergonomics and goals of your EDSL:/ The equivalent of the option #1
expression

>>> :t InT @3  -- i.e. the polymorphic InT constructor below
InT @3 ∷ Bool -| Circuit φ 0 3 |-> Bool

under option #2 or #3 requires additional terms: e.g.

>>> inT1 = InT @1 -- simulating in option #1 the InT constructor from #2-3
inT1 ∷ a -| Circuit φ 0 1 |-> b
>>> :t inT1 *** inT1 *** inT1
inT1 *** inT1 *** inT1 ∷ Bool -| Circuit φ 0 3 |-> Bool
>>> :t inT1 &&& inT1 &&& inT1
inT1 &&& inT1 &&& inT1 ∷ Bool -| Circuit φ 0 3 |-> Bool

One of these explicitly uses duplication combinators and both require explicit
construction of a separate term for each output arity @m@: this may be a bother,
may be convenient (consider the ergonomics of recursion schemes that focus on
manipulating term constructors without any type-level fanciness) or something
you want to be able to explicitly and carefully track or control as part of your
EDSL.


=== How do typeclass instances work for freely lifted categories?

Most categorical typeclasses in this module have associated type synonyms that
give you wide latitude to constrain when the typeclass's methods can be used —
e.g. controlling things like copying or deletion, more implementation-specific
constraints like having an @Ord@ instance, or reflecting any other aspect of
your domain where typeclass instance constraints encode properties you want to
model.

To freely lift some set of primitives @Prim@ into a particular kind of category
@K@, you need some way of specifying what these constraints are. In most cases,
each categorical typeclass has an associated @Has\_Object@ typeclass with an
associated type synonym. The provided instances for @FreeK Prim@ are then
parameterized by the constraints provided by a @Has\_Object@ instance.

For example, there is a @HasObject@ instance for @Circuit@ that constrains what
an object of @Cart Circuit@ (@FreeCircuit@) can be:

> instance HasObject φ Circuit where
>   type ObjectOf φ Circuit n a = (KnownNat n , ToBool (CircuitCarrier φ a))


In @Cat.Sized.Cartesian.Free.Instances@, this is used to provide a
@Cat.Sized.Semigroupoid@ instance for @Cart k@:

> instance Semigroupoid (φ ∷ Nat → κ → κ) (Cart (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)) where
>   type Object φ (Cart k) n a = ObjectOf φ k n a
>   (.) = Of


This combination of choices allows

 1. The free cartesian category type (@Cart@) to have default typeclass instances...
 2. ...while also giving you a mechanism for constraining typeclasses.

Finally, because constraints like @ObjectOf@ are associated type synonyms of a
typeclass, they have a default definition that typically leaves them
[unconstrained](https://hackage.haskell.org/package/trivial-constraint). (All of
the other category-related instances for @Circuit@ are of this form.)

For example, if we wanted to rely on smart constructors or the restrictiveness
of GADT constructors instead of including @ToBool ...@ in the @ObjectOf
definition@, we could make use of the default definition for @HasObject@ and
@ObjectOf@ given in @Cat.Sized.Semigroupoid.Free.Data@:

> class HasObject (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) where
>   type ObjectOf (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type) (n ∷ Nat) (a ∷ κ) ∷ Constraint
>   type ObjectOf φ k n a = Unconstrained4 φ k n a

Making use of this definition instead would only require

> instance HasObject φ Circuit
-}
data Circuit (φ ∷ Nat → Type → Type) (n ∷ Nat) (m ∷ Nat) (a ∷ Type) (b ∷ Type) where
  InT  ∷ (KnownNat m) ⇒ Bool -| Circuit φ 0 m |-> Bool
  InF  ∷ (KnownNat m) ⇒ Bool -| Circuit φ 0 m |-> Bool
  Not  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n n |-> Bool
  Or   ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  And  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  Nor  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  Nand ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  Xor  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool
  Iff  ∷ (KnownNat n) ⇒ Bool -| Circuit φ n 1 |-> Bool

deriving instance (Show (a -| Circuit φ n m |-> b))


class ToBool a where
  toBool ∷ a → Bool

instance ToBool Bool where
  toBool = P.id

instance ToBool (Either a b) where
  toBool (Left  _) = False
  toBool (Right _) = True

type family CircuitCarrier (φ ∷ Nat → κ → κ) (a ∷ κ) ∷ κ where
  CircuitCarrier φ (φ n a) = CircuitCarrier φ a
  CircuitCarrier φ      a  =                  a


{- | This defines the objects of the category whose arrows will be terms of the
EDSL representing Boolean functions:

> type ObjectOf φ Circuit n a = (KnownNat n, ToBool (CircuitCarrier φ a))
-}
instance HasObject φ Circuit where
  type ObjectOf φ Circuit n a = ( KnownNat n
                                , ToBool (CircuitCarrier φ a)
                                )

instance HasProxy  φ Circuit
instance HasDup    φ Circuit
instance HasSwap   φ Circuit
instance HasProj   φ Circuit
instance HasDel    φ Circuit
instance HasSelect φ Circuit


{- | The terms of our EDSL for Boolean functions will be paths in the freely
generated (/n/-ary product) Cartesian category over the 'Circuit' primitives. -}
type FreeCircuit = Cart Circuit



---------------------
-- Very basic example
---------------------

{- | A simple example term of the EDSL: ≈ "λp.λq. ¬p ∨ q".

> impliesBin = Emb Or
>            . (Emb (Not @1) *** Id)
-}
impliesBin ∷ ∀ φ. Bool -| FreeCircuit φ 2 1 |-> Bool
impliesBin =
    Emb Or
  . (   Emb (Not @1)
    *** Id
    )


{- | Elementwise 'impliesBin' of two /n/-products /p, q/ (the first and second
input /n/-product, respectively), indicating whether \( p_i \implies q_{i} \):

> impliesElem = join . zipWith impliesBin
-}
impliesElem ∷ ∀ φ n. (KnownNat n) ⇒ φ n Bool -| FreeCircuit φ 2 n |-> Bool
impliesElem = join . zipWith impliesBin


{- | Given two /n/-products ("bit vectors") /p, q/ interpretable as subsets of
some /n/-length universe, 'implies' indicates whether membership in /p/ always
entails membership in /q/:

> implies = Emb And . impliesElem
-}
implies ∷ ∀ φ n. (KnownNat n) ⇒ φ n Bool -| FreeCircuit φ 2 1 |-> Bool
implies = Emb And . impliesElem



---------------------
-- Ripple-carry adder
---------------------


{- | A 1-bit half-adder that maps a pair of bits to their sum and a carry bit:

> halfAdder2 = Emb Xor &&& Emb And

>>> eval' halfAdder $ (fromJust $ VS.fromList [True, False])
Vector [True,False]
-}
halfAdder ∷ ∀ φ. Bool -| FreeCircuit φ 2 2 |-> Bool
halfAdder =   Emb Xor
          &&& Emb And


{- | A 1-bit full adder that maps a pair of bits plus a carry bit to a sum and a
carry bit:

>                                 -- ⊕ = xor, + = or, ⋅ = and
> fullAdder = (id *** Emb Or)     -- [(a⊕b)+c, ((a⊕b)⋅c) + (a⋅b)]
>           . (halfAdder *** id)  -- [(a⊕b)+c,  (a⊕b)⋅c  ,  a⋅b ]
>           . swap 2 1            -- [ a⊕b   ,  c        ,  a⋅b ]
>           . (halfAdder *** id)  -- [ a⊕b   ,  a⋅b      ,  c   ]
>                                 -- [ a     ,  b        ,  c   ]

>>> mapM print $ table $ eval' fullAdder
([False, False, False], [False, False])
([False, False, True ], [True , False])
([False, True , False], [True , False])
([False, True , True ], [False, True ])
([True , False, False], [True , False])
([True , False, True ], [False, True ])
([True , True , False], [False, True ])
([True , True , True ], [True , True ])
-}
fullAdder ∷ ∀ φ. Bool -| FreeCircuit φ 3 2 |-> Bool
fullAdder = (id *** Emb Or)     -- [(a⊕b)+c, ((a⊕b)⋅c) + (a⋅b)]
          . (halfAdder *** id)  -- [(a⊕b)+c,  (a⊕b)⋅c  ,  a⋅b ]
          . swap 2 1            -- [ a⊕b   ,   c       ,  a⋅b ]
          . (halfAdder *** id)  -- [ a⊕b   ,   a⋅b     ,  c   ]
                                -- [ a     ,   b       ,  c   ]


{- | A ripple-carry adder for a pair of 2-bit numbers /b = b₁ b₀/, /a = a₁ a₀/
(most significant bit leftmost) where the bits have been "grouped" (zipped and
flattened) — @b₁ a₁ b₀ a₁@ — yielding a pair of sum bits and a trailing carry
bit — @s₁ s₀ co@.

>                                     -- ⊕ = xor, + = or, ⋅ = and
> rippleCarry2' = swap 1 2            -- [(b₁⊕a₁)+(b₀⋅a₀), (b₀⊕a₀)                 ,((b₁⊕a₁)⋅(b₀⋅a₀))+(b₁⋅a₁)]
>               . (fullAdder *** id)  -- [(b₁⊕a₁)+(b₀⋅a₀),((b₁⊕a₁)⋅(b₀⋅a₀))+(b₁⋅a₁),            b₀⊕a₀        ]
>               . swap 3 2            -- [ b₁            , a₁                      ,   b₀⋅a₀ ,  b₀⊕a₀        ]
>               . (id *** halfAdder)  -- [ b₁            , a₁                      ,   b₀⊕a₀ ,  b₀⋅a₀        ]
>                                     -- [ b₁            , a₁                      ,   b₀    ,     a₀        ]
-}
rippleCarry2' ∷ ∀ φ. Bool -| FreeCircuit φ 4 3 |-> Bool
rippleCarry2' = swap 1 2            -- [(b₁⊕a₁)+(b₀⋅a₀), (b₀⊕a₀)                 ,((b₁⊕a₁)⋅(b₀⋅a₀))+(b₁⋅a₁)]
              . (fullAdder *** id)  -- [(b₁⊕a₁)+(b₀⋅a₀),((b₁⊕a₁)⋅(b₀⋅a₀))+(b₁⋅a₁),            b₀⊕a₀        ]
              . swap 3 2            -- [ b₁            , a₁                      ,   b₀⋅a₀ ,  b₀⊕a₀        ]
              . (id *** halfAdder)  -- [ b₁            , a₁                      ,   b₀⊕a₀ ,  b₀⋅a₀        ]
                                    -- [ b₁            , a₁                      ,   b₀    ,     a₀        ]


{- | A ripple-carry adder for a pair of 2-bit numbers, yielding a pair of sum
bits and a trailing carry bit.

> rippleCarry2 = rippleCarry2' . join . zip

=== Examples

>>> two = numToBools @2 @Int 2
>>> two
Vector [True,False]
>>> eval' rippleCarry2 $ (fromJust $ VS.fromList [two, two])
Vector [False,False,True]

Below are tabular representations of the complete output

 - Once with the pair of 2-bit inputs on the left as @Int@s and the two output
   bits (as an @Int@) plus the carry bit.
 - Again presenting the bits as 0s and 1s but little other processing of the data.

>>> import Control.Arrow (first, (>>>))
>>> import Data.Bifunctor (bimap)
>>> import Data.Functor qualified as F
>>> intyO = boolsToNumR @3 @Int
>>> intyI = first $ bimap (boolsToNum' @Int) (boolsToNum' @Int)
>>> mapM print $ intyI <$> table2 (eval' rippleCarry2 >>> intyO)  -- This is @table2I@ henceforth
((0,0),(0,False))
((0,1),(1,False))
((0,2),(2,False))
((0,3),(3,False))
((1,0),(1,False))
((1,1),(2,False))
((1,2),(3,False))
((1,3),(0,True))
((2,0),(2,False))
((2,1),(3,False))
((2,2),(0,True))   -- 2 + 2 'overflows', and we get a carry bit, as above
((2,3),(1,True))
((3,0),(3,False))
((3,1),(0,True))
((3,2),(1,True))
((3,3),(2,True))
>>> bitsy  = F.fmap (boolToNum @Int)
>>> bitsyO = VS.toList >>> bitsy
>>> bitsyI = first $ bimap bitsy bitsy
>>> mapM print $ bitsyI <$> table2 (eval' rippleCarry2 >>> bitsyO)  -- This is @table2B@ henceforth
(([0,0],[0,0]),[0,0,0])
(([0,0],[0,1]),[0,1,0])
(([0,0],[1,0]),[1,0,0])
(([0,0],[1,1]),[1,1,0])
(([0,1],[0,0]),[0,1,0])
(([0,1],[0,1]),[1,0,0])
(([0,1],[1,0]),[1,1,0])
(([0,1],[1,1]),[0,0,1])
(([1,0],[0,0]),[1,0,0])
(([1,0],[0,1]),[1,1,0])
(([1,0],[1,0]),[0,0,1])
(([1,0],[1,1]),[0,1,1])
(([1,1],[0,0]),[1,1,0])
(([1,1],[0,1]),[0,0,1])
(([1,1],[1,0]),[0,1,1])
(([1,1],[1,1]),[1,0,1])
-}
rippleCarry2 ∷ ∀ φ. φ 2 Bool -| FreeCircuit φ 2 3 |-> Bool
rippleCarry2 = rippleCarry2'
             . join
             . zip


{- | Generalization of @rippleCarry2'@, adding a pair of 3-bit numbers, yielding
three sum bits and a trailing carry bit.

> rippleCarry3' =
>   let id1 = id @Type @φ @FreeCircuit @1
>   in  swap 2 3
>    .  swap 1 2
>    .  (fullAdder *** id)
>    .  swap 3 2
>    .  (id *** fullAdder *** id1)
>    .  swap 5 4
>    .  (id *** halfAdder)
-}
rippleCarry3' ∷ ∀ (φ ∷ Nat → Type → Type). Bool -| FreeCircuit φ 6 4 |-> Bool
rippleCarry3' = let id1 = id @Type @φ @FreeCircuit @1
              in swap 2 3                   -- ...all the way.
               . swap 1 2                   -- Propagate the last carry rightward...
               . (fullAdder *** id)         -- [ sum b2 a2, carry b2 a2 c_         , (b₁⊕a₁)+(b₀⋅a₀)         ,  b₀⊕a₀          ]
               . swap 3 2                   -- [ b2 , a2 ,((b₁⊕a₁)⋅(b₀⋅a₀))+(b₁⋅a₁), (b₁⊕a₁)+(b₀⋅a₀)         ,  b₀⊕a₀          ]
               . (id *** fullAdder *** id1) -- [ b2 , a2 , (b₁⊕a₁)+(b₀⋅a₀)         , (b₁⊕a₁)⋅(b₀⋅a₀)+(b₁⋅a₁) , (b₀⊕a₀)         ]
               . swap 5 4                   -- [ b2 , a2 , b₁                      , a₁                     ,  b₀⋅a₀ ,  b₀⊕a₀  ]
               . (id *** halfAdder)         -- [ b2 , a2 , b₁                      , a₁                     ,  b₀⊕a₀ ,  b₀⋅a₀  ]
                                            -- [ b2 , a2 , b₁                      , a₁                     , b₀     , a₀      ]

{- | A ripple-carry adder for a pair of 3-bit numbers, yielding three sum
bits and a trailing carry bit.

> rippleCarry3 = rippleCarry3' . join . zip

>>> mapM print $ table2IR rippleCarry3
((0,0),(0,False))
((0,1),(1,False))
((0,2),(2,False))
((0,3),(3,False))
((0,4),(4,False))
((0,5),(5,False))
((0,6),(6,False))
((0,7),(7,False))
((1,0),(1,False))
((1,1),(2,False))
((1,2),(3,False))
((1,3),(4,False))
((1,4),(5,False))
((1,5),(6,False))
((1,6),(7,False))
((1,7),(0,True))
((2,0),(2,False))
((2,1),(3,False))
((2,2),(4,False))
((2,3),(5,False))
((2,4),(6,False))
((2,5),(7,False))
((2,6),(0,True))
((2,7),(1,True))
((3,0),(3,False))
((3,1),(4,False))
((3,2),(5,False))
((3,3),(6,False))
((3,4),(7,False))
((3,5),(0,True))
((3,6),(1,True))
((3,7),(2,True))
((4,0),(4,False))
((4,1),(5,False))
((4,2),(6,False))
((4,3),(7,False))
((4,4),(0,True))
((4,5),(1,True))
((4,6),(2,True))
((4,7),(3,True))
((5,0),(5,False))
((5,1),(6,False))
((5,2),(7,False))
((5,3),(0,True))
((5,4),(1,True))
((5,5),(2,True))
((5,6),(3,True))
((5,7),(4,True))
((6,0),(6,False))
((6,1),(7,False))
((6,2),(0,True))
((6,3),(1,True))
((6,4),(2,True))
((6,5),(3,True))
((6,6),(4,True))
((6,7),(5,True))
((7,0),(7,False))
((7,1),(0,True))
((7,2),(1,True))
((7,3),(2,True))
((7,4),(3,True))
((7,5),(4,True))
((7,6),(5,True))
((7,7),(6,True))
-}
rippleCarry3 ∷ ∀ φ. φ 3 Bool -| FreeCircuit φ 2 4 |-> Bool
rippleCarry3 = rippleCarry3'
             . join
             . zip


{- | Generalization of @rippleCarry3'@, adding a pair of 4-bit numbers, yielding
four sum bits and a trailing carry bit. The definition has been adapted to more
clearly suggest a general pattern and to highlight what "rippling" looks like.

> rippleCarry4' = let id1 = id @Type @φ @FreeCircuit @1
>                     id2 = id @Type @φ @FreeCircuit @2
>                     id3 = id @Type @φ @FreeCircuit @3
>                     id0 = id @Type @φ @FreeCircuit @0
>               in swap 3 4
>                . swap 2 3
>                . swap 1 2
>                . (id0 *** fullAdder *** id3)
>                . swap 3 2
>                . (id  *** fullAdder *** id2)
>                . swap 5 4
>                . (id  *** fullAdder *** id1)
>                . swap 7 6
>                . (id  *** halfAdder *** id0)
-}
rippleCarry4' ∷ ∀ (φ ∷ Nat → Type → Type). Bool -| FreeCircuit φ 8 5 |-> Bool
rippleCarry4' = let id1 = id @Type @φ @FreeCircuit @1
                    id2 = id @Type @φ @FreeCircuit @2
                    id3 = id @Type @φ @FreeCircuit @3
                    id0 = id @Type @φ @FreeCircuit @0
              in swap 3 4
               . swap 2 3
               . swap 1 2
               . (id0 *** fullAdder *** id3)
               . swap 3 2
               . (id  *** fullAdder *** id2)
               . swap 5 4
               . (id  *** fullAdder *** id1)
               . swap 7 6
               . (id  *** halfAdder *** id0)


{- | A ripple-carry adder for a pair of 4-bit numbers, yielding four sum
bits and a trailing carry bit.

> rippleCarry4 = rippleCarry4' . join . zip
-}
rippleCarry4 ∷ ∀ φ. φ 4 Bool -| FreeCircuit φ 2 5 |-> Bool
rippleCarry4 = rippleCarry4'
             . join
             . zip


------------------------
-- Carry-lookahead adder
------------------------

{- | Map a pair of bits to their carry-generate and carry-propagate bits for
a carry-lookahead adder.

> fullAdderGP = Emb And &&& Emb Xor
-}
fullAdderGP ∷ ∀ φ. Bool -| FreeCircuit φ 2 2 |-> Bool
fullAdderGP =   Emb And
            &&& Emb Xor


{- | Map a /(generate, propagate, carry-in)/ triple to a /(carry-out, sum)/ pair
for a carry-lookahead adder, where, if ⊕ = @xor@, + = @||@, ⋅ = @&&@, then

 - /carry-out = generate + (propagate ⋅ carry-in)/
 - /sum = propagate ⊕ carry-in/

> lookahead = ( Emb Or
>             . (id *** (Emb $ And @2))
>             )
>         &&& (del 1 *** Emb Xor)
-}
lookahead ∷ ∀ φ. Bool -| FreeCircuit φ 3 2 |-> Bool
lookahead = ( Emb Or
            . (id *** Emb (And @2))
            )
        &&& (del 1 *** Emb Xor)


{- | Map a pair of /n/-bit (unsigned) numbers to /n/ pairs of
/(generate, propagate)/ bits for a carry-lookahead adder.

> lookaheadCarryGPs = zipWith fullAdderGP

>>> one2 = numToBools @2 @Int 1
>>> two2 = numToBools @2 @Int 2
>>> mapM print [one2, two2]
Vector [False,True]
Vector [True,False]
>>> twoTwo2 = fromJust $ VS.fromList @2 [two2, two2]
twoTwo2 :: VS.Vector 2 (VS.Vector 2 Bool)
>>> twoOne2 = fromJust $ VS.fromList @2 [two2, one2]
twoOne2 :: VS.Vector 2 (VS.Vector 2 Bool)
>>> eval' lookaheadCarryGPs $ twoTwo2
Vector [Vector [True,False],Vector [False,False]]  -- generate+propagate for the left and right bits, respectively
>>> eval' lookaheadCarryGPs $ twoOne2
Vector [Vector [False,True],Vector [False,True]]  -- generate+propagate for the left and right bits, respectively
-}
lookaheadCarryGPs ∷ ∀ φ n. KnownNat n ⇒ φ n Bool -| FreeCircuit φ 2 n |-> φ 2 Bool
lookaheadCarryGPs = zipWith fullAdderGP


{- | Map /4/ pairs of /(generate, propagate)/ bits from a pair of /4/-bit numbers
to a pair of /(group generate, group propagate)/ bits for a carry-lookahead
unit.

That is, given

> [[g₃ p₃], [g₂ p₂], [g₁ p₁], [g₀ p₀]]

the group generate and group propagate are defined as:

> gg ≝ g₃ + g₂⋅p₃ + g₁⋅p₂⋅p₃ + g₀⋅p₁⋅p₂⋅p₃

> gp ≝ p₃⋅p₂⋅p₁⋅p₀

where '+' is '||' and '⋅' is '&&', as elsewhere in this module.

=== Definition

> lookaheadCarryGGP4 =
>    (   gg
>    &&& gp
>    )
>    . zip  -- Rezip the (g,p) pairs into all of the generate bits and all the propagate bits.

where

> -- | Given carry-generates and carry-propagates
> --
> -- > [[g₃, g₂, g₁, g₀], [p₃, p₂, p₁, p₀]]
> --
> -- this returns the group-propagate @gp@
> --
> -- > gp ≝ p₃⋅p₂⋅p₁⋅p₀
> gp ∷ φ 4 Bool -| Cart Circuit φ 2 1 |-> Bool
> gp = Emb And  -- Take the && of all the propagates to get the group-propagate bit
>    . join     -- Remove nesting on the propagates
>    . last     -- Ignore the generate bits ≡ project the pair of 4-products to just the second 4-product

(See also 'join', 'last'.)

> -- | Given carry-generates and carry-propagates
> --
> -- > [[g₃, g₂, g₁, g₀], [p₃, p₂, p₁, p₀]]
> --
> -- gg returns the group-generate @gg@
> --
> -- > gg ≝ g₃ + g₂⋅p₃ + g₁⋅p₂⋅p₃ + g₀⋅p₁⋅p₂⋅p₃
> gg ∷ φ 4 Bool -| FreeCircuit φ 2 1 |-> Bool
> gg = (Emb $ Or @4)           -- The first three lines are essentially a dot-product (≡ special case of a fold ≡ jam)
>    . join
>    . zipWith (Emb $ And @2)
>    . (id *** (sing . psufs . rev4 . unsing))  -- ...and 'psufs' is essentially a scan

(See also 'zipWith', 'sing', and 'unsing'.)

The helpers @rev4@ and @psufs@ are defined as:

> -- | Reverse a 4-product.
> rev4 ∷ Bool -| FreeCircuit φ 4 4 |-> Bool
> rev4 = swap 1 2 . swap 0 3
>
> -- | Given 4 propagate bits
> --
> --   > [p₀, p₁, p₂, p₃]
> --
> -- psufs returns
> --
> --   > [True, p₃, (p₂ ⋅ p₃), (p₁ ⋅ p₂ ⋅ p₃)]
> psufs ∷ Bool -| FreeCircuit φ 4 4 |-> Bool
> psufs = (Emb $ InT @1)
>     *** ((    ((    suffix @Type @φ @FreeCircuit @1 @2
>                 &&& (Emb $ And @2)
>               )
>               . suffix @Type @φ @FreeCircuit @2 @3
>               )
>           &&& (Emb $ And @3)
>         )
>         . suffix @Type @φ @FreeCircuit @3 @4)

(See also 'swap' and 'suffix'.)

-}
lookaheadCarryGGP4 ∷ ∀ φ. φ 2 Bool -| FreeCircuit φ 4 2 |-> Bool
lookaheadCarryGGP4 =
  let

    -- | Reverse a 4-product.
    rev4 ∷ Bool -| FreeCircuit φ 4 4 |-> Bool
    rev4 = swap 1 2 . swap 0 3

    -- | Given 4 propagates
    --
    --   > [p₀, p₁, p₂, p₃]
    --
    -- psufs returns
    --
    --   > [True, p₃, (p₂ ⋅ p₃), (p₁ ⋅ p₂ ⋅ p₃)]
    psufs ∷ Bool -| FreeCircuit φ 4 4 |-> Bool
    psufs = (Emb $ InT @1)
        *** ((    ((    suffix @Type @φ @FreeCircuit @1 @2
                    &&& (Emb $ And @2)
                  )
                  . suffix @Type @φ @FreeCircuit @2 @3
                  )
              &&& (Emb $ And @3)
            )
            . suffix @Type @φ @FreeCircuit @3 @4)

    -- | Given carry-generates and carry-propagates
    --
    -- > [[g₃, g₂, g₁, g₀], [p₃, p₂, p₁, p₀]]
    --
    -- this returns the group-generate @gg@
    --
    -- > gg ≝ g₃ + g₂⋅p₃ + g₁⋅p₂⋅p₃ + g₀⋅p₁⋅p₂⋅p₃
    gg ∷ φ 4 Bool -| FreeCircuit φ 2 1 |-> Bool
    gg = (Emb $ Or @4)
       . join
       . zipWith (Emb $ And @2)
       . (id *** (sing . psufs . rev4 . unsing))

    -- | Given carry-generates and carry-propagates
    --
    -- > [[g₃, g₂, g₁, g₀], [p₃, p₂, p₁, p₀]]
    --
    -- this returns the group-propagate @gp@
    --
    -- > gp ≝ p₃⋅p₂⋅p₁⋅p₀
    gp ∷ φ 4 Bool -| Cart Circuit φ 2 1 |-> Bool
    gp = Emb And  -- Take the && of all the propagates to get the group-propagate bit.
       . join     -- Remove nesting on the propagates
       . last     -- Ignore the generate bits

  in (   gg
     &&& gp
     )
   . zip  -- Rezip the (g,p) pairs into all of the generate bits and all the propagate bits.


{- | Map a pair of bits to their /(carry-out, sum)/ pair.

> lookaheadCarry1 = lookahead
>                 . (fullAdderGP *** Emb InF)

>>> mapM print $ table (eval' lookaheadCarry1)
([False,False],[False,False])
([False,True],[False,True])
([True,False],[False,True])
([True,True],[True,False])
-}
lookaheadCarry1 ∷ ∀ φ. Bool -| FreeCircuit φ 2 2 |-> Bool
lookaheadCarry1 = lookahead
                . (fullAdderGP *** Emb InF)


{- | Map a pair of 2-bit numbers to their /(carry-out, sum, sum)/ triple.

> lookaheadCarry2 = (lookahead *** id)
>                 . (id *** lookahead)
>                 . (id *** Emb InF)
>                 . join . lookaheadCarryGPs


>>> mapM print $ table2IL lookaheadCarry2
((0,0),(False,0))
((0,1),(False,1))
((0,2),(False,2))
((0,3),(False,3))
((1,0),(False,1))
((1,1),(False,2))
((1,2),(False,3))
((1,3),(True,0))
((2,0),(False,2))
((2,1),(False,3))
((2,2),(True,0))
((2,3),(True,1))
((3,0),(False,3))
((3,1),(True,0))
((3,2),(True,1))
((3,3),(True,2))
>>> mapM print $ table2B lookaheadCarry2
(([0,0],[0,0]),[0,0,0])
(([0,0],[0,1]),[0,0,1])
(([0,0],[1,0]),[0,1,0])
(([0,0],[1,1]),[0,1,1])
(([0,1],[0,0]),[0,0,1])
(([0,1],[0,1]),[0,1,0])
(([0,1],[1,0]),[0,1,1])
(([0,1],[1,1]),[1,0,0])
(([1,0],[0,0]),[0,1,0])
(([1,0],[0,1]),[0,1,1])
(([1,0],[1,0]),[1,0,0])
(([1,0],[1,1]),[1,0,1])
(([1,1],[0,0]),[0,1,1])
(([1,1],[0,1]),[1,0,0])
(([1,1],[1,0]),[1,0,1])
(([1,1],[1,1]),[1,1,0])
-}
lookaheadCarry2 ∷ ∀ φ. φ 2 Bool -| FreeCircuit φ 2 3 |-> Bool
lookaheadCarry2 = (lookahead *** id)
                . (id *** lookahead)
                . (id *** Emb InF)
                . join . lookaheadCarryGPs


{- | Map a pair of 3-bit numbers to their /(carry-out, sum, sum, sum)/ triple.

> lookaheadCarry3 = let id1 = id @Type @φ @FreeCircuit @1
>                       id2 = id @Type @φ @FreeCircuit @2
>                   in  (       lookahead *** id2)
>                    .  (id *** lookahead *** id1)
>                    .  (id *** lookahead)
>                    .  (id *** Emb InF)
>                    .  join . lookaheadCarryGPs


>>> mapM print $ table2IL lookaheadCarry3
((0,0),(False,0))
((0,1),(False,1))
((0,2),(False,2))
((0,3),(False,3))
((0,4),(False,4))
((0,5),(False,5))
((0,6),(False,6))
((0,7),(False,7))
((1,0),(False,1))
((1,1),(False,2))
((1,2),(False,3))
((1,3),(False,4))
((1,4),(False,5))
((1,5),(False,6))
((1,6),(False,7))
((1,7),(True,0))
((2,0),(False,2))
((2,1),(False,3))
((2,2),(False,4))
((2,3),(False,5))
((2,4),(False,6))
((2,5),(False,7))
((2,6),(True,0))
((2,7),(True,1))
((3,0),(False,3))
((3,1),(False,4))
((3,2),(False,5))
((3,3),(False,6))
((3,4),(False,7))
((3,5),(True,0))
((3,6),(True,1))
((3,7),(True,2))
((4,0),(False,4))
((4,1),(False,5))
((4,2),(False,6))
((4,3),(False,7))
((4,4),(True,0))
((4,5),(True,1))
((4,6),(True,2))
((4,7),(True,3))
((5,0),(False,5))
((5,1),(False,6))
((5,2),(False,7))
((5,3),(True,0))
((5,4),(True,1))
((5,5),(True,2))
((5,6),(True,3))
((5,7),(True,4))
((6,0),(False,6))
((6,1),(False,7))
((6,2),(True,0))
((6,3),(True,1))
((6,4),(True,2))
((6,5),(True,3))
((6,6),(True,4))
((6,7),(True,5))
((7,0),(False,7))
((7,1),(True,0))
((7,2),(True,1))
((7,3),(True,2))
((7,4),(True,3))
((7,5),(True,4))
((7,6),(True,5))
((7,7),(True,6))-}
lookaheadCarry3 ∷ ∀ φ. φ 3 Bool -| FreeCircuit φ 2 4 |-> Bool
lookaheadCarry3 = let id1 = id @Type @φ @FreeCircuit @1
                      id2 = id @Type @φ @FreeCircuit @2
                  in  (       lookahead *** id2)
                   .  (id *** lookahead *** id1)
                   .  (id *** lookahead)
                   .  (id *** Emb InF)
                   .  join . lookaheadCarryGPs


{- | Where 'lookaheadCarry3' and 'lookaheadCarry2' are clear extensions of
'lookahead' and 'lookaheadCarryGPs', this is a stepping stone to the form used
in this module to represent a 4-bit lookahead carry adder unit that can be
composed to add larger fixed-width numbers. Like the previous two functions,
this does not make use of the generate-propagate pairs to compute or make use
of a group-level generate-propagate pair.

'lookaheadCarry4Flat' is a composable 4-bit carry-lookahead adder that maps

 - A pair of grouped ("zipped and flattened") 4-bit numbers and a trailing
   carry-in bit: @b₃ a₃ b₂ a₂ b₁ a₁ ci@.

to

 - A leading carry-out bit and the 4-bit sum (most significant bit leftmost):
   @co s₃ s₂ s₁ s₀@.


> lookaheadCarry4Flat = let id1 = id @Type @φ @FreeCircuit @1
>                           id2 = id @Type @φ @FreeCircuit @2
>                           id3 = id @Type @φ @FreeCircuit @3
>                           id0 = id @Type @φ @FreeCircuit @0
>                       in  (       lookahead *** id3)
>                        .  (id *** lookahead *** id2)
>                        .  (id *** lookahead *** id1)
>                        .  (id *** lookahead *** id0)
>                        .  ((join . lookaheadCarryGPs . split) *** id1)
-}
lookaheadCarry4Flat ∷ ∀ φ. Bool -| FreeCircuit φ 9 5 |-> Bool
lookaheadCarry4Flat = let id1 = id @Type @φ @FreeCircuit @1
                          id2 = id @Type @φ @FreeCircuit @2
                          id3 = id @Type @φ @FreeCircuit @3
                          id0 = id @Type @φ @FreeCircuit @0
                      in  (       lookahead *** id3)
                       .  (id *** lookahead *** id2)
                       .  (id *** lookahead *** id1)
                       .  (id *** lookahead *** id0)
                       .  ((join . lookaheadCarryGPs . split) *** id1)


{- | A composable 4-bit carry-lookahead adder unit that maps

 - A pair of ungrouped (concatenated) 4-bit numbers (most significant bit
   leftmost) plus a trailing carry-in bit: @b₃ b₂ b₁ b₀ a₃ a₂ a₁ a₀ ci@.

to

 - A leading carry-out bit followed by the 4-bit sum (most significant bit
   leftmost): @co s₃ s₂ s₁ s₀@.

Unlike 'lookaheadCarry4Flat', this does make use of group-level
generate-propagate pairs.

=== Definition

> lookaheadCarry4Unit =
>     (      co
>        &&& sums
>     )
>     . gps

where

> -- | Regroup the 8 input bits to 2 blocks of 4, zip them together,
> -- compute 4 generate-propagate pairs, and flatten the result.
> gps ∷ Bool -| FreeCircuit φ 9 9 |-> Bool
> gps = ( join
>       . lookaheadCarryGPs
>       . split
>       )
>   *** id1  -- Leave the carry-in bit alone

(See 'join', 'split'.)

> -- | Compute 4 sum bits from generate-propagate pairs and the carry-in bit.
> sums ∷ Bool -| FreeCircuit φ 9 4 |-> Bool
> sums = del 0                       -- Throw-away the carry-out bit;
>      . (       lookahead *** id3)  -- a carry-lookahead adder offers a faster
>      . (id *** lookahead *** id2)  -- way of computing this.
>      . (id *** lookahead *** id1)
>      . (id *** lookahead *** id0)

> -- | Compute the carry-out from 4 generate-propagate bits and the carry-in.
> co ∷ Bool -| FreeCircuit φ 9 1 |-> Bool
> co = co'
>    . (  (lookaheadCarryGGP4 . split)
>      *** id1)

> -- | Map the group-generate, group-propagate, and carry-in to the carry-out.
> co' ∷ Bool -| FreeCircuit φ 3 1 |-> Bool
> co' = (Emb $ Or @2)
>     . (id1 *** (Emb $ And @2))

> id1 = id @Type @φ @FreeCircuit @1
> id2 = id @Type @φ @FreeCircuit @2
> id3 = id @Type @φ @FreeCircuit @3
> id0 = id @Type @φ @FreeCircuit @0

-}
lookaheadCarry4Unit ∷ ∀ φ. Bool -| FreeCircuit φ 9 5 |-> Bool
lookaheadCarry4Unit =
  let id1 = id @Type @φ @FreeCircuit @1
      id2 = id @Type @φ @FreeCircuit @2
      id3 = id @Type @φ @FreeCircuit @3
      id0 = id @Type @φ @FreeCircuit @0

      -- | Regroup the 8 input bits to 2 blocks of 4, zip them together,
      -- compute 4 generate-propagate pairs, and flatten the result.
      gps ∷ Bool -| FreeCircuit φ 9 9 |-> Bool
      gps = ( join
            . lookaheadCarryGPs
            . split
            )
        *** id1

      -- | Map the group-generate, group-propagate, and carry-in bit to a
      -- carry-out bit.
      co' ∷ Bool -| FreeCircuit φ 3 1 |-> Bool
      co' = (Emb $ Or @2)
          . (id1 *** (Emb $ And @2))

      co  ∷ Bool -| FreeCircuit φ 9 1 |-> Bool
      co  = co'
          . (  (lookaheadCarryGGP4 . split) -- Generate group-generate+propagate bits from 4 generate-propagate pairs
            *** id1
            )

      sums ∷ Bool -| FreeCircuit φ 9 4 |-> Bool
      sums = del 0
           . (       lookahead *** id3)
           . (id *** lookahead *** id2)
           . (id *** lookahead *** id1)
           . (id *** lookahead *** id0)

  in
    (      co
       &&& sums
    )
    . gps

{- | 8-bit adder composed of 'lookaheadCarry4Unit's.

Maps

 - two 8-bit numbers grouped into alternating pairs of 4-bit blocks (most
   significant-bit leftmost) followed by a trailing carry-in bit:
   @b₁₅ b₁₄ b₁₃ b₁₂ a₁₅ a₁₄ a₁₃ a₁₂ b₁₁ b₁₀ b₉ b₈ a₁₁ ... a₀ ci@

to

 - a leading carry-out bit and their 8-bit sum: @co s₇ s₆ ...s₀@.

> lookaheadCarry8Unit = let id4  = id @Type @φ @FreeCircuit @4
>                       in  (       lookaheadCarry4Unit *** id4 )
>                        .  (id *** lookaheadCarry4Unit         )
-}
lookaheadCarry8Unit ∷ ∀ φ. Bool -| FreeCircuit φ 17 9 |-> Bool
lookaheadCarry8Unit = let id4  = id @Type @φ @FreeCircuit @4
                      in  (       lookaheadCarry4Unit *** id4 )
                       .  (id *** lookaheadCarry4Unit         )


{- | 16-bit adder composed of 'lookaheadCarry4Unit's.

Maps

 - two 16-bit numbers grouped into alternating pairs of 4-bit blocks (most
   significant-bit leftmost) followed by a trailing carry-in bit:
   @b₃₁ b₃₀ b₂₉ b₂₈ a₃₁ a₃₀ a₂₉ a₂₈ b₂₇ b₂₆ b₂₅ b₂₄ a₂₇ ... a₀ ci@

to

 - a leading carry-out bit and their 16-bit sum: @co s₁₅ s₁₄ ...s₀@.

> lookaheadCarry16Unit = let id4  = id @Type @φ @FreeCircuit @4
>                            id8  = id @Type @φ @FreeCircuit @8
>                            id12 = id @Type @φ @FreeCircuit @12
>                     in (       lookaheadCarry4Unit *** id12)
>                      . (id *** lookaheadCarry4Unit *** id8 )
>                      . (id *** lookaheadCarry4Unit *** id4 )
>                      . (id *** lookaheadCarry4Unit         )
-}
lookaheadCarry16Unit ∷ ∀ φ. Bool -| FreeCircuit φ 33 17 |-> Bool
lookaheadCarry16Unit = let id4  = id @Type @φ @FreeCircuit @4
                           id8  = id @Type @φ @FreeCircuit @8
                           id12 = id @Type @φ @FreeCircuit @12
                    in (       lookaheadCarry4Unit *** id12)
                     . (id *** lookaheadCarry4Unit *** id8 )
                     . (id *** lookaheadCarry4Unit *** id4 )
                     . (id *** lookaheadCarry4Unit         )


{- | Carry-lookahead adder for a pair of 4-bit numbers with overflow (no carry-out
bit).

> lookaheadCarry4O = tail
>                  . lookaheadCarry4Flat
>                  . (id *** Emb InF)
>                  . join

>>> tableLc4O = table2I lookaheadCarry4O
tableLc4O :: [((Int, Int), Int)]
>>> testLc4 ((x,y),xy) = ((x + y) `mod` (2 ^ 4)) == xy
testLc4 :: (Eq a, Num a) => ((a, a), a) -> Bool
>>> all testLc4 tableLc4O
True
>>> mapM print $ L.take 20 $ tableLc4O
((0,0),0)
((0,1),1)
((0,2),2)
((0,3),3)
((0,4),4)
((0,5),5)
((0,6),6)
((0,7),7)
((0,8),8)
((0,9),9)
((0,10),10)
((0,11),11)
((0,12),12)
((0,13),13)
((0,14),14)
((0,15),15)
((1,0),1)
((1,1),2)
((1,2),3)
((1,3),4)
>>> mapM print $ L.take 20 $ reverse $ tableLc4O
((15,15),14)
((15,14),13)
((15,13),12)
((15,12),11)
((15,11),10)
((15,10),9)
((15,9),8)
((15,8),7)
((15,7),6)
((15,6),5)
((15,5),4)
((15,4),3)
((15,3),2)
((15,2),1)
((15,1),0)
((15,0),15)
((14,15),13)
((14,14),12)
((14,13),11)
((14,12),10)
-}
lookaheadCarry4O ∷ ∀ φ. φ 4 Bool -| FreeCircuit φ 2 4 |-> Bool
lookaheadCarry4O = tail
                 . lookaheadCarry4Flat
                 . (id *** Emb InF)
                 . join


{- | Carry-lookahead adder for a pair of 4-bit numbers with overflow (no carry-out
bit).

> lookaheadCarry4UnitO = tail
>                      . lookaheadCarry4Unit
>                      . (id *** Emb InF)
>                      . join

>>> tableLc4O = table2I lookaheadCarry4UnitO
tableLc4O :: [((Int, Int), Int)]
>>> testLc4 ((x,y),xy) = ((x + y) `mod` (2 ^ 4)) == xy
testLc4 :: (Eq a, Num a) => ((a, a), a) -> Bool
>>> all testLc4 tableLc4O
True
>>> mapM print $ L.take 20 $ tableLc4O
((0,0),0)
((0,1),1)
((0,2),2)
((0,3),3)
((0,4),4)
((0,5),5)
((0,6),6)
((0,7),7)
((0,8),8)
((0,9),9)
((0,10),10)
((0,11),11)
((0,12),12)
((0,13),13)
((0,14),14)
((0,15),15)
((1,0),1)
((1,1),2)
((1,2),3)
((1,3),4)
-}
lookaheadCarry4UnitO ∷ ∀ φ. φ 4 Bool -| FreeCircuit φ 2 4 |-> Bool
lookaheadCarry4UnitO = tail
                     . lookaheadCarry4Unit
                     . (id *** Emb InF)
                     . join


{- | Sum a pair of 8-bit numbers (most significant bit leftmost) with wraparound
(overflow) using 'lookaheadCarry4Unit' as the building block.

>>> tableLc8O = table2I lookaheadCarry8UnitO
>>> testLc8 ((x,y),xy) = ((x + y) `mod` (2 ^ 8)) == xy
testLc8 :: Integral a => ((a, a), a) -> Bool
>>> L.all testLc8 tableLc8O
True

=== Definition

> lookaheadCarry8UnitO = tail
>                      . lookaheadCarry8Unit
>                      . (id *** Emb InF)
>                      . blockify

where

> -- | Each 4-bit carrylookahead adder unit expects 4 bits from one number, 4
> -- bits from the next, and a trailing carry-in bit.
> --
> -- This re-groups the bits of the two incoming 8-bit numbers into adjacent
> -- pairs of 4-bit blocks where the first 4 bit block in each pair comes from
> -- the first 8-bit number, and the second block comes from the other.
> blockify ∷ φ 8 Bool -| FreeCircuit φ 2 16 |-> Bool
> blockify = join                                 -- Flatten the pair of 8 bit blocks
>          . map2 (join . zip)                    -- Zip each group of 4 pairs of bits into a pair of 4 bit blocks from the same number, then flatten each group of pairs of 4 bit blocks into an 8 bit block
>          . split @Type @φ @FreeCircuit @2       -- Group the 8 pairs of bits into 2 groups of 4 pairs of bits
>          . zip                                  -- Group the ith bit of the first number with that of the second
>
> map2 f = (bising f *** bising f) :: φ n a -| FreeCircuit φ 2 2 |-> φ m b

(See also 'tail', 'join', 'split', 'zip', 'bising'.)
-}
lookaheadCarry8UnitO ∷ ∀ φ. φ 8 Bool -| FreeCircuit φ 2 8 |-> Bool
lookaheadCarry8UnitO =
  let
      map2 ∷ ∀ n m a b.
           ( KnownNat n, KnownNat m
           , ToBool (CircuitCarrier φ a)
           , ToBool (CircuitCarrier φ b)
           )
           ⇒     a -| FreeCircuit φ n m |->     b
           → φ n a -| FreeCircuit φ 2 2 |-> φ m b
      map2 f = let f' = bising f
               in  f' *** f'

      -- | Each 4-bit carrylookahead adder unit expects 4 bits from one number, 4
      -- bits from the next, and a trailing carry-in bit.
      --
      -- This re-groups the bits of the two incoming 8-bit numbers into adjacent
      -- pairs of 4-bit blocks where the first 4 bit block in each pair comes from
      -- the first 8-bit number, and the second block comes from the other.
      blockify ∷ φ 8 Bool -| FreeCircuit φ 2 16 |-> Bool
      blockify = join                                 -- Flatten the pair of 8 bit blocks
               . map2 (join . zip)                    -- Zip each group of 4 pairs of bits into a pair of 4 bit blocks from the same number, then flatten each group of pairs of 4 bit blocks into an 8 bit block
               . split @Type @φ @FreeCircuit @2       -- Group the 8 pairs of bits into 2 groups of 4 pairs of bits
               . zip                                  -- Group the ith bit of the first number with that of the second
  in tail
   . lookaheadCarry8Unit
   . (id *** Emb InF)
   . blockify


{- | Sum a pair of 16-bit numbers (most significant bit leftmost) with wraparound
(overflow) using 'lookaheadCarry4Unit' as the building block.

=== Definition

> lookaheadCarry16UnitO = tail
>                       . lookaheadCarry16Unit
>                       . (id *** Emb InF)
>                       . blockify

where

> map4 ∷ ∀ n m a b.
>      ( KnownNat n, KnownNat m
>      , ToBool (CircuitCarrier φ a)
>      , ToBool (CircuitCarrier φ b)
>      )
>      ⇒     a -| FreeCircuit φ n m |->     b
>      → φ n a -| FreeCircuit φ 4 4 |-> φ m b
> map4 f = let f' = bising f
>          in  f' *** f' *** f' *** f'

> -- | Each 4-bit carrylookahead adder unit expects 4 bits from one number, 4
> -- bits from the next, and a trailing carry-in bit.
> --
> -- This re-groups the bits of the two incoming 16-bit numbers into adjacent
> -- pairs of 4-bit blocks where the first 4 bit block in each pair comes from
> -- the first 16-bit number, and the second block comes from the other.
> blockify ∷ φ 16 Bool -| FreeCircuit φ 2 32 |-> Bool
> blockify = join                                 -- Flatten the pair of 8 bit blocks
>          . map4 (join . zip)                    -- Zip each group of 4 pairs of bits into a pair of 4 bit blocks from the same number, then flatten each group of pairs of 4 bit blocks into an 8 bit block
>          . split @Type @φ @FreeCircuit @4       -- Group the 16 pairs of bits into 4 groups of 4 pairs of bits
>          . zip                                  -- Group the ith bit of the first number with that of the second

(See also 'tail', 'join', 'split', 'zip', 'bising'.)
-}
lookaheadCarry16UnitO ∷ ∀ φ. φ 16 Bool -| FreeCircuit φ 2 16 |-> Bool
lookaheadCarry16UnitO = let

  map4 ∷ ∀ n m a b.
       ( KnownNat n, KnownNat m
       , ToBool (CircuitCarrier φ a)
       , ToBool (CircuitCarrier φ b)
       -- , S.Functor (φ 4) φ φ FreeCircuit FreeCircuit
       )
       ⇒     a -| FreeCircuit φ n m |->     b
       → φ n a -| FreeCircuit φ 4 4 |-> φ m b
  map4 f = let f' = bising f
           in  f' *** f' *** f' *** f'
  -- map4 = omap @4 @φ @FreeCircuit @FreeCircuit

  -- | Each 4-bit carrylookahead adder unit expects 4 bits from one number, 4
  -- bits from the next, and a trailing carry-in bit.
  --
  -- This re-groups the bits of the two incoming 16-bit numbers into adjacent
  -- pairs of 4-bit blocks where the first 4 bit block in each pair comes from
  -- the first 16-bit number, and the second block comes from the other.
  blockify ∷ φ 16 Bool -| FreeCircuit φ 2 32 |-> Bool
  blockify = join                                 -- Flatten the pair of 8 bit blocks
           -- . omap @4 @φ @FreeCircuit (join . zip) -- Zip each group of 4 pairs of bits into a pair of 4 bit blocks from the same number, then flatten each group of pairs of 4 bit blocks into an 8 bit block
           . map4 (join . zip)                    -- Zip each group of 4 pairs of bits into a pair of 4 bit blocks from the same number, then flatten each group of pairs of 4 bit blocks into an 8 bit block
           . split @Type @φ @FreeCircuit @4       -- Group the 16 pairs of bits into 4 groups of 4 pairs of bits
           . zip                                  -- Group the ith bit of the first number with that of the second
  in  tail
    . lookaheadCarry16Unit
    . (id *** Emb InF)
    . blockify




---------------------
-- Bit/int conversion
---------------------


boolToNum ∷ ∀ a. (Num a) ⇒ Bool → a
boolToNum False = 0
boolToNum True  = 1

{- | Most significant bits are leftmost:

>>> boolsToNum' [False, False, True]
1
>>> boolsToNum' [True, False, True]
5
-}
boolsToNum' ∷ ∀ a. (Num a, B.Bits a) ⇒ [Bool] → a
boolsToNum' = FO.foldl' (\n a -> (n `B.shiftL` 1) .|. boolToNum a) 0

boolsToNumR' ∷ ∀ a. (Num a, B.Bits a)
             ⇒ [Bool] → (a, Bool)
boolsToNumR' b@[] = (boolsToNum' b, False)
boolsToNumR' bs   = (boolsToNum' <<< P.init $ bs, P.last bs)

boolsToNumL' ∷ ∀ a. (Num a, B.Bits a)
             ⇒ [Bool] → (Bool, a)
boolsToNumL' b@[] = (False  , boolsToNum' b)
boolsToNumL' bs   = (P.head bs, boolsToNum' <<< P.tail $ bs)


numToBool ∷ ∀ a. (Eq a, Num a) ⇒ a → Bool
numToBool 0 = False
numToBool _ = True


{- | @numToBools' b n@ maps @n@ to its representation as an unsigned integer
with @b@ bits of precision and most significant bits leftmost.

>>> numToBools' 3 5
[True,False,True]
>>> numToBools' 3 8      -- Note overflow
[False, False, False]
-}
numToBools' ∷ ∀ a. (Num a, B.Bits a) ⇒ Int → a → [Bool]
numToBools' b n =
  let f m = numToBool (m .&. 1) : f (m `B.shiftR` 1)
  in P.reverse $ P.take b $ f n


{- | Convert a vector of @Bool@s representing an unsigned fixed-width integer
to a @Num@ type. Most significant bits are leftmost.

>>> boolsToNum @3 $ fromJust $ VS.fromList [False, False, True]
1
>>> boolsToNum @3 $ fromJust $ VS.fromList [True, False, True]
5
-}
boolsToNum ∷ ∀ (n ∷ Nat) a. (Num a, B.Bits a)
           ⇒ VS.Vector n Bool → a
boolsToNum = boolsToNum' <<< VS.toList

{- | Variation on 'boolsToNum' that takes a vector representing an unsigned
fixed-width @n-1@-bit integer plus a trailing carry bit to a @Num@ type plus that carry
bit. -}
boolsToNumR ∷ ∀ (n ∷ Nat) a. (Num a, B.Bits a)
            ⇒ VS.Vector n Bool → (a, Bool)
boolsToNumR = boolsToNumR' <<< VS.toList

{- | Variation on 'boolsToNum' that takes a vector representing an unsigned
fixed-width @n-1@-bit integer with a leading carry bit to a carry bit plus that
@Num@ type. -}
boolsToNumL ∷ ∀ (n ∷ Nat) a. (Num a, B.Bits a)
            ⇒ VS.Vector n Bool → (Bool, a)
boolsToNumL = boolsToNumL' <<< VS.toList


{- | @numToBools \@n i@ maps @i@ to its representation as an unsigned integer
with @n@ bits of precision and most significant bits leftmost.

>>> numToBools @3 5
Vector [True,False,True]
>>> numToBools @3 8      -- Note overflow
Vector [False, False, False]
-}
numToBools ∷ ∀ (n ∷ Nat) a. (KnownNat n, Num a, B.Bits a)
           ⇒ a → VS.Vector n Bool
numToBools = fromJust <<< VS.fromList <<< numToBools' (fromIntegral $ natVal $ SNat @n)



-------------------------------
-- Evaluation into @Sized (->)@
-------------------------------

instance HasObject VS.Vector (Sized (->))
instance HasProxy VS.Vector (Sized (->))


inTF ∷ ∀ t. Applicative t ⇒ t Bool
inTF = pure True

inFF ∷ ∀ t. Applicative t ⇒ t Bool
inFF = pure False

notF ∷ ∀ t. F.Functor t ⇒ t Bool → t Bool
notF = F.fmap P.not

orF ∷ ∀ t. Foldable t ⇒ t Bool → Bool
orF = P.or

andF ∷ ∀ t. Foldable t ⇒ t Bool → Bool
andF = P.and

norF ∷ ∀ t. Foldable t ⇒ t Bool → Bool
norF = P.not <<< P.or

nandF ∷ ∀ t. Foldable t ⇒ t Bool → Bool
nandF = P.not <<< P.and

iffF ∷ ∀ t. Foldable t ⇒ t Bool → Bool
iffF = uncurry (||)
   <<< (norF CA.&&& andF)

xorF ∷ ∀ t. Foldable t ⇒ t Bool → Bool
xorF =
  let δ False q@(Just False) = q
      δ True    (Just False) = Just True
      δ False q@(Just True ) = q
      δ True    (Just True ) = Nothing
      δ _     q@Nothing      = q
  in  fromMaybe False
  <<< foldr δ (Just False)



-- count ∷ ∀ t n. (Foldable t, Num n) ⇒ t Bool → n
-- count = coerce @(Sum n)
--       <<< P.foldMap (coerce @n <<< bool 0 1)

-- exactlyN ∷ ∀ t n. (Foldable t, Num n, Eq n) ⇒ n → t Bool → Bool
-- exactlyN n = (n ==) <<< count

-- atLeastN ∷ ∀ t n. (Foldable t, Num n, Ord n) ⇒ n → t Bool → Bool
-- atLeastN n = (n >=) <<< count

-- atMostN ∷ ∀ t n. (Foldable t, Num n, Ord n) ⇒ n → t Bool → Bool
-- atMostN n = (n <=) <<< count


{- | This maps each 'Circuit' primitive to an analogue in @(Sized (->))@:

> evalCircuitPrim InT  = Sized $ const    inTF
> evalCircuitPrim InF  = Sized $ const    inFF
> evalCircuitPrim Not  = Sized            notF
> evalCircuitPrim Or   = Sized $ pure <<< orF
> evalCircuitPrim And  = Sized $ pure <<< andF
> evalCircuitPrim Nor  = Sized $ pure <<< norF
> evalCircuitPrim Nand = Sized $ pure <<< nandF
> evalCircuitPrim Xor  = Sized $ pure <<< xorF
> evalCircuitPrim Iff  = Sized $ pure <<< iffF
-}
evalCircuitPrim ∷ ∀ (n ∷ Nat) (m ∷ Nat) a b.
    a -| Circuit      VS.Vector n m |-> b
  → a -| (Sized (->)) VS.Vector n m |-> b
evalCircuitPrim InT  = Sized $ const    inTF
evalCircuitPrim InF  = Sized $ const    inFF
evalCircuitPrim Not  = Sized            notF
evalCircuitPrim Or   = Sized $ pure <<< orF
evalCircuitPrim And  = Sized $ pure <<< andF
evalCircuitPrim Nor  = Sized $ pure <<< norF
evalCircuitPrim Nand = Sized $ pure <<< nandF
evalCircuitPrim Xor  = Sized $ pure <<< xorF
evalCircuitPrim Iff  = Sized $ pure <<< iffF


{- |

> eval ≝ foldMap Prelude.id evalCircuitPrim

>>> (unSized (eval impliesBin)) $ (fromJust $ VS.fromList @2 [True, True])
Vector [True]

See 'foldMap' in "Cat.Sized.Cartesian.Free.Data".
-}
eval ∷ ∀ n m a b.
  ( Object VS.Vector FreeCircuit n a
  , Object VS.Vector FreeCircuit m b
  )
  ⇒ a -| FreeCircuit  VS.Vector n m |-> b
  → a -| (Sized (->)) VS.Vector n m |-> b
eval = foldMap P.id evalCircuitPrim


{- |

> eval' ≝ foldMap Prelude.id evalCircuitPrim >>> unSized

>>> (eval' impliesBin) $ (fromJust $ VS.fromList @2 [True, True])
Vector [True]
>>> (eval' impliesBin) $ (fromJust $ VS.fromList @2 [True, False])
Vector [False]
>>> (eval' impliesBin) $ (fromJust $ VS.fromList @2 [False, True])
Vector [True]
>>> (eval' impliesBin) $ (fromJust $ VS.fromList @2 [False, False])
Vector [True]
-}
eval' ∷ ∀ n m a b.
  ( Object VS.Vector FreeCircuit n a
  , Object VS.Vector FreeCircuit m b
  )
  ⇒ a -| FreeCircuit VS.Vector n m |-> b
  → (VS.Vector n a → VS.Vector m b)
eval' = unSized <<< foldMap P.id evalCircuitPrim




----------------------------------
-- Documentation / testing helpers
----------------------------------

-- {- | Generate all /n/-lists of booleans starting from the all-@True@ list
-- "downward".

-- >>> bnL' 2
-- [[True,True],[True,False],[False,True],[False,False]]
-- -}
-- bnL' ∷ Int → [[Bool]]
-- bnL' 0 = []
-- bnL' 1 = pure <$> [True, False]
-- bnL' n = (:)  <$> [True, False] <*> bnL' (n - 1)


{- | Generate all /n/-lists of booleans starting from the all-@False@ list
"upward".

>>> bnL 2
[[False,False],[False,True],[True,False],[True,True]]
-}
bnL ∷ Int → [[Bool]]
bnL 0 = []
bnL 1 = pure <$> [False, True]
bnL n = (:)  <$> [False, True] <*> bnL (n - 1)


{- | Generate all vectors with @n@ @Bool@s starting from the all-@False@ list
"upward".

>>> bn @2
[Vector [False,False],Vector [False,True],Vector [True,False],Vector [True,True]]
-}
bn ∷ ∀ (n ∷ Nat). (KnownNat n) ⇒ [VS.Vector n Bool]
bn = (VS.fromList @n >>> fromJust)
  <$> bnL (fromIntegral $ natVal $ SNat @n)


-- {- | Generate all pairs of vectors with @n@ @Bool@s. -}
-- bn2 ∷ ∀ (n ∷ Nat). (KnownNat n) ⇒ [VS.Vector 2 (VS.Vector n Bool)]
-- bn2 =  (VS.fromList @2 >>> fromJust   )
--    <$> (second pure    >>> uncurry (:))
--    <$> ((,) <$> bn @n <*> bn @n)



{- | Generate an exhaustive table of inputs and outputs for a function with the
given type, converting the inputs and outputs to lists for ease of manipulation,
e.g. in a REPL. -}
table ∷ ∀ (n ∷ Nat) (m ∷ Nat). (KnownNat n)
      ⇒ (VS.Vector n Bool → VS.Vector m Bool)
      → [([Bool], [Bool])]
table f = P.zip (bnL (fromIntegral $ natVal $ SNat @n)) (VS.toList <$> f <$> bn @n)

-- table' ∷ ∀ (n ∷ Nat) a. (KnownNat n)
--       ⇒ (VS.Vector n Bool → a)
--       → [([Bool], a)]
-- table' f = P.zip (bnL (fromIntegral $ natVal $ SNat @n)) (f <$> bn @n)


{- | Generalization of 'table'. -}
table2 ∷ ∀ (n ∷ Nat) a. (KnownNat n)
      ⇒ (VS.Vector 2 (VS.Vector n Bool) → a)
      → [(([Bool], [Bool]), a)]
table2 f =
  let ins ∷ [(VS.Vector n Bool, VS.Vector n Bool)]
      ins = (,) <$> bn @n <*> bn @n
      f' ∷ (VS.Vector n Bool, VS.Vector n Bool) → a
      f' (x,y) = f $ fromJust <<< VS.fromList $ [x,y]
      f_ ∷ (VS.Vector n Bool, VS.Vector n Bool) → (([Bool], [Bool]), a)
      f_ i@(x,y) = ((VS.toList x, VS.toList y), f' i)
  in f_ <$> ins


-- table2P ∷ ∀ (n ∷ Nat) a. (KnownNat n)
--       ⇒ ((VS.Vector n Bool, VS.Vector n Bool) → Bool)
--       → (VS.Vector 2 (VS.Vector n Bool) → a)
--       → [(([Bool], [Bool]), a)]
-- table2P p f =
--   let ins ∷ [(VS.Vector n Bool, VS.Vector n Bool)]
--       ins = (,) <$> bn @n <*> bn @n
--       f' ∷ (VS.Vector n Bool, VS.Vector n Bool) → a
--       f' (x,y) = f $ fromJust <<< VS.fromList $ [x,y]
--       f_ ∷ (VS.Vector n Bool, VS.Vector n Bool) → (([Bool], [Bool]), a)
--       f_ i@(x,y) = ((VS.toList x, VS.toList y), f' i)
--   in f_ <$> (L.filter p ins)


{- | Specialized variant of 'table2' for concise examples: renders a
most-significant-bit-leftmost sequence of bits as an @Int@. -}
table2I ∷ ∀ n m. (KnownNat n, KnownNat m)
  ⇒ VS.Vector n Bool -| FreeCircuit VS.Vector 2 m |-> Bool
  → [((Int, Int), Int)]
table2I f =
  let intyI = first $ bimap boolsToNum' boolsToNum'
      intyO = boolsToNum
  in  intyI <$> table2 (eval' f >>> intyO)


{- | Specialized variant of 'table2' for concise examples: renders a
most-significant-bit-leftmost sequence of bits as a list of @0@s and @1s@. -}
table2B ∷ ∀ n m. (KnownNat n, KnownNat m)
  ⇒ VS.Vector n Bool -| FreeCircuit VS.Vector 2 m |-> Bool
  → [(([Int], [Int]), [Int])]
table2B f =
  let bitsy  = F.fmap (boolToNum @Int)
      bitsyI = first $ bimap bitsy bitsy
      bitsyO = VS.toList >>> bitsy
  in  bitsyI <$> table2 (eval' f >>> bitsyO)


{- | Specialized variant of 'table2' for concise examples.

 - Renders a most-significant-bit-leftmost sequence of bits as an @Int@.
 - The output bits have a trailing (rightmost) carry bit, presented as a @Bool@.
-}
table2IR ∷ ∀ n m. (KnownNat n, KnownNat m)
  ⇒ VS.Vector n Bool -| FreeCircuit VS.Vector 2 m |-> Bool
  → [((Int, Int), (Int, Bool))]
table2IR f =
  let intyI = first $ bimap boolsToNum' boolsToNum'
      intyO = boolsToNumR
  in  intyI <$> table2 (eval' f >>> intyO)


{- | Specialized variant of 'table2' for concise examples.

 - Renders a most-significant-bit-leftmost sequence of bits as an @Int@.
 - The output bits have a leading (leftmost) carry bit, presented as a @Bool@.
-}
table2IL ∷ ∀ n m. (KnownNat n, KnownNat m)
  ⇒ VS.Vector n Bool -| FreeCircuit VS.Vector 2 m |-> Bool
  → [((Int, Int), (Bool, Int))]
table2IL f =
  let intyI = first $ bimap boolsToNum' boolsToNum'
      intyO = boolsToNumL
  in  intyI <$> table2 (eval' f >>> intyO)



--------------------
-- Recursion schemes
--------------------

{- |
> Cart' k ≝ (Fix (CartF k))
> Cart' k ≅ Cart k

See 'HFunctor' in "Cat.Unsized.Functor"/the resources mentioned there for
background and "Cat.Sized.Functor" for the relevant instance here. -}
type FreeCircuit' = Cart' Circuit
type FreeCircuitF = CartF Circuit


{- | Variant on 'eval' demonstrating the use of recursion schemes with Cartesian
categories.

> evalFreeCircuit ≝ cata $ mkAlg evalCircuitPrim

>>> (unSized $ evalFreeCircuit' impliesBin') $ (fromJust $ VS.fromList @2 [True, True])
Vector [True]
it :: VS.Vector 1 Bool

See 'cata' in 'Cat.Sized.Functor' and 'mkAlg' in 'Cat.Sized.Cartesian.Free.Data'.
-}
evalFreeCircuit' ∷ ∀ n m a b.
    FreeCircuit' VS.Vector n m a b
  → Sized (->)   VS.Vector n m a b
evalFreeCircuit' = cata $ mkAlg evalCircuitPrim



{- | A simple example term of the EDSL: ≈ "λp.λq. ¬p ∨ q".

> impliesBin' = In (EmbF Or)
>             . (   In (EmbF (Not @1))
>               *** In IdF
>               )
-}
impliesBin' ∷ ∀ φ. Bool -| FreeCircuit' φ 2 1 |-> Bool
impliesBin' =
    In (EmbF Or)
  . (   In (EmbF (Not @1))
    *** In IdF
    )


{- | Elementwise 'impliesBin\'' of two /n/-products /p, q/ (the first and second
input /n/-product, respectively), indicating whether \( p_i \implies q_{i} \):

> impliesElem' = join . zipWith impliesBin'
-}
impliesElem' ∷ ∀ φ n. (KnownNat n) ⇒ φ n Bool -| FreeCircuit' φ 2 n |-> Bool
impliesElem' = join . zipWith impliesBin'


{- | Given two /n/-products ("bit vectors") /p, q/ interpretable as subsets of
some /n/-length universe, 'implies' indicates whether membership in /p/ always
entails membership in /q/:

> implies' = In (EmbF And) . impliesElem'
-}
implies' ∷ ∀ φ n. (KnownNat n) ⇒ φ n Bool -| FreeCircuit' φ 2 1 |-> Bool
implies' = In (EmbF And) . impliesElem'



{- | Evaluate @FreeCircuit'@ morphisms by first converting them via a catamorphism
('unfixed') to @FreeCircuit@ morphisms.

>>> (unSized $ evalFreeCircuitUnfixed' $ impliesBin') (fromJust $ VS.fromList @2 [True, True])
Vector [True]
>>> pq = fromJust $ VS.fromList @2 [(fromJust $ VS.fromList @3 [True, False, False]), (fromJust $ VS.fromList @3 [False, True, True])]
pq :: VS.Vector 2 (VS.Vector 3 Bool)
>>> (unSized $ evalFreeCircuitUnfixed' $ implies') pq
Vector [False]
-}
evalFreeCircuitUnfixed' ∷ ∀ n m a b.
  ( Object VS.Vector FreeCircuit' n a
  , Object VS.Vector FreeCircuit' m b
  )
  ⇒ a -| FreeCircuit' VS.Vector n m |-> b
  → a -| (Sized (->)) VS.Vector n m |-> b
evalFreeCircuitUnfixed' = eval <<< unfixed



{- | Evaluate @FreeCircuit@ morphisms by first converting them via an anamorphism
('fixed') to @FreeCircuit'@ morphisms.

>>> (unSized $ evalFreeCircuitFixed $ impliesBin) (fromJust $ VS.fromList @2 [True, True])
Vector [True]
>>> pq = fromJust $ VS.fromList @2 [(fromJust $ VS.fromList @3 [True, False, False]), (fromJust $ VS.fromList @3 [False, True, True])]
pq :: VS.Vector 2 (VS.Vector 3 Bool)
>>> (unSized $ evalFreeCircuitFixed $ implies) pq
Vector [False]
-}
evalFreeCircuitFixed ∷ ∀ n m a b.
    a -| FreeCircuit  VS.Vector n m |-> b
  → a -| (Sized (->)) VS.Vector n m |-> b
evalFreeCircuitFixed = evalFreeCircuit' <<< fixed
