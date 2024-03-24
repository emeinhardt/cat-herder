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
details like this, see the Boolean circuits (combinational logic) module
"Cat.Sized.Examples.Circuit" or the discussion in the README. -}

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
  , Semigroupoid
  , Category
  , (.)
  , id
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

import Cat.Unsized.Category.Free.TTG qualified as TTG
import Cat.Unsized.Category.Free.TTG
  ( noExt
  , NoField ( NoField )
  )

import Cat.Unsized.GraphViz
  ( catGraph
  , catGraph'
  , reNodeId
  , reNodeId'
  , GV
  , RankDir
  )

import Data.Void (Void)

import Language.Dot
  ( Graph
  )


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
evalFreeArithUnfixed' = evalFreeArith . unfixed



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



-- Trees That Grow + GraphViz


{- | @FreeArithX@ ≅ @FreeArith@: The phase index is @Void@, and — per the @X____@
type family instances — there are no extension fields and no extension
constructor.

Instrumentally, @FreeArithX@ is a convenient but not strictly necessary bridge
into any other "trees-that-grow"-based free category type; it's presented here as
the simplest possible trees-that-grow variant. -}
type FreeArithX  = TTG.Cat  Void ArithFunc

{- | @FreeArithT'@ ≅ @FreeArith'@. -}
type FreeArithT' = TTG.Cat' Void ArithFunc

{- | @FreeArithFT@ ≅ @FreeArithF@. -}
type FreeArithFT = TTG.CatF Void ArithFunc


type instance TTG.XEmb  Void = TTG.NoField
type instance TTG.XId   Void = TTG.NoField
type instance TTG.XOf   Void = TTG.NoField
type instance TTG.XXCat Void = TTG.NoExt



instance Semigroupoid FreeArithX where
  type Object FreeArithX a = ObjectOf ArithFunc a
  g . f = TTG.Of NoField g f


instance Category FreeArithX where
  id = TTG.Id NoField


instance Semigroupoid (FreeArithFT FreeArithT') where
  type Object (FreeArithFT FreeArithT') a = ObjectOf ArithFunc a
  g . f = TTG.OfF NoField (In g) (In f)


instance Category (FreeArithFT FreeArithT') where
  id = TTG.IdF NoField



{- | Map a 'FreeArith' value into its "trees that grow" equivalent. -}
grow ∷ ∀ a b. FreeArith a b → FreeArithX a b
grow Id         = TTG.Id  NoField
grow (Emb k)    = TTG.Emb NoField k
grow (g `Of` f) = TTG.Of  NoField (grow g) (grow f)


{- | Map a "trees that grow" 'FreeArithX' value into its more basic 'FreeArith' form. -}
shrink ∷ ∀ a b. FreeArithX a b → FreeArith a b
shrink (TTG.Id  _    ) = Id
shrink (TTG.Emb _ k  ) = Emb k
shrink (TTG.Of  _ g f) = shrink g `Of` shrink f


{- | Map a @FreeArith'@ value into its "trees that grow" equivalent. -}
grow' ∷ ∀ a b. FreeArith' a b → FreeArithT' a b
grow' = cata $ mkAlg (In . TTG.EmbF TTG.NoField)


{- | Map a "trees that grow" @FreeArithT'@ value into its more basic @FreeArith'@
form. -}
shrink' ∷ ∀ a b. FreeArithT' a b → FreeArith' a b
shrink' = cata $ TTG.mkAlg noExt (In . EmbF)



{- | @FreeArithG@ ≅ @FreeArith@ ≅ @CatG ArithFunc@: The phase index is @GV@
("GraphViz"), and — per the @X____@ type family instances in
"Cat.Unsized.GraphViz" — there are extension fields containing auxiliary
annotations useful for rendering a free category term as a GraphViz expression. -}
type FreeArithG  = TTG.Cat  GV ArithFunc  -- ≡ GV.CatG  ArithFunc


{- | @FreeArithG'@ ≅ @FreeArith'@ ≅ @CatG' ArithFunc@. -}
type FreeArithG' = TTG.Cat' GV ArithFunc  -- ≡ GV.CatG' ArithFunc


{- | @FreeArithFT@ ≅ @FreeArithF@ ≅ @CatFG ArithFunc@. -}
type FreeArithFG = TTG.CatF GV ArithFunc



{- | Change the extension field type from @NoField@ to an annotation type for
pretty-printing to GraphViz. -}
graphExt ∷ ∀ a b. FreeArithX a b → FreeArithG a b
graphExt = TTG.foldMap noExt (TTG.Emb Nothing)


{- | Convert a @FreeArith@ value to a
@[language-dot](https://hackage.haskell.org/package/language-dot)@ 'Graph'
AST.

>>> import Language.Dot
>>> import Text.Pretty.Simple ( pPrint )
>>> import Cat.Unsized.GraphViz ( RankDir (TB) )
>>> pPrint $ toGraph TB alsoOne
Graph UnstrictGraph DirectedGraph Nothing
    [ AssignmentStatement
        ( StringId "margin" )
        ( IntegerId 0 )
    , AssignmentStatement
        ( StringId "compound" )
        ( StringId "true" )
    , AssignmentStatement
        ( StringId "nslimit" )
        ( IntegerId 20 )
    , AttributeStatement NodeAttributeStatement
        [ AttributeSetValue
            ( StringId "shape" )
            ( StringId "Mrecord" )
        ]
    , NodeStatement
        ( NodeId
            ( IntegerId 0 ) Nothing
        )
        [ AttributeSetValue
            ( StringId "label" )
            ( StringId "{ { <i0> } | Dec | { <o0> } }" )
        ]
    , NodeStatement
        ( NodeId
            ( IntegerId 1 ) Nothing
        )
        [ AttributeSetValue
            ( StringId "label" )
            ( StringId "{ { <i0> } | Lit 2 | { <o0> } }" )
        ]
    , EdgeStatement
        [ ENodeId NoEdge
            ( NodeId
                ( IntegerId 1 )
                ( Just
                    ( PortI
                        ( StringId "o0" ) Nothing
                    )
                )
            )
        , ENodeId DirectedEdge
            ( NodeId
                ( IntegerId 0 )
                ( Just
                    ( PortI
                        ( StringId "i0" ) Nothing
                    )
                )
            )
        ] []
    ]
>>> prettyPrintDot $ toGraph TB alsoOne
digraph {
  "margin"=0
  "compound"="true"
  "nslimit"=20
  node ["shape"="Mrecord"]
  0 ["label"="{ { <i0> } | Dec | { <o0> } }"]
  1 ["label"="{ { <i0> } | Lit 2 | { <o0> } }"]
  1:"o0" -> 0:"i0"
}
-}
toGraph ∷ ∀ a b. RankDir → FreeArith a b → Graph
toGraph d = catGraph d
          . reNodeId
          . graphExt
          . grow


{- | Change the extension field type from @NoField@ to an annotation type for
pretty-printing to GraphViz. -}
graphExt' ∷ ∀ a b. FreeArithT' a b → FreeArithG' a b
graphExt' = cata $ TTG.mkAlg noExt (In . TTG.EmbF Nothing)


{- | Convert a @FreeArith'@ value to a
@[language-dot](https://hackage.haskell.org/package/language-dot)@ 'Graph'
AST.

>>> import Language.Dot
>>> import Text.Pretty.Simple ( pPrint )
>>> import Cat.Unsized.GraphViz ( RankDir (TB) )
>>> pPrint $ toGraph' TB alsoOne'
Graph UnstrictGraph DirectedGraph Nothing
    [ AssignmentStatement
        ( StringId "margin" )
        ( IntegerId 0 )
    , AssignmentStatement
        ( StringId "compound" )
        ( StringId "true" )
    , AssignmentStatement
        ( StringId "nslimit" )
        ( IntegerId 20 )
    , AttributeStatement NodeAttributeStatement
        [ AttributeSetValue
            ( StringId "shape" )
            ( StringId "Mrecord" )
        ]
    , NodeStatement
        ( NodeId
            ( IntegerId 0 ) Nothing
        )
        [ AttributeSetValue
            ( StringId "label" )
            ( StringId "{ { <i0> } | Dec | { <o0> } }" )
        ]
    , NodeStatement
        ( NodeId
            ( IntegerId 1 ) Nothing
        )
        [ AttributeSetValue
            ( StringId "label" )
            ( StringId "{ { <i0> } | Lit 2 | { <o0> } }" )
        ]
    , EdgeStatement
        [ ENodeId NoEdge
            ( NodeId
                ( IntegerId 1 )
                ( Just
                    ( PortI
                        ( StringId "o0" ) Nothing
                    )
                )
            )
        , ENodeId DirectedEdge
            ( NodeId
                ( IntegerId 0 )
                ( Just
                    ( PortI
                        ( StringId "i0" ) Nothing
                    )
                )
            )
        ] []
    ]
>>> prettyPrintDot $ toGraph' TB alsoOne'
digraph {
  "margin"=0
  "compound"="true"
  "nslimit"=20
  node ["shape"="Mrecord"]
  0 ["label"="{ { <i0> } | Dec | { <o0> } }"]
  1 ["label"="{ { <i0> } | Lit 2 | { <o0> } }"]
  1:"o0" -> 0:"i0"
}
-}
toGraph' ∷ ∀ a b. RankDir → FreeArith' a b → Graph
toGraph' d = catGraph' d
           . reNodeId'
           . graphExt'
           . grow'
