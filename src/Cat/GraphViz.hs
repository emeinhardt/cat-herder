{-# OPTIONS_HADDOCK show-extensions #-}
-- |

module Cat.GraphViz
  (
  ) where


import Prelude hiding
  ( id
  , (.)
  )

import Cat.Operators

import Cat.Unsized.Functor

import Cat.Unsized.Category.Class
import Cat.Unsized.Category.Instances

import Cat.Unsized.Category.Free.Data
import Cat.Unsized.Category.Free.Instances

-- import Algebra.Graph

import Language.Dot


{- TODO continuation:
 - Figure out how to produce a single node with two wires representing `id`.

 - Figure out what kind of gadget (a collection of node statements? plus some
   state for identifier generation?) corresponds to a morphism.

 - Figure out how composition maps to node/edge statements.

 - You might need/want a monad for identifier generation
   - That probably means top-down generation (i.e. a coalgebra) is going to be easier
     without further thought about fresh name generation.
-}

-- idG =

-- type Graph' = K Graph

-- instance Semigroupoid Graph' where
--   (K g) . (K f) = undefined

-- instance Category Graph' where
--   id = K undefined


-- -- catGraph ∷ Maybe Id → [Statement] → Graph
-- -- catGraph = Graph UnstrictGraph DirectedGraph
catGraph ∷ [Statement] → Graph
catGraph = Graph UnstrictGraph DirectedGraph Nothing


idNodeStatement ∷ Statement
idNodeStatement = NodeStatement (NodeId (IntegerId 0) Nothing)
                                []

-- intoGraph ∷ a -| Cat' k |-> b
--           → a -| Graph' |-> b
-- intoGraph = cata graphAlg

-- graphAlg ∷
--     a -| CatF k Graph' |-> b
--   → a -| Graph' |-> b
-- graphAlg = mkAlg f where
--   f ∷ a `k` b → a -| Graph' |-> b
--   f = undefined
-- -- intoGraphAlg IdF         = id
-- -- intoGraphAlg (g `OfF` f) =
-- -- intoGraphAlg (EmbF m)    = undefined

-- -- intoGraph ∷ a -| Cat' k |-> b → Graph (a -| Cat' k |-> b)
-- -- intoGraph (In IdF) = undefined
-- -- intoGraph (In IdF) = undefined


-- -- intoGraphAlg ∷ _
-- -- intoGraphAlg = undefined
