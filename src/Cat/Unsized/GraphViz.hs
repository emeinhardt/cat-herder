{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{- | This module contains functionality for pretty-printing an "unsized" morphism
in a free category type to a
@[language-dot](https://hackage.haskell.org/package/language-dot)@ 'Graph' AST;
such an AST can then be pretty-printed to a @DOT@-language expression which can
then be rendered as an image of a directed graph.

This is currently implemented in terms of "Cat.Unsized.Category.Free.TTG", i.e.
GraphViz-related annotations are added via the "trees-that-grow" approach to the
AST-typing problem. See the TTG module for more context. -}

module Cat.Unsized.GraphViz
  ( GV
  , CatG
  , CatFG
  , CatG'
  , RankDir ( TB
            , LR
            )

  , catGraph
  , catGraphF
  , catGraph'
  , catGraphWith
  , catGraphWithF
  , catGraphWith'

  , prelude

  , reNodeId
  , reNodeId'
  ) where


import Prelude hiding
  ( id
  , (.)
  , Functor
  , fmap
  )

import Control.Arrow
  ( (&&&)
  )

import Control.Monad.State
  ( evalState
  , State
  , MonadState ( put
               , get
               )
  )

import GHC.Generics
  ( Generic
  )


import Data.Functor qualified as F

import Data.List    qualified as L
import Data.Maybe
  ( maybeToList
  )

import Cat.Operators
  ( type (-|)
  , type (|->)
  )

import Cat.Unsized.Functor
  ( Fix ( In
        , out
        )
  )

import Cat.Unsized.Category.Class
  ( Semigroupoid ( Object
                 , (.)
                 )
  , Category ( id
             )
  )
import Cat.Unsized.Category.Instances ()

-- import Cat.Unsized.Category.Free.Data
-- import Cat.Unsized.Category.Free.Instances

import Cat.Unsized.Category.Free.TTG
  ( HasObject ( ObjectOf
              )
  , XOf
  , Cat ( Of
        , Id
        , Emb
        )
  , NoField ( NoField
            )
  , XId
  , CatF ( OfF
         , IdF
         , EmbF
         )
  , XEmb
  , XXCat
  , NoExt
  , Cat'
  , unfixed
  )


import Language.Dot
  ( Graph ( Graph
          )
  , Statement ( AttributeStatement
              , NodeStatement
              , EdgeStatement
              , AssignmentStatement
              )
  , NodeId ( NodeId
           )
  , Attribute ( AttributeSetValue
              )
  , AttributeStatementType ( NodeAttributeStatement
                           )
  , EdgeType ( DirectedEdge
             , NoEdge
             )
  , Entity ( ENodeId
           )
  , GraphDirectedness ( DirectedGraph
                      )
  , GraphStrictness ( UnstrictGraph
                    )
  , Id ( StringId
       , IntegerId
       )
  , Port ( PortI
         )
  )




{- | GraphViz phase index. -}
data GV

type CatG    = Cat  GV
type CatFG   = CatF GV
type CatG' k = Cat' GV k


type instance XEmb  GV = Maybe Int
type instance XId   GV = Maybe Int
type instance XOf   GV = NoField
type instance XXCat GV = NoExt


instance Semigroupoid (CatG k) where
  type Object (CatG k) a = ObjectOf k a
  g . f = Of NoField g f

instance Category (CatG k) where
  id = Id Nothing

instance Semigroupoid (CatFG k (CatG' k)) where
  type Object (CatFG k (CatG' k)) a = ObjectOf k a
  g . f = OfF NoField (In g) (In f)

instance Category (CatFG k (CatG' k)) where
  id = IdF Nothing



sourceNodeIdOf ∷ ∀ k a b.
    a -| CatG k |-> b
  → Maybe Int
sourceNodeIdOf (Id  nid  ) = nid
sourceNodeIdOf (Emb nid _) = nid
sourceNodeIdOf (Of  _ _ f) = sourceNodeIdOf f
-- sourceNodeIdOf (XCat x    ) = noExt x


sourceNodeIdOfF ∷ ∀ k a b.
    a -| CatFG k (CatG' k) |-> b
  → Maybe Int
sourceNodeIdOfF (IdF   nid  ) = nid
sourceNodeIdOfF (EmbF  nid _) = nid
sourceNodeIdOfF (OfF   _ _ f) = sourceNodeIdOfF . out $ f
-- sourceNodeIdOfF (XCatF x    ) = noExt x


targetNodeIdOf ∷ ∀ k a b.
    a -| CatG k |-> b
  → Maybe Int
targetNodeIdOf (Id  nid  ) = nid
targetNodeIdOf (Emb nid _) = nid
targetNodeIdOf (Of  _ g _) = targetNodeIdOf g
-- targetNodeIdOf (XCat x    ) = noExt x


targetNodeIdOfF ∷ ∀ k a b.
    a -| CatFG k (CatG' k) |-> b
  → Maybe Int
targetNodeIdOfF (IdF  nid  ) = nid
targetNodeIdOfF (EmbF nid _) = nid
targetNodeIdOfF (OfF  _ g _) = targetNodeIdOfF . out $ g
-- targetNodeIdOfF (XCatF x    ) = noExt x


nodeIdOf ∷ ∀ k a b.
    a -| CatG k |-> b
  → Maybe Int
nodeIdOf (Id  nid  ) = nid
nodeIdOf (Emb nid _) = nid
nodeIdOf (Of  {}   ) = Nothing
-- nodeIdOf (XCat x    ) = noExt x


nodeIdOfF ∷ ∀ k a b.
    a -| CatFG k (CatG' k) |-> b
  → Maybe Int
nodeIdOfF (IdF   nid  ) = nid
nodeIdOfF (EmbF  nid _) = nid
nodeIdOfF (OfF   {}   ) = Nothing
-- nodeIdOfF (XCatF x    ) = noExt x




data PreNodeLabel = PreNodeLabel { ins      ∷ !Int
                                 , outs     ∷ !Int
                                 , showName ∷ !String
                                 }
  deriving stock (Eq, Ord, Show, Read, Generic)


data RankDir = TB | LR
  deriving stock (Eq, Ord, Show, Read, Generic)



show_ ∷ ∀ a. (Show a) ⇒ a → String
show_ a
  | (L.take 3 . head . words . show $ a) == "Emb" = unwrapThis "(" ")" . unwords . L.drop 3 . words . show $ a
  | otherwise = unwords . (take =<< (subtract 2 . length)) . words . show $ a



preNodeLabel ∷ ∀ k a b. (Show (a -| CatG k |-> b))
  ⇒ a -| CatG k |-> b
  → PreNodeLabel
preNodeLabel = PreNodeLabel 1 1 . show_


preNodeLabelF ∷ ∀ k a b. (Show (a -| CatG k |-> b))
  ⇒ a -| CatFG k (CatG' k) |-> b
  → PreNodeLabel
preNodeLabelF = PreNodeLabel 1 1 . show_ . unfixed . In




morphismNodeStatement ∷ ∀ k a b. (Show (a -| CatG k |-> b))
  ⇒ RankDir
  → a -| CatG k |-> b
  → Maybe Statement
morphismNodeStatement LR f = NodeStatement
                          <$> morphismNodeStatementId f
                          <*> pure [AttributeSetValue (StringId "label")
                                                      (StringId . morphismNodeLabel
                                                                . preNodeLabel
                                                                $ f)
                                   ]
morphismNodeStatement TB f = NodeStatement
                          <$> morphismNodeStatementId f
                          <*> pure [AttributeSetValue (StringId "label")
                                                      (StringId . brack'
                                                                . morphismNodeLabel
                                                                . preNodeLabel
                                                                $ f)
                                   ]

morphismNodeStatementF ∷ ∀ k a b. (Show (a -| CatG k |-> b))
  ⇒ RankDir
  → a -| CatFG k (CatG' k) |-> b
  → Maybe Statement
morphismNodeStatementF LR f = NodeStatement
                           <$> morphismNodeStatementIdF f
                           <*> pure [AttributeSetValue (StringId "label")
                                                       (StringId . morphismNodeLabel
                                                                 . preNodeLabelF
                                                                 $ f)
                                    ]
morphismNodeStatementF TB f = NodeStatement
                           <$> morphismNodeStatementIdF f
                           <*> pure [AttributeSetValue (StringId "label")
                                                       (StringId . brack'
                                                                 . morphismNodeLabel
                                                                 . preNodeLabelF
                                                                 $ f)
                                   ]



morphismNodeStatementId ∷ a -| CatG k |-> b → Maybe NodeId
morphismNodeStatementId = F.fmap ( flip NodeId Nothing
                                 . IntegerId
                                 . fromIntegral
                                 )
                        . nodeIdOf


morphismNodeStatementIdF ∷ a -| CatFG k (CatG' k) |-> b → Maybe NodeId
morphismNodeStatementIdF = F.fmap ( flip NodeId Nothing
                                  . IntegerId
                                  . fromIntegral
                                  )
                         . nodeIdOfF


{- |
>>> morphismNodeLabel (PreNodeLabel 3 1 "Or 3")
"{ <i0> | <i1> | <i2> } | Or 3 | { <o0> }"
-}
morphismNodeLabel ∷ PreNodeLabel → String
morphismNodeLabel = bar
                  . ([nodeLabelHelperIns, showName, nodeLabelHelperOuts] <*>)
                  . pure


{- |

>>> nodeLabelHelperIns (PreNodeLabel 3 2 "foo")
"{ <i0> | <i1> | <i2> }"
-}
nodeLabelHelperIns ∷ PreNodeLabel → String
nodeLabelHelperIns = brack'
                   . bar
                   . L.map (ang . ("i" ++) . show)
                   . enumFromTo 0
                   . subtract 1
                   . ins


{- |

>>> nodeLabelHelperOuts (PreNodeLabel 2 3 "foo")
"{ <o0> | <o1> | <o2> }"
-}
nodeLabelHelperOuts ∷ PreNodeLabel → String
nodeLabelHelperOuts = brack'
                    . bar
                    . L.map (ang . ("o" ++) . show)
                    . enumFromTo 0
                    . subtract 1
                    . outs



wrap ∷ ∀ a. [a] → [a] → [a] → [a]
wrap l r s = l ++ s ++ r

wrap' ∷ String → String → String → String
wrap' l r s = unwords [l, s, r]

unwrapThis ∷ ∀ a. (Eq a) ⇒ [a] → [a] → [a] → [a]
unwrapThis l r s =
  let pre = take (length l)
      suf = reverse . take (length r) . reverse
  in if   pre s == l && suf s == r
     then reverse . drop (length r) . reverse . drop (length l) $ s
     else s

-- unwrap ∷ ∀ a. [a] → [a]
-- unwrap = L.init . L.tail

-- brack ∷ String → String
-- brack = wrap "{" "}"

brack' ∷ String → String
brack' = wrap' "{" "}"

ang ∷ String → String
ang = wrap "<" ">"

bar ∷ [String] → String
bar = L.intercalate " | "



morphismNodeStatements ∷ ∀ k a b. (∀ u v. Show (u `k` v))
  ⇒ RankDir
  → a -| CatG k |-> b
  → [Statement]
morphismNodeStatements d (Of _ g f) = morphismNodeStatements d g ++ morphismNodeStatements d f
morphismNodeStatements d f          = maybeToList $ morphismNodeStatement d f


morphismNodeStatementsF ∷ ∀ k a b. (∀ u v. Show (u -| CatG k |-> v))
  ⇒ RankDir
  → a -| CatFG k (CatG' k) |-> b
  → [Statement]
morphismNodeStatementsF d (OfF _ (In g) (In f)) = morphismNodeStatementsF d g ++ morphismNodeStatementsF d f
morphismNodeStatementsF d f                     = maybeToList $ morphismNodeStatementF d f



morphismEdgeStatements ∷ ∀ k a b.
    a -| CatG k |-> b
  → [Statement]
morphismEdgeStatements (Of _ g f) = morphismEdgeStatements' g f
morphismEdgeStatements _          = []

morphismEdgeStatementsF ∷ ∀ k a b.
    a -| CatFG k (CatG' k) |-> b
  → [Statement]
morphismEdgeStatementsF (OfF _ (In g) (In f)) = morphismEdgeStatementsF' g f
morphismEdgeStatementsF _                     = []


morphismEdgeStatements' ∷ ∀ k a c b.
    b -| CatG k |-> c
  → a -| CatG k |-> b
  → [Statement]
morphismEdgeStatements' g f =
  let fId = targetNodeId f
      gId = sourceNodeId g

      entities ∷ NodeId → NodeId → [Entity]
      entities from to = [ENodeId NoEdge from, ENodeId DirectedEdge to]
  in  maybeToList (EdgeStatement <$> (entities <$> fId <*> gId) <*> pure [])
   ++ morphismEdgeStatements g
   ++ morphismEdgeStatements f


morphismEdgeStatementsF' ∷ ∀ k a c b.
    b -| CatFG k (CatG' k) |-> c
  → a -| CatFG k (CatG' k) |-> b
  → [Statement]
morphismEdgeStatementsF' g f =
  let fId = targetNodeIdF f
      gId = sourceNodeIdF g

      entities ∷ NodeId → NodeId → [Entity]
      entities from to = [ENodeId NoEdge from, ENodeId DirectedEdge to]
  in  maybeToList (EdgeStatement <$> (entities <$> fId <*> gId) <*> pure [])
   ++ morphismEdgeStatementsF g
   ++ morphismEdgeStatementsF f


sourceNodeId ∷ ∀ k a b.
    a -| CatG k |-> b
  → Maybe NodeId
sourceNodeId = F.fmap ( flip NodeId (Just . flip PortI Nothing $ StringId "i0" )
                      . IntegerId
                      . fromIntegral
                      )
             . sourceNodeIdOf

sourceNodeIdF ∷ ∀ k a b.
    a -| CatFG k (CatG' k) |-> b
  → Maybe NodeId
sourceNodeIdF = F.fmap ( flip NodeId (Just . flip PortI Nothing $ StringId "i0" )
                       . IntegerId
                       . fromIntegral
                       )
              . sourceNodeIdOfF

targetNodeId ∷ ∀ k a b.
    a -| CatG k |-> b
  → Maybe NodeId
targetNodeId = F.fmap ( flip NodeId (Just . flip PortI Nothing $ StringId "o0" )
                      . IntegerId
                      . fromIntegral
                      )
             . targetNodeIdOf

targetNodeIdF ∷ ∀ k a b.
    a -| CatFG k (CatG' k) |-> b
  → Maybe NodeId
targetNodeIdF = F.fmap ( flip NodeId (Just . flip PortI Nothing $ StringId "o0" )
                       . IntegerId
                       . fromIntegral
                       )
              . targetNodeIdOfF


{- | A prelude of statements setting global defaults for GraphViz digraphs:

> prelude = [ AssignmentStatement (StringId "margin")   (IntegerId 0)
>           , AssignmentStatement (StringId "compound") (StringId "true")
>           , AssignmentStatement (StringId "nslimit")  (IntegerId 20)
>           , AttributeStatement NodeAttributeStatement
>                                [AttributeSetValue (StringId "shape") (StringId "Mrecord")]
>           ]

-}
prelude ∷ [Statement]
prelude = [ AssignmentStatement (StringId "margin")   (IntegerId 0)
          , AssignmentStatement (StringId "compound") (StringId "true")
          , AssignmentStatement (StringId "nslimit")  (IntegerId 20)
          , AttributeStatement NodeAttributeStatement
                               [AttributeSetValue (StringId "shape") (StringId "Mrecord")]
          ]




type NodeIdState = Int

-- TODO After refactoring HFunctor into its own module, explore adding an HMonad
-- class and using an effectful anamorphism instead of the current strategy:
-- a state monad depth-first traversal of a binary tree that incidentally contains
-- bifunctors contravariant in one parameter and covariant in the other.
{- | Recalculate the unique node identifier for each non-composition term from the
top down. -}
reNodeId ∷ ∀ k a b.
    a -| CatG k |-> b
  → a -| CatG k |-> b
reNodeId f = evalState (reNodeId_ f) 0

reNodeId_ ∷ ∀ k a b.
    a -| CatG k |-> b
  → State NodeIdState (a -| CatG k |-> b)
reNodeId_ (Id _) = do
  q ← get
  put (q + 1)
  return (Id $ Just q)
reNodeId_ (Emb _ f) = do
  q ← get
  put (q + 1)
  return (Emb (Just q) f)
reNodeId_ (Of _ g f) = do
  g' ← reNodeId_ g
  f' ← reNodeId_ f
  return (Of NoField g' f')


{- | Recalculate the unique node identifier for each non-composition term from the
top down. -}
reNodeId' ∷ ∀ k a b.
    a -| CatG' k |-> b
  → a -| CatG' k |-> b
reNodeId' f = evalState (reNodeId_' f) 0


reNodeId_' ∷ ∀ k a b.
    a -| CatG' k |-> b
  → State NodeIdState (a -| CatG' k |-> b)
reNodeId_' (In (IdF _)) = do
  q ← get
  put (q + 1)
  return $ In $ IdF (Just q)
reNodeId_' (In (EmbF _ f)) = do
  q ← get
  put (q + 1)
  return $ In $ EmbF (Just q) f
reNodeId_' (In (OfF _ g f)) = do
  g' ← reNodeId_' g
  f' ← reNodeId_' f
  return $ In $ OfF NoField g' f'



{- | @catGraph d f@ maps a @CatG@ value to a @language-dot@ AST. -}
catGraph ∷ ∀ k a b. (∀ u v. Show (u `k` v))
  ⇒ RankDir            -- ^ The orientation ('rankdir') of the GraphViz digraph.
  → a -| CatG k |-> b
  → Graph
catGraph d = catGraphHelper
           . (prelude ++)
           . uncurry (++)
           . (morphismNodeStatements d &&& morphismEdgeStatements)


{- | @catGraphF d f@ maps a @CatFG@ value to a @language-dot@ AST. -}
catGraphF ∷ ∀ k a b. (∀ u v. Show (u -| CatG k |-> v))
  ⇒ RankDir                       -- ^ The orientation ('rankdir') of the GraphViz digraph.
  → a -| CatFG k (CatG' k) |-> b
  → Graph
catGraphF d = catGraphHelper
            . (prelude ++)
            . uncurry (++)
            . (morphismNodeStatementsF d &&& morphismEdgeStatementsF)


{- | @catGraph' d f@ maps a @CatG'@ value to a @language-dot@ AST. -}
catGraph' ∷ ∀ k a b. (∀ u v. Show (u -| CatG k |-> v))
  ⇒ RankDir              -- ^ The orientation ('rankdir') of the GraphViz digraph.
  → a -| CatG' k |-> b
  → Graph
catGraph' d = catGraphHelper
            . (prelude ++)
            . uncurry (++)
            . (morphismNodeStatementsF d &&& morphismEdgeStatementsF)
            . out


catGraphHelper ∷ [Statement] → Graph
catGraphHelper = Graph UnstrictGraph DirectedGraph Nothing


catGraphHelperWith ∷ Maybe Id → [Statement] → Graph
catGraphHelperWith = Graph UnstrictGraph DirectedGraph



{- | @catGraphWith graphName prelude d f@ maps a @CatG@ value to a @language-dot@
AST where the resulting @dot@ graph has the name @graphName@ and the prelude of
'Statement's given by @prelude@. -}
catGraphWith ∷ ∀ k a b. (∀ u v. Show (u `k` v))
  ⇒ Maybe Id            -- ^ A name for the resulting digraph.
  → [Statement]         -- ^ A 'prelude' of statements defining global properties of the digraph.
  → RankDir             -- ^ The orientation ('rankdir') of the GraphViz digraph.
  → a -| CatG k |-> b
  → Graph
catGraphWith graphName prelude' d =
      catGraphHelperWith graphName
    . (prelude' ++)
    . uncurry (++)
    . (morphismNodeStatements d &&& morphismEdgeStatements)


{- | @catGraphWithF graphName prelude d f@ maps a @CatFG k (CatG' k)@ value to a
@language-dot@ AST where the resulting @dot@ graph has the name @graphName@ and
the prelude of 'Statement's given by @prelude@. -}
catGraphWithF ∷ ∀ k a b. (∀ u v. Show (u -| CatG k |-> v))
  ⇒ Maybe Id                       -- ^ A name for the resulting digraph.
  → [Statement]                    -- ^ A 'prelude' of statements defining global properties of the digraph.
  → RankDir                        -- ^ The orientation ('rankdir') of the GraphViz digraph.
  → a -| CatFG k (CatG' k) |-> b
  → Graph
catGraphWithF graphName prelude' d =
      catGraphHelperWith graphName
    . (prelude' ++)
    . uncurry (++)
    . (morphismNodeStatementsF d &&& morphismEdgeStatementsF)


{- | @catGraphWith' graphName prelude d f@ maps a @CatG' k@ value to a
@language-dot@ AST where the resulting @dot@ graph has the name @graphName@ and
the prelude of 'Statement's given by @prelude@. -}
catGraphWith' ∷ ∀ k a b. (∀ u v. Show (u `k` v))
  ⇒ Maybe Id            -- ^ A name for the resulting digraph.
  → [Statement]         -- ^ A 'prelude' of statements defining global properties of the digraph.
  → RankDir             -- ^ The orientation ('rankdir') of the GraphViz digraph.
  → a -| CatG' k |-> b
  → Graph
catGraphWith' graphName prelude' d =
      catGraphHelperWith graphName
    . (prelude' ++)
    . uncurry (++)
    . (morphismNodeStatementsF d &&& morphismEdgeStatementsF)
    . out

