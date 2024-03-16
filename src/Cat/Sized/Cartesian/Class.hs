{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- |

module Cat.Sized.Cartesian.Class
  ( Cartesian

    -- * Re-exports from "Cat.Sized.Monoidal"
  , Monoidal ( Proxy
             , Unit
             , (***)
             , mul
             , ith
             , ith'
               -- * Nested product combinators
             , join
             , split
             , assoc
             , sing
             , unsing
             , lift1
             , bisplit
             , bijoin
             , biassoc
             )
  , (+++)
  , (|.|)
  , (|+|)
  , (⊗)
  , (⊕)
  , Solo   (Solo  , unSolo)
  , Factor (Factor, unFactor)
  , omap
  , gmap

    -- * Re-exports from "Cat.Sized.Braided"
  , Braided ( SwapObject
            , swap
            -- , swap'
            )
  , SwapObject'
  , swapRep
  , Permutable ( PermObject
               -- , Perm
               , permute
               )
  , PermObject'
  , permRep
  , permRep'
  , zipPermIdxs
  , zipPerm
  , reverse

    -- * Re-exports from "Cat.Sized.Diagonal"
  , Diagonal ( DupObject
             , dup
             , dup'
             , (&&&)
             , fork
             )
  , DupObject'
  , (△)
  , dupRep
  , fork2
  , fork3

    -- * Re-exports from "Cat.Sized.Semicartesian"
  , Semicartesian ( ProjObject
                  , idx
                  )
  , index
  , π
  , ProjObject'
  , idxRep
  , FinRep (FinRep, unFinRep)
  , idxs
  , idxs'
  , HasTerminal (terminal)
  , Delete ( DelObject
           , del
           )
  , DelObject'
  , Select ( SelectObject
           , sel
           )
  , SelectObject'
  , unfork
  , head
  , tail
  , last
  , init
  , prefix
  , suffix
  , take
  , drop

  ) where

-- TODO cleanup after testing

import Prelude hiding
  ( (.)
  , id
  , Functor
  , fmap
  , zip
  , zipWith
  , reverse
  , head
  , tail
  , last
  , init
  , take
  , drop
  )
-- import Control.Arrow qualified as A
-- import Prelude.Unicode ((∘))

-- import Data.Kind ( Type
--                  -- , Constraint
--                  )
-- import Data.Constraint.Trivial
--   ( Unconstrained4
--   , Unconstrained5
--   )

-- import GHC.TypeNats
--   ( KnownNat
--   , Nat
--   , SNat
--   , pattern SNat
--   , type (*)
-- --   , type (+)
--   , type (-)
--   , type (<=)
--   , SomeNat (SomeNat)
--   , someNatVal
--   , withSomeSNat
--   )
-- import Data.Finite
--   ( Finite
--   , natToFinite
--   , finites
--   )
-- import Data.Proxy qualified as P
-- import Data.Proxy (Proxy (Proxy))

-- import Data.List qualified as L

-- import Cat.Operators (type (-|), type (|->))

-- import Cat.Sized.Functor
--   ( Functor
--   )

import Cat.Sized.Category.Class
  -- ( Object
  -- , Sub (Sub)
  -- , (⊙)
  -- )
import Cat.Sized.Monoidal.Class
  ( Monoidal ( Proxy
             , Unit
             , (***)
             , mul
             , ith
             , ith'
             , join
             , split
             , assoc
             , sing
             , unsing
             , lift1
             , bisplit
             , bijoin
             , biassoc
             )
  , (+++)
  , (|.|)
  , (|+|)
  , (⊗)
  , (⊕)
  -- , ProdK
  , Solo   (Solo  , unSolo)
  , Factor (Factor, unFactor)
  , omap
  , gmap
  )
import Cat.Sized.Braided.Class
  ( Braided ( SwapObject
            , swap
            -- , swap'
            )
  , SwapObject'
  , swapRep
  , Permutable ( PermObject
               -- , Perm
               , permute
               )
  , PermObject'
  , permRep
  , permRep'
  , zipPermIdxs
  , zipPerm
  , reverse
  )

import Cat.Sized.Diagonal.Class
  ( Diagonal ( DupObject
             , dup
             , dup'
             , (&&&)
             , fork
             )
  , DupObject'
  , (△)
  , dupRep
  , fork2
  , fork3
  )
import Cat.Sized.Semicartesian.Class
  ( Semicartesian ( ProjObject
                  , idx
                  )
  , index
  , π
  , ProjObject'
  , idxRep
  , FinRep (FinRep, unFinRep)
  , idxs
  , idxs'
  , HasTerminal (terminal)
  , Delete ( DelObject
           , del
           )
  , DelObject'
  , Select ( SelectObject
           , sel
           )
  , SelectObject'
  , unfork
  , head
  , tail
  , last
  , init
  , prefix
  , suffix
  , take
  , drop
  )

import Cat.Sized.Category.Instances      ()
import Cat.Sized.Monoidal.Instances      ()
import Cat.Sized.Braided.Instances       ()
import Cat.Sized.Diagonal.Instances      ()
import Cat.Sized.Semicartesian.Instances ()



class ( Monoidal      φ k
      , Braided       φ k
      , Diagonal      φ k
      , Semicartesian φ k
      )
      ⇒ Cartesian     φ k


instance (Cartesian φ k, Proxy φ k ~ Proxy φ (o `Sub` k))
  ⇒ Cartesian φ (o `Sub` k)
