{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-dodgy-exports #-}
-- |

module Cat.Sized.Cocartesian.Class
  ( Cocartesian

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

    -- * Re-exports from "Cat.Sized.Codiagonal"
  , Codiagonal ( JamObject
               , jam
               , jam'
               )
  , JamObject'
  , (▽)
  , jamMon
  , jamMon'
  , JamMon (JamMon, unJamMon)

    -- * Re-exports from "Cat.Sized.Semicocartesian"
  , Semicocartesian ( InjObject
                    , inj
                    , inj'
                    )
  , InjObject'
  , injMon
  , InjMon (InjMon, unInjMon)

    -- * Re-exports from "Cat.Sized.Zero"
  , HasZero (pointer)
  ) where

import Data.Type.Equality (type (~))
import Data.Kind (Type)
import GHC.TypeNats (Nat)

import Cat.Sized.Semigroupoid.Class
  ( Sub
  )
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
  )
import Cat.Sized.Codiagonal.Class
  ( Codiagonal ( JamObject
               , jam
               , jam'
               )
  , JamObject'
  , (▽)
  , jamMon
  , jamMon'
  , JamMon (JamMon, unJamMon)
  )
import Cat.Sized.Semicocartesian.Class
  ( Semicocartesian ( InjObject
                    , inj
                    , inj'
                    )
  , InjObject'
  , injMon
  , InjMon (InjMon, unInjMon)
  )
import Cat.Sized.Zero.Class
  ( HasZero (pointer)
  )



class ( Braided         φ k
      , Codiagonal      φ k
      , Semicocartesian φ k
      )
  ⇒ Cocartesian (φ ∷ Nat → κ → κ) (k ∷ (Nat → κ → κ) → Nat → Nat → κ → κ → Type)

instance (Cocartesian φ k, Proxy φ k ~ Proxy φ (o `Sub` k)) ⇒ Cocartesian φ (o `Sub` k)
