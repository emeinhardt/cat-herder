{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-- |

module Cat.Unsized.Category.Class
  ( Category (id)
    -- * Re-exports from "Cat.Unsized.Semigroupoid.Class"
  , Semigroupoid ( Object
                 , (.)
                 )
  , Object'
  , (>>>)
  , (<<<)
  , (∘)
  , (⊙)

  , Sub (Sub, unSub)
  , sub
  , unsub
  ) where

import Data.Kind (Type
                 )

import Cat.Unsized.Semigroupoid.Class
  ( Semigroupoid ((.))
  , Object
  , Object'
  , (>>>)
  , (<<<)
  , (∘)
  , (⊙)

  , Sub (Sub, unSub)
  , sub
  , unsub
  )



class (Semigroupoid k) ⇒ Category (k ∷ κ → κ → Type) where
  id ∷ ∀ (a ∷ κ).
      ( Object k a )
      ⇒ a `k` a
