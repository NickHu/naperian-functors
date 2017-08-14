{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : Data.Naperian.Conversions
Description : Naperian conversion functions
Copyright   : © Nick Hu, 2017
License     : BSD3
Maintainer  : Nick Hu <nick.hu@cs.ox.ac.uk>
Portability : unportable

This module provides some conversion functions between nested @Dimension@ types,
nested lists, and multidimensional @Hyper@ types.
-}

module Data.Naperian.Conversions where

import Data.Naperian
import GHC.Exts (IsList(..))
import GHC.Prim (proxy#, Proxy#)

-- | Converts nested IsList type its corresponding nested list type
-- @
--    :kind! Nest (Vector One (Vector Two Int)) = [[Int]]
-- @
type family Nest d where
  Nest (f a) = [Nest (Item (f a))]
  Nest a = a

-- | Returns a type-level Boolean indicating whether we're at the most nested
-- type
-- @
--    :kind! Atomic Int = 'True
--    :kind! Atomic (Vector One Int) = 'False
-- @
type family Atomic a where
  Atomic (f a) = 'False
  Atomic a = 'True

-- | Converts between nested IsList instances and nested lists
-- @
--    expand (x :: Vector One (Vector Two Int)) :: [[Int]]
--    contract (xss :: [[Int]]) :: Vector One (Vector Two Int)
-- @
class Expandable a where
  expand :: a -> Nest a
  contract :: Nest a -> a

class Expandable' (flag :: Bool) a where
  expand' :: Proxy# flag -> a -> Nest a
  contract' :: Proxy# flag -> Nest a -> a

instance (Atomic a ~ flag, Expandable' flag a) => Expandable a where
  expand = expand' (proxy# :: Proxy# flag)
  contract = contract' (proxy# :: Proxy# flag)

instance (IsList (f a), Expandable (Item (f a))) =>
         Expandable' 'False (f a) where
  expand' _ = fmap expand . toList
  contract' _ = GHC.Exts.fromList . fmap contract

instance (a ~ Nest a) => Expandable' 'True a where
  expand' _ = id
  contract' _ = id

-- Hyper conversions
-- | Expands a type to its fully formed Hyper type
-- @
--    :kind! ToHyper (Vector One (Vector Two Int))
--      = Hyper '[Vector Two, Vector One] Int
--    :kind! ToHyper (Hyper '[Vector One] (Pair Int))
--      = Hyper '[Pair, Vector One] Int
-- @
type family ToHyper h where
  ToHyper (Hyper fs (f a)) = ToHyper (Hyper (f ': fs) a)
  ToHyper (Hyper fs a) = Hyper fs a
  ToHyper a = ToHyper (Hyper '[] a) -- requires UndecidableInstances

data State
  = Base
  | FullHyper
  | MidHyper

type family HyperState a where
  HyperState (Hyper fs (f a)) = 'MidHyper
  HyperState (Hyper fs a) = 'FullHyper
  HyperState a = 'Base

class IsHyper' (flag :: State) a where
  toHyper' :: Proxy# flag -> a -> ToHyper a

-- | Adds Hyper structure
-- @
--    toHyper (x :: d3 (d2 (d1 a))) :: Hyper '[d1, d2, d3] a
-- @
class IsHyper a where
  toHyper :: a -> ToHyper a

instance (HyperState a ~ flag, IsHyper' flag a) => IsHyper a where
  toHyper = toHyper' (proxy# :: Proxy# flag)

instance (IsHyper (Hyper '[] a), ToHyper a ~ ToHyper (Hyper '[] a)) =>
         IsHyper' 'Base a where
  toHyper' _ = toHyper . Scalar

instance (Dimension f, Shapely fs, IsHyper (Hyper (f ': fs) a)) =>
         IsHyper' 'MidHyper (Hyper fs (f a)) where
  toHyper' _ = toHyper . Prism

instance (ToHyper (Hyper fs a) ~ Hyper fs a) =>
         IsHyper' 'FullHyper (Hyper fs a) where
  toHyper' _ = id

-- | Converts a Hyper type into nested dimensions
-- @
--    :kind! FromHyper (Hyper '[d1, d2, d3] a) = d3 (d2 (d1 a))
-- @
type family FromHyper h where
  FromHyper (Hyper '[] a) = a
  FromHyper (Hyper (f ': fs) a) = FromHyper (Hyper fs (f a))

-- | Removes Hyper structure
-- @
--    fromHyper (h :: Hyper '[d1, d2, d3] a) :: d3 (d2 (d1 a))
-- @
fromHyper :: Hyper fs a -> FromHyper (Hyper fs a)
fromHyper (Scalar x) = x
fromHyper (Prism x) = fromHyper x
