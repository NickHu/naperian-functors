{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}

{-|
Module      : Data.Naperian.Pair
Description : Naperian Pair type
Copyright   : © Nick Hu, 2017
License     : BSD3
Maintainer  : Nick Hu <nick.hu@cs.ox.ac.uk>
Portability : unportable

This module serves as a simple example of how to define a Naperian datatype.

A @Pair@ has two positions, and can therefore be indexed by a @Bool@, which is a
type with exactly two inhabitants: @False@ and @True@. @False@ indexes the first
position and @True@ indexes the second position.
-}

module Data.Naperian.Pair where

import Data.Naperian

data Pair a = P a a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Pair where
  pure x = P x x
  P f g <*> P x y = P (f x) (g y)

instance Naperian Pair where
  type Log Pair = Bool
  lookup (P x _) False = x
  lookup (P _ y) True = y
  positions = P False True

instance Dimension Pair where size = const 2

