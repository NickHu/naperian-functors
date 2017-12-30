{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-|
Module      : Data.Naperian.Vector
Description : Naperian, statically sized Vector newtype of Data.Vector
Copyright   : © Nick Hu, 2017
                Austin Seipp, 2017
License     : BSD3
Maintainer  : Nick Hu <nick.hu@cs.ox.ac.uk>
Portability : unportable

A newtype representing a statically sized vector, implementing the Naperian
typeclass.

Implemented with @Data.Vector@.
-}

module Data.Naperian.Vector where

import qualified Data.Foldable as F
import           Data.Kind     (Type)
import           Data.Maybe    (fromMaybe)
import qualified Data.Vector   as V
import           GHC.Exts      (IsList (..))
import           GHC.Prim      (Proxy#, proxy#)
import           GHC.TypeLits

import           Data.Naperian

newtype Vector (n :: Nat) a = Vector (V.Vector a)
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

-- | The finite set of type-bounded Naturals. A value of type @'Fin' n@ has
-- exactly @n@ inhabitants, the natural numbers from @[0..n-1]@.
data Finite :: Nat -> Type where
  Fin :: Int -> Finite n
  deriving (Eq, Show)

-- | Create a type-bounded finite number @'Fin' n@ from a runtime integer,
-- bounded to a statically known limit. If the input value @x > n@, then
-- @'Nothing'@ is returned. Otherwise, returns @'Just' (x :: 'Fin' n)@.
finite :: forall n. KnownNat n => Int -> Maybe (Finite n)
finite x = if x > y then Nothing else Just (Fin x)
  where y = fromIntegral (natVal' (proxy# :: Proxy# n))

cons :: a -> Vector n a -> Vector (n + 1) a
cons x (Vector v) = Vector $ V.cons x v

snoc :: Vector n a -> a -> Vector (n + 1) a
snoc (Vector v) x = Vector $ V.snoc v x

(++) :: Vector m a -> Vector m a -> Vector (m + n) a
(++) (Vector u) (Vector v) = Vector $ (V.++) u v

concat :: Vector m (Vector n a) -> Vector (m * n) a
concat (Vector u) = Vector $ V.concat (map unvector $ V.toList u)
  where unvector :: Vector n a -> V.Vector a
        unvector (Vector v) = v

generate :: forall n a. KnownNat n => (Int -> a) -> Vector n a
generate f = Vector $ V.generate s f
  where s = fromIntegral $ natVal' (proxy# :: Proxy# n) :: Int

tail :: Vector n a -> Vector (n - 1) a
tail (Vector v) = Vector $ V.tail v

zipWith :: (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWith f (Vector u) (Vector v) = Vector $ V.zipWith f u v

length :: forall n a. KnownNat n => Vector n a -> Int
length _ = fromIntegral $ natVal' (proxy# :: Proxy# n)

replicate :: forall n a. KnownNat n => a -> Vector n a
replicate x = Vector (V.replicate s x) where
  s = fromIntegral $ natVal' (proxy# :: Proxy# n) :: Int

index :: Vector n a -> Finite n -> a
index (Vector v) (Fin n) = (V.!) v n

iota :: forall n. KnownNat n => Vector n (Finite n)
iota = Vector (fmap Fin (V.enumFromN 0 s)) where
  s = fromIntegral (natVal' (proxy# :: Proxy# n)) :: Int

maybeFromList :: forall n a. KnownNat n => [a] -> Maybe (Vector n a)
maybeFromList xs = if Prelude.length xs == s
                      then Just (Vector $ V.fromList xs)
                      else Nothing
  where s = fromIntegral (natVal' (proxy# :: Proxy# n)) :: Int

instance KnownNat n => Applicative (Vector n) where
  pure = Data.Naperian.Vector.replicate
  (<*>) = Data.Naperian.Vector.zipWith ($)

instance KnownNat n => IsList (Vector n a) where
  type Item (Vector n a) = a
  fromList xs = fromMaybe (error "list cast to vector of wrong length") $ maybeFromList xs
  toList = F.toList

instance KnownNat n => Naperian (Vector n) where
  type Log (Vector n) = Finite n
  lookup = index
  positions = iota

instance KnownNat n => Dimension (Vector n) where
  size = Data.Naperian.Vector.length

