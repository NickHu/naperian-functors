{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

{-|
Module      : Data.Naperian.Vector
Description : Naperian, statically sized Vector newtype of Data.Vector.Unboxed
Copyright   : © Nick Hu, 2017
License     : BSD3
Maintainer  : Nick Hu <nick.hu@cs.ox.ac.uk>
Portability : unportable

A newtype representing a statically sized unboxed vector, implementing the
Naperian typeclass.

Implemented with @Data.Vector.Unboxed@.
-}

module Data.Naperian.Vector.Unboxed where

import qualified Data.Foldable        as F
import           Data.Kind            (Type)
import           Data.Maybe           (fromJust, fromMaybe)
import           Data.MonoTraversable
import qualified Data.Vector.Unboxed  as V
import           GHC.Exts             (IsList (..))
import           GHC.Prim             (Proxy#, proxy#)
import           GHC.TypeLits

import           Data.MonoNaperian
import           Data.Naperian.Vector (Finite (..), finite)

newtype Vector (n :: Nat) a = Vector (V.Vector a)
  deriving (Eq, Show, Ord, MonoFunctor, MonoFoldable)

type instance Element (Vector n a) = a

instance V.Unbox a => MonoTraversable (Vector n a) where
  otraverse f (Vector v) = Vector <$> (otraverse f v)

tail :: V.Unbox a => Vector n a -> Vector (n - 1) a
tail (Vector v) = Vector $ V.tail v

zipWith :: (V.Unbox a, V.Unbox b, V.Unbox c) => (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWith f (Vector u) (Vector v) = Vector $ V.zipWith f u v

length :: forall n a. KnownNat n => Vector n a -> Int
length _ = fromIntegral $ natVal' (proxy# :: Proxy# n)

replicate :: forall n a. (KnownNat n, V.Unbox a) => a -> Vector n a
replicate x = Vector (V.replicate s x) where
  s = fromIntegral $ natVal' (proxy# :: Proxy# n) :: Int

index :: V.Unbox a => Vector n a -> Finite n -> a
index (Vector v) (Fin n) = (V.!) v n

maybeFromList :: forall n a. (KnownNat n, V.Unbox a) => [a] -> Maybe (Vector n a)
maybeFromList xs = if Prelude.length xs == s
                      then Just (Vector $ V.fromList xs)
                      else Nothing
  where s = fromIntegral (natVal' (proxy# :: Proxy# n)) :: Int

instance (KnownNat n, V.Unbox a) => MonoPointed (Vector n a) where
  opoint = Data.Naperian.Vector.Unboxed.replicate

instance (KnownNat n, V.Unbox a) => IsList (Vector n a) where
  type Item (Vector n a) = a
  fromList xs = fromMaybe (error "list cast to vector of wrong length") $ maybeFromList xs
  toList = otoList

instance (KnownNat n, V.Unbox a) => MonoNaperian (Vector n a) where
  type MonoLog (Vector n a) = Finite n
  olookup = index
  otabulate f = Vector $ V.generate s (f . fromJust . finite)
    where s = fromIntegral (natVal' (proxy# :: Proxy# n)) :: Int

instance (KnownNat n, V.Unbox a) => MonoDimension (Vector n a) where
  osize = Data.Naperian.Vector.Unboxed.length

