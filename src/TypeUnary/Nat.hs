{-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeUnary.Nat
-- Copyright   :  (c) Conal Elliott 2009-2012
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Experiment in length-typed vectors
----------------------------------------------------------------------

module TypeUnary.Nat
  (
    module TypeUnary.TyNat
  -- * Value-typed natural numbers
  , Nat(..), zero, one, two, three, four
  , withIsNat, natSucc, natIsNat
  , natToZ, natEq, natAdd, natMul
  , IsNat(..)
  -- * Inequality proofs and indices
  , (:<:)(..), Index(..), succI, index0, index1, index2, index3
  , coerceToIndex
  ) where

import Prelude hiding (foldr,sum)

-- #include "Typeable.h"

import Control.Applicative ((<$>))
import Data.Maybe (isJust)

import Data.Proof.EQ

import TypeUnary.TyNat

-- Natural numbers in unary form, built from zero & successor
data Nat :: * -> * where
  Zero :: Nat Z
  Succ :: IsNat n => Nat n -> Nat (S n)

instance Show (Nat n) where
  show n = show (natToZ n :: Integer)

withIsNat :: (IsNat n => Nat n -> a) -> (Nat n -> a)
withIsNat p Zero     = p Zero
withIsNat p (Succ n) = p (Succ n)

-- Helper for when we don't have a convenient proof of IsNat n.
natSucc :: Nat n -> Nat (S n)
natSucc = withIsNat Succ 

natIsNat :: Nat n -> (IsNat n => Nat n)
natIsNat Zero     = Zero
natIsNat (Succ n) = Succ n

{-

-- Another approach (also works):

data NatIsNat :: * -> * where
  NatIsNat :: IsNat n' => Nat n' -> (n :=: n') -> NatIsNat n

natIsNat' :: Nat n -> NatIsNat n
natIsNat' Zero     = NatIsNat Zero Refl
natIsNat' (Succ n) = NatIsNat (Succ n) Refl

withIsNat' :: (IsNat n => Nat n -> a) -> (Nat n -> a)
withIsNat' p n = case natIsNat' n of
                   NatIsNat n' Refl -> p n'
-}

-- | Interpret a 'Nat' as a plain number
natToZ :: (Enum a, Num a) => Nat n -> a
natToZ Zero     = 0
natToZ (Succ n) = (succ . natToZ) n

-- | Equality test
natEq :: Nat m -> Nat n -> Maybe (m :=: n)
Zero   `natEq` Zero   = Just Refl
Succ m `natEq` Succ n = liftEq <$> (m `natEq` n)
_      `natEq` _      = Nothing

-- | Sum of naturals
natAdd :: Nat m -> Nat n -> Nat (m :+: n)
Zero   `natAdd` n = n
Succ m `natAdd` n = natSucc (m `natAdd` n)

-- | Product of naturals
natMul :: forall m n. Nat m -> Nat n -> Nat (m :*: n)
Zero   `natMul` _ = Zero
Succ m `natMul` n = n `natAdd` (m `natMul` n)

zero :: Nat N0
zero = Zero

one :: Nat N1
one = Succ zero

two :: Nat N2
two = Succ one

three :: Nat N3
three = Succ two

four :: Nat N4
four = Succ three

-- TODO: Consider whether we really want definitions like natAdd, natMul,
-- and zero, ..., four, considering that all of them can be synthesized
-- from IsNat.

infix 4 :<:

-- | Proof that @m < n@
data m :<: n where
  ZLess :: Z :<: S n
  SLess :: m :<: n -> S m :<: S n

-- | A number under the given limit, with proof
data Index lim = forall n. IsNat n => Index (n :<: lim) (Nat n)

-- Equivalently,
-- 
--   data Index :: * -> * where
--     Index :: (n :<: lim) -> Nat n -> Index lim

-- TODO: Consider removing the Nat n field, since it's computable from
-- IsNat n or n :<: lim.

instance Eq (Index lim) where
  Index _ n == Index _ n' = isJust (n `natEq` n')

succI :: Index m -> Index (S m)
succI (Index p n) = Index (SLess p) (Succ n)

index0 :: Index (N1 :+: m)
index0 = Index ZLess Zero

index1 :: Index (N2 :+: m)
index1 = succI index0

index2 :: Index (N3 :+: m)
index2 = succI index1

index3 :: Index (N4 :+: m)
index3 = succI index2

-- | Index generation from integer. Can fail dynamically if the integer is
-- too large.
coerceToIndex :: (Show i, Integral i, IsNat m) => i -> Index m
coerceToIndex = coerceToIndex' nat

coerceToIndex' :: (Show i, Integral i) => Nat m -> i -> Index m
coerceToIndex' mOrig niOrig = loop mOrig niOrig
 where
   loop :: (Show i, Integral i) => Nat m -> i -> Index m
   loop Zero _        = error $ "coerceToIndex: out of bounds: "
                                ++ show niOrig ++ " should be less than "
                                ++ show mOrig
   loop (Succ _)   0  = Index ZLess Zero
   loop (Succ m') ni' = succI (loop m' (ni'-1))

{--------------------------------------------------------------------
    IsNat
--------------------------------------------------------------------}

-- | Is @n@ a natural number type?
class IsNat n where nat :: Nat n

instance            IsNat Z     where nat = Zero
instance IsNat n => IsNat (S n) where nat = Succ nat
