{-# LANGUAGE TypeFamilies, EmptyDataDecls, TypeOperators
           , GADTs, KindSignatures
           , FlexibleInstances, FlexibleContexts
           , UndecidableInstances
           , ScopedTypeVariables, CPP
           , RankNTypes
  #-}
{-# OPTIONS_GHC -Wall -fno-warn-incomplete-patterns #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeUnary.Vec
-- Copyright   :  (c) Conal Elliott 2009
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Experiment in length-typed vectors
----------------------------------------------------------------------

module TypeUnary.Vec
  (
  -- * Type-level numbers
    Z, S, (:+:)
  , N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16
  -- * Typed natural numbers
  , Nat(..), zero, one, two, three, four
  , withIsNat, natSucc, natIsNat
  , natToZ, natEq, natAdd, (:<:)
  , Index(..), succI, index0, index1, index2, index3
  -- * Vectors
  , Vec(..), IsNat(..), (<+>), indices
  , Vec0,Vec1,Vec2,Vec3,Vec4,Vec5,Vec6,Vec7,Vec8,Vec9
  , Vec10,Vec11,Vec12,Vec13,Vec14,Vec15,Vec16
  , vec1, vec2, vec3, vec4
  , un1, un2, un3, un4
  , get0, get1, get2, get3
  , get, swizzle, split
  ) where

import Prelude hiding (foldr,sum)

-- #include "Typeable.h"

import Control.Applicative (Applicative(..),liftA2,(<$>))
import Data.Foldable (Foldable(..),toList,sum)
import Data.Traversable (Traversable(..))
import Data.Maybe (isJust)
-- import Data.Typeable

import Foreign.Storable
import Foreign.Ptr (Ptr,plusPtr,castPtr)

import Control.Compose (result)

import Data.VectorSpace

import Data.Proof.EQ


{--------------------------------------------------------------------
    Type-level numbers
--------------------------------------------------------------------}

-- | Type-level representation of zero
data Z
-- | Type-level representation of successor
data S n

-- INSTANCE_TYPEABLE0(Z,zTC ,"Z")
-- INSTANCE_TYPEABLE1(S,sTC ,"S")

infixl 6 :+:

-- | Sum of type-level numbers
type family a :+: b

type instance Z   :+: b = b
type instance S a :+: b = S (a :+: b)

type N0  = Z
type N1  = S N0
type N2  = S N1
type N3  = S N2
type N4  = S N3
type N5  = S N4
type N6  = S N5
type N7  = S N6
type N8  = S N7
type N9  = S N8
type N10 = S N9
type N11 = S N10
type N12 = S N11
type N13 = S N12
type N14 = S N13
type N15 = S N14
type N16 = S N15

-- putStrLn $ unlines ["type N" ++ show (n+1) ++ " = S N" ++ show n | n <- [0..15]]

{--------------------------------------------------------------------
    Typed natural numbers
--------------------------------------------------------------------}

-- Natural numbers
data Nat :: * -> * where
  Zero :: Nat Z
  Succ :: IsNat n => Nat n -> Nat (S n)

instance Show (Nat n) where show = show . natToZ

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

-- | Interpret a 'Nat' as an 'Integer'
natToZ :: Nat n -> Integer
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


infix 4 :<:

-- | Proof that @m < n@
data m :<: n where
  ZLess :: Z :<: S n
  SLess :: m :<: n -> S m :<: S n

-- data Index :: * -> * where
--   Index :: (n :<: lim) -> Nat n -> Index lim

-- or

-- | A number under the given limit, with proof
data Index lim = forall n. IsNat n => Index (n :<: lim) (Nat n)

instance Eq (Index lim) where
  Index _ n == Index _ n' = isJust (n `natEq` n')

succI :: Index m -> Index (S m)
succI (Index p n) = Index (SLess p) (Succ n)

index0 :: Index (S m)
index0 = Index ZLess Zero

index1 :: Index (S (S m))
index1 = succI index0

index2 :: Index (S (S (S m)))
index2 = succI index1

index3 :: Index (S (S (S (S m))))
index3 = succI index2


{--------------------------------------------------------------------
    Vectors
--------------------------------------------------------------------}

infixr 5 :<

-- | Vectors with type-determined length, having empty vector ('ZVec') and
-- vector cons ('(:<)').
data Vec :: * -> * -> * where
  ZVec :: Vec Z a                       -- -- ^ zero vector
  (:<) :: a -> Vec n a -> Vec (S n) a   -- -- ^ vector cons

-- TODO: when haddock is fixed, reinstate per-ctor haddock comments and
-- remove the constructor comments in the data doc.

-- INSTANCE_TYPEABLE2(Vec,vecTC ,"Vec")


-- instance Show a => Show (Vec n a) where
--   show ZVec = "ZVec"
--   show (a :< v) = show a ++ " :< " ++ show v

-- | Enumerate the elements of a vector.  See also 'elemsV'
-- vElems :: Vec n a -> [a]
-- vElems ZVec      = []
-- vElems (a :< as) = a : vElems as

-- TODO: Add strictness annotations ("!") to (:<) arguments & compare

{-

{-# DEPRECATED vElems "Use Data.Foldable.toList instead" #-}
vElems :: Vec n a -> [a]
vElems = foldr (:) []

-}

{--------------------------------------------------------------------
    Instances for standard classes
--------------------------------------------------------------------}

instance Eq a => Eq (Vec n a) where
  ZVec    == ZVec    = True
  a :< as == b :< bs = a==b && as==bs

instance Ord a => Ord (Vec n a) where
  ZVec      `compare` ZVec      = EQ
  (a :< as) `compare` (b :< bs) =
    case a `compare` b of
      LT -> LT
      GT -> GT
      EQ -> as `compare` bs

instance Show a => Show (Vec n a) where
  show v = "elemsV " ++ show (toList v)

instance Functor (Vec n) where
  fmap _ ZVec     = ZVec
  fmap f (a :< u) = f a :< fmap f u

instance IsNat n => Applicative (Vec n) where
  pure  = pureV
  (<*>) = applyV

applyV :: Vec n (a -> b) -> Vec n a -> Vec n b
ZVec      `applyV` ZVec      = ZVec
(f :< fs) `applyV` (x :< xs) = f x :< (fs `applyV` xs)

-- Without -fno-warn-incomplete-patterns above,
-- the previous two instances lead to warnings about non-exhaustive
-- pattern matches, although the other possibilities
-- are type-incorrect.  According to SLPJ:
-- 
--   The overlap warning checker simply doesn't take account of GADTs.
--   There's a long-standing project suggestion to fix this:
--   http://hackage.haskell.org/trac/ghc/wiki/ProjectSuggestions .
--   Perhaps a good GSoc project.

instance Foldable (Vec n) where
  foldr _  b ZVec     = b
  foldr h b (a :< as) = a `h` foldr h b as

instance Traversable (Vec n) where
  traverse _ ZVec      = pure ZVec
  traverse f (a :< as) = liftA2 (:<) (f a) (traverse f as)

instance (IsNat n, Num a) => AdditiveGroup (Vec n a) where
  { zeroV = pure 0; (^+^) = liftA2 (+) ; negateV = fmap negate }

instance (IsNat n, Num a) => VectorSpace (Vec n a) where
  type Scalar (Vec n a) = Vec1 a
  (*^) (s :< ZVec) = fmap (s *)

instance (IsNat n, Num a) => InnerSpace (Vec n a) where
   -- u <.> v = vec1 (sum (liftA2 (*) u v))
   (<.>) = (result.result) (vec1 . sum) (liftA2 (*))

instance (IsNat n, Storable a) => Storable (Vec n a) where
   sizeOf    = const (fromIntegral (natToZ (nat :: Nat n))
                      * sizeOf (undefined :: a))
   alignment = const (alignment (undefined :: a))
   peek      = peekV . castPtr
   poke      = pokeV . castPtr

{--------------------------------------------------------------------
    IsNat
--------------------------------------------------------------------}

instance IsNat Z where
  nat          = Zero
  pureV _      = ZVec
  elemsV []    = ZVec
  elemsV (_:_) = error "elemsV: too many elements"
  peekV        = const (return ZVec)
  pokeV        = const (const (return ()))

instance IsNat n => IsNat (S n) where
  nat               = Succ nat
  pureV a           = a :< pureV a
  elemsV []         = error "elemsV: too few elements"
  elemsV (a : as)   = a :< elemsV as
  peekV p           =  do a  <- peek p
                          as <- peekV (p `plusPtr` sizeOf a)
                          return (a :< as)
                     -- liftA2 (:<) (peek p) (peekV (succPtr p))
  -- peekV = (liftA2.liftA2) (:<) peek (peekV . succPtr)
  -- TODO: Try these niftier peekV definitions
  pokeV p (a :< as) = do poke p a
                         pokeV (p `plusPtr` sizeOf a) as

-- -- Experiment toward simplifying away the plusPtr calls.
-- succPtr :: forall a. Storable a => Ptr a -> Ptr a
-- succPtr p = p `plusPtr` sizeOf (undefined :: a)

-- TODO: Optimize peekV, pokeV.  For instance, unroll the loop in the
-- dictionary, remove the sizeOf dependence on @a@.

infixl 1 <+>
-- | Concatenation of vectors
(<+>) :: Vec m a -> Vec n a -> Vec (m :+: n) a
ZVec     <+> v = v
(a :< u) <+> v = a :< (u <+> v)

-- | Indices under @n@: 'index0' :< 'index1' :< ...
indices :: Nat n -> Vec n (Index n)
indices Zero     = ZVec
indices (Succ n) = index0 :< fmap succI (indices n)

-- TODO: Try reimplementing many Vec functions via foldr.  Warning: some
-- (most?) will fail because they rely on a polymorphic combining function.

-- | @n@ a vector length.
class {- Typeable n => -} IsNat n where
  nat    :: Nat n
  pureV  :: a   -> Vec n a
  elemsV :: [a] -> Vec n a
  peekV  :: Storable a => Ptr a -> IO (Vec n a)
  pokeV  :: Storable a => Ptr a -> Vec n a -> IO ()

-- Convert from vector to list via Data.Foldable.toList

{-
-- TODO: remove all but nat from the class. Define the rest outside of the
-- class by using nat. Then break this module into Nat and Vec. For instance,

pureV :: IsNat n => a -> Vec n a
pureV = pureN nat

pureN :: Nat n -> a -> Vec n a
pureN Zero     _ = ZVec
pureN (Succ n) a = a :< pureN n a
-}

-- Convenient nicknames

type Vec0  = Vec N0
type Vec1  = Vec N1
type Vec2  = Vec N2
type Vec3  = Vec N3
type Vec4  = Vec N4
type Vec5  = Vec N5
type Vec6  = Vec N6
type Vec7  = Vec N7
type Vec8  = Vec N8
type Vec9  = Vec N9
type Vec10 = Vec N10
type Vec11 = Vec N11
type Vec12 = Vec N12
type Vec13 = Vec N13
type Vec14 = Vec N14
type Vec15 = Vec N15
type Vec16 = Vec N16

-- putStr $ unlines ["type Vec" ++ show n ++ " = Vec N" ++ show n | n <- [0..16]]

vec1 :: a -> Vec1 a
vec1 a = a :< ZVec

vec2 :: a -> a -> Vec2 a
vec2 a b = a :< vec1 b

vec3 :: a -> a -> a -> Vec3 a
vec3 a b c = a :< vec2 b c

vec4 :: a -> a -> a -> a -> Vec4 a
vec4 a b c d = a :< vec3 b c d

-- | Extract element
un1 :: Vec1 a -> a
un1 (a :< ZVec) = a

-- | Extract elements
un2 :: Vec2 a -> (a,a)
un2 (a :< b :< ZVec) = (a,b)

-- | Extract elements
un3 :: Vec3 a -> (a,a,a)
un3 (a :< b :< c :< ZVec) = (a,b,c)

-- | Extract elements
un4 :: Vec4 a -> (a,a,a,a)
un4 (a :< b :< c :< d :< ZVec) = (a,b,c,d)

{--------------------------------------------------------------------
    Extract elements
--------------------------------------------------------------------}

-- | General indexing, taking a proof that the index is within bounds.
get :: Index n -> Vec n a -> Vec1 a
get (Index ZLess     Zero    ) (a :< _)  = vec1 a
get (Index (SLess p) (Succ m)) (_ :< as) = get (Index p m) as


get0 :: Vec (S n)             a -> Vec1 a
get1 :: Vec (S (S n))         a -> Vec1 a
get2 :: Vec (S (S (S n)))     a -> Vec1 a
get3 :: Vec (S (S (S (S n)))) a -> Vec1 a

get0 = get index0
get1 = get index1
get2 = get index2
get3 = get index3


-- | Swizzling.  Extract multiple elements simultaneously.
swizzle :: Vec n (Index m) -> Vec m a -> Vec n a
swizzle ZVec        _ = ZVec
swizzle (ix :< ixs) v = un1 (get ix v) :< swizzle ixs v

{-
-- 'a' :< 'b' :< 'c' :< ZVec
t1 :: Three Char
t1 = elemsV "abc"
     -- 'a' :< 'b' :< 'c' :< ZVec

t2 :: Four (Index N3)
t2 = elemsV [index2, index0 ,index1, index2]

-- 'c' :< 'a' :< 'b' :< 'c' :< ZVec
t3 :: Four Char
t3 = swizzle t2 t1
-}

-- | Split a vector
split :: IsNat n => Vec (n :+: m) a -> (Vec n a, Vec m a)
split = split' nat

split' :: Nat n -> Vec (n :+: m) a -> (Vec n a, Vec m a)
split' Zero v             = (ZVec, v)
split' (Succ n) (a :< as) = (a :< bs, cs)
 where
   (bs,cs) = split' n as

-- For instance,
-- 
--   *TypeUnary.Vec> split (pure 3) :: (Vec7 Int, Vec4 Int)
--   (elemsV [3,3,3,3,3,3,3],elemsV [3,3,3,3])
-- 
-- Note that 'pure 3' was inferred to have type 'Vec11 Int'.

-- I'd like to define take & drop similarly, e.g.,
--
--   take :: IsNat n => Vec (n :+: m) a -> Vec n a
--   take = fst . split
-- 
-- However,
-- 
--   Could not deduce ((n :+: m0) ~ (n :+: m))
--   from the context (IsNat n)
--     bound by the type signature for
--                TypeUnary.Vec.take :: IsNat n => Vec (n :+: m) a -> Vec n a
--     at /Users/conal/Haskell/type-unary/src/TypeUnary/Vec.hs:488:1-18
--   NB: `:+:' is a type function, and may not be injective
