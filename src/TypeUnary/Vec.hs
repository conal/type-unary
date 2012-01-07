{-# LANGUAGE TypeFamilies, EmptyDataDecls, TypeOperators
           , GADTs, KindSignatures
           , FlexibleInstances, FlexibleContexts
           , UndecidableInstances
           , ScopedTypeVariables, CPP
           , RankNTypes
           , MultiParamTypeClasses, FunctionalDependencies
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
    module TypeUnary.Nat
  -- * Vectors
  , Vec(..), headV, tailV, joinV, (<+>), indices
  , Vec0,Vec1,Vec2,Vec3,Vec4,Vec5,Vec6,Vec7,Vec8,Vec9
  , Vec10,Vec11,Vec12,Vec13,Vec14,Vec15,Vec16
  , vec1, vec2, vec3, vec4, vec5, vec6, vec7, vec8
  , un1, un2, un3, un4
  , get, get0, get1, get2, get3
  , update
  , set, set0, set1, set2, set3
  , getI, setI
  , swizzle, split, deleteV, elemsV
  , ToVec(..)
  ) where

import Prelude hiding (foldr,sum)

-- #include "Typeable.h"

import Data.Monoid (Monoid(..))
import Control.Applicative (Applicative(..),liftA2,(<$>))
import Data.Foldable (Foldable(..),toList,sum)
import Data.Traversable (Traversable(..))
-- import Data.Typeable

import Foreign.Storable
import Foreign.Ptr (Ptr,plusPtr,castPtr)

import Data.VectorSpace

import TypeUnary.Nat

{--------------------------------------------------------------------
    Vectors
--------------------------------------------------------------------}

infixr 5 :<

-- | Vectors with type-determined length, having empty vector ('ZVec') and
-- vector cons ('(:<)').
data Vec :: * -> * -> * where
  ZVec :: Vec Z a 
  (:<) :: a -> Vec n a -> Vec (S n) a

-- | Type-safe head for vectors
headV :: Vec (S n) a -> a
headV (a :< _) = a

-- | Type-safe tail for vectors
tailV :: Vec (S n) a -> Vec n a
tailV (_ :< as') = as'

-- TODO: when haddock is fixed, reinstate per-ctor haddock comments and
-- remove the constructor comments in the data doc.

-- INSTANCE_TYPEABLE2(Vec,vecTC ,"Vec")


-- instance Show a => Show (Vec n a) where
--   show ZVec = "ZVec"
--   show (a :< v) = show a ++ " :< " ++ show v

{-
-- | Enumerate the elements of a vector.  See also 'elemsV'
vElems :: Vec n a -> [a]
vElems ZVec      = []
vElems (a :< as) = a : vElems as
-}

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

-- 2011-10-26: There was an orphan Show Vec instance in shady-gen's
-- Shady.Language.Type, which conflicted with the Show instance above. To
-- do: check whether this change broke Shady's code generation. Maybe not,
-- if the code generation uses Pretty instead of Show.

-- The Monoid instance uses a standard recipe for applicative functors.
instance (IsNat n, Monoid a) => Monoid (Vec n a) where
  mempty  = pure mempty
  mappend = liftA2 mappend

instance Functor (Vec n) where
  fmap _ ZVec     = ZVec
  fmap f (a :< u) = f a :< fmap f u

instance IsNat n => Applicative (Vec n) where
  pure  = pureV
  (<*>) = applyV

pureV :: IsNat n => a -> Vec n a
pureV = pureV' nat

pureV' :: Nat n -> a -> Vec n a
pureV' Zero     _ = ZVec
pureV' (Succ n) a = a :< pureV' n a

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

instance IsNat n => Monad (Vec n) where
  return = pure
  v >>= f = joinV (f <$> v)

-- | Equivalent to monad @join@ for vectors
joinV :: Vec n (Vec n a) -> Vec n a
joinV ZVec = ZVec
joinV ((a :< _) :< vs) = a :< joinV (tailV <$> vs)

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

-- TODO: Rethink the previous three instances. Maybe replace the Num
-- constraints with AdditiveGroup, VectorSpace, and InnerSpace.
-- And why Vec1 for Scalar?

instance (IsNat n, Storable a) => Storable (Vec n a) where
   sizeOf    = const (fromIntegral (natToZ (nat :: Nat n))
                      * sizeOf (undefined :: a))
   alignment = const (alignment (undefined :: a))
   peek      = peekV . castPtr
   poke      = pokeV . castPtr


infixl 1 <+>
-- | Concatenation of vectors
(<+>) :: Vec m a -> Vec n a -> Vec (m :+: n) a
ZVec     <+> v = v
(a :< u) <+> v = a :< (u <+> v)


peekV :: (IsNat n, Storable a) => Ptr a -> IO (Vec n a)
peekV = peekV' nat

pokeV :: (IsNat n, Storable a) => Ptr a -> Vec n a -> IO ()
pokeV = pokeV' nat

peekV' :: Storable a => Nat n -> Ptr a -> IO (Vec n a)
peekV' Zero _ = return ZVec
peekV' (Succ n) p =  do a  <- peek p
                        as <- peekV' n (p `plusPtr` sizeOf a)
                        return (a :< as)

-- peekV' (Succ n) p = liftA2 (:<) (peek p) (peekV (succPtr p))
--                   = liftA2 (:<) peek (peekV (succPtr p))
-- 
-- peekV' (Succ _) = (liftA2.liftA2) (:<) peek (peekV . succPtr)

pokeV' :: Storable a => Nat n -> Ptr a -> Vec n a -> IO ()
pokeV' Zero     _ ZVec      = return ()
pokeV' (Succ n) p (a :< as) = do poke p a
                                 pokeV' n (p `plusPtr` sizeOf a) as

-- -- Experiment toward simplifying away the plusPtr calls.
-- succPtr :: forall a. Storable a => Ptr a -> Ptr a
-- succPtr p = p `plusPtr` sizeOf (undefined :: a)

-- TODO: Optimize peekV, pokeV.  For instance, unroll the loop in the
-- dictionary, remove the sizeOf dependence on @a@.

-- | Indices under @n@: 'index0' :< 'index1' :< ...
indices :: Nat n -> Vec n (Index n)
indices Zero     = ZVec
indices (Succ n) = index0 :< fmap succI (indices n)

-- TODO: Try reimplementing many Vec functions via foldr.  Warning: some
-- (most?) will fail because they rely on a polymorphic combining function.

-- Convert from vector to list via Data.Foldable.toList


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

vec5 :: a -> a -> a -> a -> a -> Vec5 a
vec5 a b c d e = a :< vec4 b c d e

vec6 :: a -> a -> a -> a -> a -> a -> Vec6 a
vec6 a b c d e f = a :< vec5 b c d e f

vec7 :: a -> a -> a -> a -> a -> a -> a -> Vec7 a
vec7 a b c d e f g = a :< vec6 b c d e f g

vec8 :: a -> a -> a -> a -> a -> a -> a -> a -> Vec8 a
vec8 a b c d e f g h = a :< vec7 b c d e f g h

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

-- TODO: consider this notation:
--
--   infixr 5 :<
--   (<|) :: a -> a -> Vec2 a
--   (<|) = vec2
-- 
-- So we can say things like
-- 
--   a :< b <| c

{--------------------------------------------------------------------
    Extract and set elements
--------------------------------------------------------------------}

-- | Extract a vector element, taking a proof that the index is within bounds.
get :: Index n -> Vec n a -> a
get (Index ZLess     Zero    ) (a :< _)  = a
get (Index (SLess p) (Succ m)) (_ :< as) = get (Index p m) as

get0 :: Vec (N1 :+: n) a -> a   -- ^ Get first  element
get1 :: Vec (N2 :+: n) a -> a   -- ^ Get second element
get2 :: Vec (N3 :+: n) a -> a   -- ^ Get third  element
get3 :: Vec (N4 :+: n) a -> a   -- ^ Get fourth element

get0 = get index0
get1 = get index1
get2 = get index2
get3 = get index3

-- | Update a vector element, taking a proof that the index is within bounds.
update :: Index n -> (a -> a) -> Vec n a -> Vec n a
update (Index ZLess     Zero    ) f (a :< as) = f a :< as
update (Index (SLess p) (Succ m)) f (a :< as) =   a :< update (Index p m) f as

-- | Replace a vector element, taking a proof that the index is within bounds.
set :: Index n -> a -> Vec n a -> Vec n a
set i a' = update i (const a')

set0 :: a -> Vec (N1 :+: n) a -> Vec (N1 :+: n) a   -- ^ Set first element
set1 :: a -> Vec (N2 :+: n) a -> Vec (N2 :+: n) a   -- ^ Set second element
set2 :: a -> Vec (N3 :+: n) a -> Vec (N3 :+: n) a   -- ^ Set third element
set3 :: a -> Vec (N4 :+: n) a -> Vec (N4 :+: n) a   -- ^ Set fourth element

set0 = set index0
set1 = set index1
set2 = set index2
set3 = set index3

-- | Variant of 'get' in which the index size is checked at run-time
-- instead of compile-time.
getI :: (IsNat n, Integral i) => i -> Vec n a -> a
getI = get . coerceToIndex

-- | Variant of 'set' in which the index size is checked at run-time
-- instead of compile-time.
setI :: (IsNat n, Integral i) => i -> a -> Vec n a -> Vec n a
setI = set . coerceToIndex


-- | Swizzling.  Extract multiple elements simultaneously.
swizzle :: Vec n (Index m) -> Vec m a -> Vec n a
swizzle ZVec        _ = ZVec
swizzle (ix :< ixs) v = get ix v :< swizzle ixs v

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

{-

-- Reversal. Thinking about this one. Currently thwarted by missing
-- knowledge about numbers in the type-checker. Would be easy with
-- built-in type-level naturals.

-- | Reverse a vector
reverseV :: Vec n a -> Vec n a
reverseV = reverse' nat ZVec

--  Couldn't match type `n' with `n :+: Z'

-- Reverse na and append to ma
reverse' :: Nat n -> Vec m a -> Vec n a -> Vec (n :+: m) a
reverse' Zero     ma ZVec      = ma
reverse' (Succ n) ma (a :< as) = reverse' n (a :< ma) as

-- Could not deduce ((n1 :+: S m) ~ S (n1 :+: m))
-}

-- | Delete exactly one occurrence of an element from a vector, raising an
-- error if the element isn't present.
deleteV :: Eq a => a -> Vec (S n) a -> Vec n a
deleteV b (a :< as) | a == b = as
deleteV _ (_ :< ZVec)        = error "deleteV: did not find element"
deleteV b (a :< as@(_:<_))   = a :< deleteV b as


-- | Convert a list into a vector. Error if the list is too short or too long
elemsV :: IsNat n => [a] -> Vec n a
elemsV = elemsV' nat

elemsV' :: Nat n -> [a] -> Vec n a
elemsV' Zero []           = ZVec
elemsV' Zero (_:_)        = error "elemsV: too many elements"
elemsV' (Succ _) []       = error "elemsV: too few elements"
elemsV' (Succ n) (a : as) = a :< elemsV' n as

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


{--------------------------------------------------------------------
    Conversion to vectors
--------------------------------------------------------------------}

class ToVec c n a where
  toVec :: c -> Vec n a

instance ToVec (Vec n a) n a where toVec = id

instance IsNat n => ToVec [a] n a where
  toVec = toVecL nat

toVecL :: Nat n -> [a] -> Vec n a
toVecL Zero [] = ZVec
toVecL (Succ m) (a:as) = a :< toVecL m as
toVecL _ _ = error "toVecL: length mismatch"

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

result :: (b -> b') -> ((a -> b) -> (a -> b'))
result = (.)
