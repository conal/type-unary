{-# LANGUAGE TypeFamilies, EmptyDataDecls, TypeOperators
           , GADTs, KindSignatures, TupleSections
           , FlexibleInstances, FlexibleContexts
           , UndecidableInstances
           , ScopedTypeVariables, CPP
           , RankNTypes
           , MultiParamTypeClasses, FunctionalDependencies
           , DeriveDataTypeable
  #-}
{-# OPTIONS_GHC -Wall #-}

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
  , Vec(..), unConsV, headV, tailV, joinV, (<+>), indices, iota
  , Vec0,Vec1,Vec2,Vec3,Vec4,Vec5,Vec6,Vec7,Vec8,Vec9
  , Vec10,Vec11,Vec12,Vec13,Vec14,Vec15,Vec16
  , vec1, vec2, vec3, vec4, vec5, vec6, vec7, vec8
  , un1, un2, un3, un4
  , get, get0, get1, get2, get3
  , update
  , set, set0, set1, set2, set3
  , getI, setI
  , flattenV, chunkV, swizzle, split, deleteV, elemsV
  , zipV , zipWithV , unzipV
  , zipV3, zipWithV3, unzipV3
  , transpose, cross
  , ToVec(..)
  ) where

  -- TODO: Consider dropping "V" suffix from several of the names.

import Prelude hiding (foldr,sum,and)

import Data.Monoid (Monoid(..),(<>))
import Control.Applicative (Applicative(..),liftA2,(<$>))
import Data.Foldable (Foldable(..),toList,sum) -- ,and
import Data.Traversable (Traversable(..))
import Data.Typeable (Typeable)

import Foreign.Storable
import Foreign.Ptr (Ptr,plusPtr,castPtr)

import Control.Newtype (Newtype(..))

-- import Data.Constraint

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
 deriving Typeable

-- | Type-safe un-cons for vectors
unConsV :: Vec (S n) a -> (a, Vec n a)
unConsV (a :< as) = (a,as)

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

cant :: String -> a
cant str = error $ str ++ ": GHC doesn't know this case can't happen."

cantV :: String -> a
cantV str = cant (str ++ " on Vec")

{--------------------------------------------------------------------
    Instances for standard classes
--------------------------------------------------------------------}

instance Eq a => Eq (Vec n a) where
  ZVec    == ZVec    = True
  a :< as == b :< bs = a==b && as==bs
  _ == _ = cantV "(==)"

instance Ord a => Ord (Vec n a) where
  ZVec      `compare` ZVec      = EQ
  (a :< as) `compare` (b :< bs) =
    (a `compare` b) `mappend` (as `compare` bs)
  _ `compare` _ = cantV "compare"

-- Equivalently,
-- 
--   (a :< as) `compare` (b :< bs) =
--     case a `compare` b of
--       LT -> LT
--       GT -> GT
--       EQ -> as `compare` bs

-- Some alternatives:
-- 
--   (==*) :: (IsNat n, Eq a) => Vec n a -> Vec n a -> Bool
--   (==*) = (fmap.fmap) and (liftA2 (==))
--   
--   -- as ==* bs = and (liftA2 (==) as bs)
--   
--   compare' :: (IsNat n, Ord a) => Vec n a -> Vec n a -> Ordering
--   compare' = (fmap.fmap) fold (liftA2 compare)

-- instance Show (Vec Z a) where
--   show _ = "ZVec"

-- instance Show a => Show (Vec (S n) a) where
--   show v = "elemsV " ++ show (toList v)

instance Show a => Show (Vec n a) where
  show v = "elemsV " ++ show (toList v)

-- 2011-10-26: There was an orphan Show Vec instance in shady-gen's
-- Shady.Language.Type, which conflicted with the Show instance above. To
-- do: check whether this change broke Shady's code generation. Maybe not,
-- if the code generation uses Pretty instead of Show.

-- The Monoid instance uses a standard recipe for applicative functors.

#if MIN_VERSION_base(4,11,0)
instance (IsNat n, Semigroup a) => Semigroup (Vec n a) where
    (<>) = liftA2 (<>)
#endif

instance (IsNat n, Monoid a) => Monoid (Vec n a) where
  mempty  = pure mempty
  mappend = liftA2 mappend

instance Functor (Vec n) where
  fmap _ ZVec     = ZVec
  fmap f (a :< u) = f a :< fmap f u
  {-# INLINE fmap #-}

instance IsNat n => Applicative (Vec n) where
  pure  = pureV nat
  (<*>) = applyV nat
  {-# INLINE pure  #-}
  {-# INLINE (<*>) #-}

pureV :: Nat n -> a -> Vec n a
pureV Zero     _ = ZVec
pureV (Succ n) a = a :< pureV n a
{-# INLINE pureV #-}

-- Experiment

inVecS :: ((a, Vec n a) -> (b, Vec n b)) -> (Vec (S n) a -> Vec (S n) b)
inVecS f = uncurry (:<) . f . unConsV

inVecS2 :: ((a, Vec n a) -> (b, Vec n b) -> (c, Vec n c))
        -> (Vec (S n) a  -> Vec (S n) b  -> Vec (S n) c )
inVecS2 f = inVecS . f . unConsV

-- TODO: reconcile unConsV vs unVecS

applyV :: Nat n -> Vec n (a -> b) -> Vec n a -> Vec n b
applyV Zero     = \ _      _      -> ZVec
applyV (Succ n) = inVecS2 (\ (f,fs) (x,xs) -> (f x , applyV n fs xs))
{-# INLINE applyV #-}

-- applyV :: Nat n -> Vec n (a -> b) -> Vec n a -> Vec n b
-- applyV Zero     = \ ZVec      ZVec      -> ZVec
-- applyV (Succ n) = \ (f :< fs) (x :< xs) -> f x :< applyV n fs xs
-- {-# INLINE applyV #-}

-- The "= \ ..." form here side-steps the incomplete patterns warning without
-- -fno-warn-incomplete-patterns above. Otherwise we get warnings about
-- non-exhaustive pattern matches, although the other possibilities are
-- type-incorrect. Once upon a time SLPJ said
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
joinV _ = cant "joinV"

instance Foldable (Vec n) where
  foldMap _ ZVec      = mempty
  foldMap h (a :< as) = h a <> foldMap h as
  {-# INLINE foldMap #-}

instance Traversable (Vec n) where
  traverse _ ZVec      = pure ZVec
  traverse f (a :< as) = liftA2 (:<) (f a) (traverse f as)
  {-# INLINE traverse #-}

instance Newtype (Vec Z a) () where
  pack () = ZVec
  unpack ZVec = ()

instance Newtype (Vec (S n) a) (a,Vec n a) where
  pack = uncurry (:<)
  unpack = unConsV

instance (IsNat n, Num a) => AdditiveGroup (Vec n a) where
  { zeroV = pure 0; (^+^) = liftA2 (+) ; negateV = fmap negate }

instance (IsNat n, Num a) => VectorSpace (Vec n a) where
  type Scalar (Vec n a) = Vec1 a
  (*^) (s :< ZVec) = fmap (s *)
  (*^) _ = cantV "(*^)"

instance (IsNat n, Num a) => InnerSpace (Vec n a) where
   -- u <.> v = vec1 (sum (liftA2 (*) u v))
   (<.>) = (result.result) (vec1 . sum) (liftA2 (*))

-- TODO: Rethink the previous three instances. Maybe replace the Num
-- constraints with AdditiveGroup, VectorSpace, and InnerSpace.
-- And why Vec1 for Scalar?

instance (IsNat n, Storable a) => Storable (Vec n a) where
   sizeOf    = const ((natToZ (nat :: Nat n))
                      * sizeOf (undefined :: a))
   alignment = const (alignment (undefined :: a))
   peek      = peekV . castPtr
   poke      = pokeV . castPtr


infixl 1 <+>
-- | Concatenation of vectors
(<+>) :: Vec m a -> Vec n a -> Vec (m :+: n) a
ZVec     <+> v = v
(a :< u) <+> v = a :< (u <+> v)
{-# INLINE (<+>) #-}

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
pokeV' _ _ _ = cant "pokeV"

-- -- Experiment toward simplifying away the plusPtr calls.
-- succPtr :: forall a. Storable a => Ptr a -> Ptr a
-- succPtr p = p `plusPtr` sizeOf (undefined :: a)

-- TODO: Optimize peekV, pokeV.  For instance, unroll the loop in the
-- dictionary, remove the sizeOf dependence on @a@.

-- | Indices under @n@: 'index0' :< 'index1' :< ...
indices :: IsNat n => Vec n (Index n)
indices = indices' nat

-- Variant of 'indices' with explicit argument.
indices' :: Nat n -> Vec n (Index n)
indices' Zero     = ZVec
indices' (Succ n) = index0 :< fmap succI (indices' n)

-- TODO: Try reimplementing many Vec functions via foldr.  Warning: some
-- (most?) will fail because they rely on a polymorphic combining function.

-- Convert from vector to list via Data.Foldable.toList

-- | Vector of ints from 0 to n-1. Named for APL iota operation (but 0 based).
iota :: (IsNat n, Num a, Enum a) => Vec n a
iota = unIndex <$> indices


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
un1 _ = cant "un1"

-- | Extract elements
un2 :: Vec2 a -> (a,a)
un2 (a :< b :< ZVec) = (a,b)
un2 _ = cant "un2"

-- | Extract elements
un3 :: Vec3 a -> (a,a,a)
un3 (a :< b :< c :< ZVec) = (a,b,c)
un3 _ = cant "un3"

-- | Extract elements
un4 :: Vec4 a -> (a,a,a,a)
un4 (a :< b :< c :< d :< ZVec) = (a,b,c,d)
un4 _ = cant "un4"

-- TODO: consider this notation:
--
--   infixr 5 <|
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
get _ _ = cant "get"

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
update _ _ _ = cantV "update"

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
getI :: (IsNat n, Show i, Integral i) => i -> Vec n a -> a
getI = get . coerceToIndex

-- | Variant of 'set' in which the index size is checked at run-time
-- instead of compile-time.
setI :: (IsNat n, Show i, Integral i) => i -> a -> Vec n a -> Vec n a
setI = set . coerceToIndex

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- | Flatten a vector of vectors (a 2D array) into a vector
flattenV :: IsNat n => Vec n (Vec m a) -> Vec (n :*: m) a
flattenV = flattenV' nat

flattenV' :: Nat n -> Vec n (Vec m a) -> Vec (n :*: m) a
flattenV' Zero _               = ZVec
flattenV' (Succ n') (v :< vs') = v <+> flattenV' n' vs'
flattenV' _ _ = error "flattenV': GHC doesn't know this case can't happen."

-- | Chunk a vector into a vector of vectors (a 2D array)
chunkV :: (IsNat n, IsNat m) => Vec (n :*: m) a -> Vec n (Vec m a)
chunkV = chunkV' nat

chunkV' :: IsNat m => Nat n -> Vec (n :*: m) a -> Vec n (Vec m a)
chunkV' Zero     ZVec = ZVec
chunkV' (Succ n) as   = v :< chunkV' n as' where (v,as') = split as
chunkV' _ _ = cant "chunkV"

-- | Swizzling.  Extract multiple elements simultaneously.
swizzle :: Vec n (Index m) -> Vec m a -> Vec n a
swizzle is v = flip get v <$> is

-- swizzle ZVec        _ = ZVec
-- swizzle (ix :< ixs) v = get ix v :< swizzle ixs v

-- swizzle = flip (fmap . flip get)

-- | Split a vector
split :: IsNat n => Vec (n :+: m) a -> (Vec n a, Vec m a)
split = split' nat

split' :: Nat n -> Vec (n :+: m) a -> (Vec n a, Vec m a)
split' Zero v             = (ZVec, v)
split' (Succ n) (a :< as) = (a :< bs, cs)
 where
   (bs,cs) = split' n as
split' _ _ = cantV "split"

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


-- Alternatively:

{-
take :: forall m n a. (IsNat n, IsNat m) => Vec (n :+: m) a -> Vec n a
take = take' (nat :: Nat n) (nat :: Nat m)

take' :: Nat n -> Nat m -> Vec (n :+: m) a -> Vec n a
take' Zero _ _             = ZVec
take' (Succ n) m (a :< as) = a :< take' n m as
-}

-- I think it'd be hard to use take. I guess we'd have to subtract in the type
-- system.

{-

take :: forall m n a. (IsNat n, IsNat m) =>
        Vec (n :+: m) a -> (Vec n a,Nat m)
take = take' (nat :: Nat n)

take' :: Nat n -> Vec (n :+: m) a -> (Vec n a,Nat m)
take' Zero as             = (ZVec,lengthV as)
take' (Succ n) (a :< as) = (a :< as', m)
 where
   (as',m) = take' n as

lengthV :: Vec n a -> Nat n
lengthV ZVec      = Zero
lengthV (a :< as) = Succ (lengthV as)

--     Could not deduce (IsNat n1) arising from a use of `Succ'
--     from the context (n ~ S n1)

-}

-- resplit :: (Vec m a, Vec n a) -> (Vec n a, Vec m a)
-- resplit (u,v) = split (u <+> v)
-- 
-- Won't type-check without commutativity of addition. :(

#if 0

addZ :: IsNat n => Dict (n ~ (n :+: Z))
addZ = addZ' nat

addZ' :: Nat n -> Dict (n ~ (n :+: Z))
addZ' Zero                       = Dict
addZ' (Succ m) | Dict <- addZ' m = Dict

add1 :: IsNat m => Dict ((m :+: S Z) ~ S m)
add1 = add1' nat

add1' :: Nat m -> Dict ((m :+: S Z) ~ S m)
add1' Zero                       = Dict
add1' (Succ m) | Dict <- add1' m = Dict

-- addS :: (IsNat m, IsNat n) => Dict ((m :+: S n) ~ S (m :+: n))
-- addS = addS' nat

addS' :: IsNat m => Nat n -> Dict ((m :+: S n) ~ S (m :+: n))
addS' Zero | Dict <- add1 = Dict
...

-- Oops: non-injectivity

-- Reversal. Thinking about this one. Currently thwarted by missing
-- knowledge about numbers in the type-checker. Would be easy with
-- built-in type-level naturals.

-- | Reverse a vector
reverseV :: forall n a. IsNat n => Vec n a -> Vec n a
reverseV | Dict <- (addZ :: Dict (n ~ (n :+: Z))) = reverse' nat ZVec

-- reverseV :: Vec n a -> Vec n a
-- reverseV = reverse' nat ZVec

--  Couldn't match type `n' with `n :+: Z'

-- Reverse na and append to ma
reverse' :: Nat n -> Vec m a -> Vec n a -> Vec (n :+: m) a
reverse' Zero     ma ZVec      = ma
reverse' (Succ n) ma (a :< as) = reverse' n (a :< ma) as

-- Could not deduce ((n1 :+: S m) ~ S (n1 :+: m))
#endif

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

-- | Zip two vectors into one. Like @'liftA2' '(,)'@, but the former requires
-- @IsNat n@.
zipV :: Vec n a -> Vec n b -> Vec n (a,b)
zipV = zipWithV (,)

-- | Zip three vectors into one. Like @'liftA3' '(,)'@, but the former requires
-- @IsNat n@.
zipV3 :: Vec n a -> Vec n b -> Vec n c -> Vec n (a,b,c)
zipV3 = zipWithV3 (,,)

-- | Unzip one vector into two. Like 'liftA2', but the former requires
-- @IsNat n@.
zipWithV :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWithV _ ZVec      ZVec      = ZVec
zipWithV f (a :< as) (b :< bs) = f a b :< zipWithV f as bs
zipWithV _ _ _ = cant "zipWithV"

-- | Unzip one vector into two. Like 'liftA2', but the former requires
-- @IsNat n@.
zipWithV3 :: (a -> b -> c -> d) -> Vec n a -> Vec n b -> Vec n c -> Vec n d
zipWithV3 _ ZVec      ZVec      ZVec      = ZVec
zipWithV3 f (a :< as) (b :< bs) (c :< cs) = f a b c :< zipWithV3 f as bs cs
zipWithV3 _ _ _ _ = cant "zipWithV3"

-- | Unzip a vector of pairs into a pair of vectors
unzipV :: Vec n (a,b) -> (Vec n a, Vec n b)
unzipV ZVec = (ZVec,ZVec)
unzipV ((a,b) :< ps) = (a :< as, b :< bs) where (as,bs) = unzipV ps

-- | Unzip a vector of pairs into a pair of vectors
unzipV3 :: Vec n (a,b,c) -> (Vec n a, Vec n b, Vec n c)
unzipV3 ZVec = (ZVec,ZVec,ZVec)
unzipV3 ((a,b,c) :< ps) = (a :< as, b :< bs, c :< cs) 
  where (as,bs,cs) = unzipV3 ps

-- | Cross-product of two vectors, in the set-theory sense, not the geometric
-- sense. You can 'flattenV' the resulting vector of vectors.
cross :: Vec m a -> Vec n b -> Vec m (Vec n (a,b))
cross as bs = (\ a -> (a,) <$> bs) <$> as

-- | Matrix transposition. Specialization of 'sequenceA'.
transpose :: IsNat n => Vec m (Vec n a) -> Vec n (Vec m a)
transpose = sequenceA

{--------------------------------------------------------------------
    Conversion to vectors
--------------------------------------------------------------------}

class ToVec c n a where
  toVec :: c -> Vec n a

instance ToVec (Vec n a) n a where toVec = id

instance IsNat n => ToVec [a] n a where
  toVec = toVecL nat
  {-# INLINE toVec #-}

toVecL :: Nat n -> [a] -> Vec n a
toVecL Zero [] = ZVec
toVecL (Succ m) (a:as) = a :< toVecL m as
toVecL _ _ = error "toVecL: length mismatch"
{-# INLINE toVecL #-}

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

result :: (b -> b') -> ((a -> b) -> (a -> b'))
result = (.)

{--------------------------------------------------------------------
    Numeric instances via the applicative-numbers package
--------------------------------------------------------------------}

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS IsNat n, 

#define APPLICATIVE Vec n
#include "ApplicativeNumeric-inc.hs"
