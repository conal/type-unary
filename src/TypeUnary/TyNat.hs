{-# LANGUAGE TypeFamilies, TypeOperators, EmptyDataDecls #-}
{-# LANGUAGE UndecidableInstances #-} -- for :*:
-- {-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  TypeUnary.TyNat
-- Copyright   :  (c) Conal Elliott 2009
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Type-level unary natural numbers
----------------------------------------------------------------------

module TypeUnary.TyNat
  (
    -- * Type-level natural numbers
    Z, S, (:+:), (:*:), (:-:)
  , N0,N1,N2,N3,N4,N5,N6,N7,N8,N9
  , N10,N11,N12,N13,N14,N15,N16,N17,N18,N19
  , N20,N21,N22,N23,N24,N25,N26,N27,N28,N29
  , N30,N31,N32,N33,N34,N35,N36,N37,N38,N39
  , N40,N41,N42,N43,N44,N45,N46,N47,N48,N49
  , N50,N51,N52,N53,N54,N55,N56,N57,N58,N59
  , N60,N61,N62,N63,N64,N65,N66,N67,N68,N69
  , N70,N71,N72,N73,N74,N75,N76,N77,N78,N79
  , N80,N81,N82,N83,N84,N85,N86,N87,N88,N89
  , N90,N91,N92,N93,N94,N95,N96,N97,N98,N99
  ) where

-- import Data.Typeable (Typeable)

-- | Type-level representation of zero
data Z    -- deriving Typeable
-- | Type-level representation of successor
data S n  -- deriving Typeable

-- INSTANCE_TYPEABLE0(Z,zTC ,"Z")
-- INSTANCE_TYPEABLE1(S,sTC ,"S")

infixl 6 :+:

-- | Sum of type-level numbers
type family a :+: b

type instance Z   :+: b = b
type instance S a :+: b = S (a :+: b)

infixl 7 :*:

-- | Product of type-level numbers
type family a :*: b

type instance Z   :*: b = Z
type instance S a :*: b = b :+: (a :*: b)

infixl 6 :-:

-- Experiment:
type family a :-: b

type instance   n :-:   Z = n
type instance S n :-: S m = n :-: m

-- Generated code
-- 
--   putStrLn $ unlines ["type N" ++ show (n+1) ++ " = S N" ++ show n | n <- [0..15]]

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
type N17 = S N16
type N18 = S N17
type N19 = S N18

type N20 = S N19
type N21 = S N20
type N22 = S N21
type N23 = S N22
type N24 = S N23
type N25 = S N24
type N26 = S N25
type N27 = S N26
type N28 = S N27
type N29 = S N28

type N30 = S N29
type N31 = S N30
type N32 = S N31
type N33 = S N32
type N34 = S N33
type N35 = S N34
type N36 = S N35
type N37 = S N36
type N38 = S N37
type N39 = S N38

type N40 = S N39
type N41 = S N40
type N42 = S N41
type N43 = S N42
type N44 = S N43
type N45 = S N44
type N46 = S N45
type N47 = S N46
type N48 = S N47
type N49 = S N48

type N50 = S N49
type N51 = S N50
type N52 = S N51
type N53 = S N52
type N54 = S N53
type N55 = S N54
type N56 = S N55
type N57 = S N56
type N58 = S N57
type N59 = S N58

type N60 = S N59
type N61 = S N60
type N62 = S N61
type N63 = S N62
type N64 = S N63
type N65 = S N64
type N66 = S N65
type N67 = S N66
type N68 = S N67
type N69 = S N68

type N70 = S N69
type N71 = S N70
type N72 = S N71
type N73 = S N72
type N74 = S N73
type N75 = S N74
type N76 = S N75
type N77 = S N76
type N78 = S N77
type N79 = S N78

type N80 = S N79
type N81 = S N80
type N82 = S N81
type N83 = S N82
type N84 = S N83
type N85 = S N84
type N86 = S N85
type N87 = S N86
type N88 = S N87
type N89 = S N88

type N90 = S N89
type N91 = S N90
type N92 = S N91
type N93 = S N92
type N94 = S N93
type N95 = S N94
type N96 = S N95
type N97 = S N96
type N98 = S N97
type N99 = S N98

