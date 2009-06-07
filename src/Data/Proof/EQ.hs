{-# LANGUAGE GADTs, KindSignatures, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Proof.EQ
-- Copyright   :  (c) Conal Elliott 2009
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Type equality proofs
----------------------------------------------------------------------

module Data.Proof.EQ
  ( (:=:)(..)
  , liftEq, liftEq2, liftEq3, liftEq4
  , commEq, transEq
  ) where

-- TODO: Maybe remove the Eq suffixes, since the module can be imported
-- qualified, plus unqualified import of '(:=:)(..)'.

-- | Type equality proof
data (:=:) :: * -> * -> * where Refl :: a :=: a

-- | Lift proof through a unary type constructor
liftEq :: a :=: a' -> f a :=: f a'
liftEq Refl = Refl

-- | Lift proof through a binary type constructor (including '(,)')
liftEq2 :: a :=: a' -> b :=: b' -> f a b :=: f a' b'
liftEq2 Refl Refl = Refl

-- | Lift proof through a ternary type constructor (including '(,,)')
liftEq3 :: a :=: a' -> b :=: b' -> c :=: c' -> f a b c :=: f a' b' c'
liftEq3 Refl Refl Refl = Refl

-- | Lift proof through a quaternary type constructor (including '(,,,)')
liftEq4 :: a :=: a' -> b :=: b' -> c :=: c' -> d :=: d'
        -> f a b c d :=: f a' b' c' d'
liftEq4 Refl Refl Refl Refl = Refl

-- | Commutativity
commEq :: a :=: a' -> a' :=: a
commEq Refl = Refl

-- | Transitivity
transEq :: a :=: a' -> a' :=: a'' -> a :=: a''
transEq Refl Refl = Refl
