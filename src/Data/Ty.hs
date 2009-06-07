{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Ty
-- Copyright   :  (c) Conal Elliott 2009
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Typed typerefs
----------------------------------------------------------------------

module Data.Ty
  (Ty,tyEq,tyOf,ty)
  where


import Data.Typeable (Typeable,TypeRep,typeOf)
import Unsafe.Coerce (unsafeCoerce)

import Data.Proof.EQ ((:=:)(..))

data Ty a = Ty { unTy :: TypeRep }

instance Show (Ty a) where show = show . unTy

tyEq :: Ty a -> Ty b -> Maybe (a :=: b)
Ty a `tyEq` Ty b | a == b    = unsafeCoerce (Just Refl)
                 | otherwise = Nothing

ty :: forall a. Typeable a => Ty a
ty = tyOf (undefined :: a)

tyOf :: Typeable a => a -> Ty a
tyOf a = Ty (typeOf a)
